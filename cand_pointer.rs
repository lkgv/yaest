// SPDX-License-Identifier: Apache-2.0

//! 指针分析模块，实现了上下文敏感的指针分析（k-CFA Anderson算法）
//! 该模块分析Solang的CFG，构建指向关系，支持上下文敏感的查询

use crate::codegen::{
    cfg::{ControlFlowGraph, Instr, InternalCallTy, BasicBlock},
    vartable::Vartable,
    Expression, Builtin,
};
use crate::sema::ast::{Type, Namespace, ExternalCallAccounts};
use solang_parser::pt;
use std::collections::{HashMap, HashSet, BTreeMap, VecDeque};
use std::rc::Rc;
use std::fmt;
use std::sync::Arc;
use indexmap::IndexMap;
use num_bigint::BigInt;

/// 指针分析的结果
#[derive(Default, Debug)]
pub struct PointerAnalysisResult {
    /// 指针指向关系：(变量ID, 上下文) -> 可能指向的对象集合
    points_to_map: HashMap<(usize, Context), HashSet<AbstractObject>>,
    
    /// 指针别名关系：(变量ID, 上下文) -> 可能的别名变量
    alias_map: HashMap<(usize, Context), HashSet<(usize, Context)>>,
}

/// 表示分析上下文的类型
/// 对于2-objpointer分析，我们使用两个对象ID作为上下文
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Context {
    /// 上下文对象，最多保留K个（这里K=2）
    objects: Vec<ObjectId>,
}

/// 表示抽象对象的唯一标识符
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ObjectId(pub usize);

/// 表示抽象对象的类型
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AbstractObject {
    /// 分配的内存对象
    Allocation {
        id: ObjectId,
        ty: Type,
        size: Option<BigInt>,
    },
    /// 全局变量对象
    Global {
        id: ObjectId,
        var_no: usize,
        contract_no: Option<usize>,
    },
    /// 函数对象
    Function {
        id: ObjectId,
        function_no: usize,
    },
    /// 存储槽对象
    StorageSlot {
        id: ObjectId,
        slot: BigInt,
    },
    /// 未知/未定义对象
    Unknown {
        id: ObjectId,
    },
}

/// 指针分析器
pub struct PointerAnalyzer<'a> {
    /// 命名空间
    ns: &'a Namespace,
    
    /// 当前分析的CFG
    cfg: &'a ControlFlowGraph,
    
    /// 所有需要分析的CFG
    all_cfgs: &'a [ControlFlowGraph],
    
    /// 当前上下文
    current_context: Context,
    
    /// 分析结果
    result: PointerAnalysisResult,
    
    /// 待处理的约束
    worklist: VecDeque<PointerConstraint>,
    
    /// 下一个可用的对象ID
    next_object_id: usize,
    
    /// 已经分析过的函数和上下文对
    analyzed_functions: HashSet<(usize, Context)>,
}

/// 指针分析约束
#[derive(Clone, PartialEq, Eq, Debug)]
enum PointerConstraint {
    /// 指针赋值：ptr = &var
    AddressOf {
        ptr: (usize, Context),
        var: AbstractObject,
    },
    /// 指针复制：dst = src
    Copy {
        dst: (usize, Context),
        src: (usize, Context),
    },
    /// 指针存储：*ptr = val
    Store {
        ptr: (usize, Context),
        val: (usize, Context),
    },
    /// 指针加载：dst = *ptr
    Load {
        dst: (usize, Context),
        ptr: (usize, Context),
    },
    /// 函数调用
    Call {
        caller_context: Context,
        callee_context: Context,
        args: Vec<(usize, Context)>,
        params: Vec<usize>,
        returns: Vec<(usize, Context)>,
        ret_vals: Vec<usize>,
    },
}

/// 指针分析错误
#[derive(Debug)]
pub enum PointerAnalysisError {
    UnsupportedExpression(String),
    UnsupportedInstruction(String),
    InvalidType(String),
    Other(String),
}

impl fmt::Display for PointerAnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PointerAnalysisError::UnsupportedExpression(msg) => write!(f, "不支持的表达式：{}", msg),
            PointerAnalysisError::UnsupportedInstruction(msg) => write!(f, "不支持的指令：{}", msg),
            PointerAnalysisError::InvalidType(msg) => write!(f, "类型错误：{}", msg),
            PointerAnalysisError::Other(msg) => write!(f, "其他错误：{}", msg),
        }
    }
}

type Result<T> = std::result::Result<T, PointerAnalysisError>;

impl Context {
    /// 创建一个新的上下文
    pub fn new() -> Self {
        Context { objects: Vec::new() }
    }
    
    /// 从对象创建上下文
    pub fn from_objects(objects: Vec<ObjectId>) -> Self {
        Context { objects }
    }
    
    /// 添加一个对象到上下文中
    /// 对于k-CFA，我们只保留最近的k个对象
    pub fn push(&mut self, obj: ObjectId) {
        const K: usize = 2; // 2-obj指针分析
        
        self.objects.push(obj);
        if self.objects.len() > K {
            self.objects.remove(0);
        }
    }
    
    /// 获取上下文中的对象
    pub fn objects(&self) -> &[ObjectId] {
        &self.objects
    }
}

impl AbstractObject {
    /// 获取对象的ID
    pub fn id(&self) -> ObjectId {
        match self {
            AbstractObject::Allocation { id, .. } => *id,
            AbstractObject::Global { id, .. } => *id,
            AbstractObject::Function { id, .. } => *id,
            AbstractObject::StorageSlot { id, .. } => *id,
            AbstractObject::Unknown { id } => *id,
        }
    }
    
    /// 获取对象的类型
    pub fn get_type(&self) -> Option<&Type> {
        match self {
            AbstractObject::Allocation { ty, .. } => Some(ty),
            _ => None,
        }
    }
    
    /// 检查对象是否为函数
    pub fn is_function(&self) -> bool {
        matches!(self, AbstractObject::Function { .. })
    }
    
    /// 检查对象是否为存储
    pub fn is_storage(&self) -> bool {
        matches!(self, AbstractObject::StorageSlot { .. })
    }
    
    /// 检查对象是否为全局变量
    pub fn is_global(&self) -> bool {
        matches!(self, AbstractObject::Global { .. })
    }
}

impl PointerAnalysisResult {
    /// 创建一个新的分析结果
    pub fn new() -> Self {
        PointerAnalysisResult {
            points_to_map: HashMap::new(),
            alias_map: HashMap::new(),
        }
    }
    
    /// 添加指针指向关系
    pub fn add_points_to(&mut self, var: usize, context: &Context, obj: AbstractObject) -> bool {
        let entry = self.points_to_map.entry((var, context.clone())).or_insert_with(HashSet::new);
        entry.insert(obj)
    }
    
    /// 添加指针别名关系
    pub fn add_alias(&mut self, var1: usize, ctx1: &Context, var2: usize, ctx2: &Context) -> bool {
        let entry = self.alias_map.entry((var1, ctx1.clone())).or_insert_with(HashSet::new);
        entry.insert((var2, ctx2.clone()))
    }
    
    /// 获取变量可能指向的所有对象
    pub fn get_points_to(&self, var: usize, context: &Context) -> HashSet<AbstractObject> {
        self.points_to_map
            .get(&(var, context.clone()))
            .cloned()
            .unwrap_or_default()
    }
    
    /// 获取变量的所有可能别名
    pub fn get_aliases(&self, var: usize, context: &Context) -> HashSet<(usize, Context)> {
        self.alias_map
            .get(&(var, context.clone()))
            .cloned()
            .unwrap_or_default()
    }
    
    /// 检查两个变量是否可能是别名
    pub fn may_alias(&self, var1: usize, ctx1: &Context, var2: usize, ctx2: &Context) -> bool {
        // 检查两个变量指向的对象集合是否有交集
        let pts1 = self.get_points_to(var1, ctx1);
        let pts2 = self.get_points_to(var2, ctx2);
        
        !pts1.is_empty() && !pts2.is_empty() && pts1.iter().any(|obj| pts2.contains(obj))
    }
}

impl<'a> PointerAnalyzer<'a> {
    /// 创建一个新的指针分析器
    pub fn new(ns: &'a Namespace, cfg: &'a ControlFlowGraph, all_cfgs: &'a [ControlFlowGraph]) -> Self {
        PointerAnalyzer {
            ns,
            cfg,
            all_cfgs,
            current_context: Context::new(),
            result: PointerAnalysisResult::new(),
            worklist: VecDeque::new(),
            next_object_id: 0,
            analyzed_functions: HashSet::new(),
        }
    }
    
    /// 创建一个新的对象ID
    fn new_object_id(&mut self) -> ObjectId {
        let id = self.next_object_id;
        self.next_object_id += 1;
        ObjectId(id)
    }
    
    /// 分析指针关系，返回分析结果
    pub fn analyze(&mut self) -> Result<PointerAnalysisResult> {
        // 初始化工作列表
        self.initialize_constraints();
        
        // 不断处理约束直到工作列表为空
        while let Some(constraint) = self.worklist.pop_front() {
            self.process_constraint(constraint)?;
        }
        
        Ok(self.result.clone())
    }
    
    /// 初始化分析约束
    fn initialize_constraints(&mut self) {
        // 遍历CFG中的每个基本块和指令，生成初始约束
        for (block_idx, block) in self.cfg.blocks.iter().enumerate() {
            for instr in &block.instr {
                if let Some(constraints) = self.generate_constraints_from_instr(instr, block_idx) {
                    for constraint in constraints {
                        self.worklist.push_back(constraint);
                    }
                }
            }
        }
    }
    
    /// 从指令生成初始约束
    fn generate_constraints_from_instr(&mut self, instr: &Instr, block_idx: usize) -> Option<Vec<PointerConstraint>> {
        match instr {
            Instr::Set { res, expr, .. } => {
                // 从表达式生成约束
                let constraints = self.generate_constraints_from_expr(*res, expr, block_idx);
                if let Ok(cs) = constraints {
                    Some(cs)
                } else {
                    // 忽略不支持的表达式
                    None
                }
            }
            Instr::Store { dest, data, .. } => {
                // 处理存储指令
                let mut constraints = Vec::new();
                
                // 分析目标表达式
                if let Ok((ptr_var, ptr_ctx)) = self.analyze_expr_to_var(dest, block_idx) {
                    // 分析源表达式
                    if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(data, block_idx) {
                        constraints.push(PointerConstraint::Store {
                            ptr: (ptr_var, ptr_ctx),
                            val: (val_var, val_ctx),
                        });
                    }
                }
                
                Some(constraints)
            }
            Instr::Call { res, call, args, .. } => {
                // 处理函数调用
                let mut constraints = Vec::new();
                
                match call {
                    InternalCallTy::Static { cfg_no } => {
                        // 处理静态函数调用
                        if let Some(callee_cfg) = self.all_cfgs.get(*cfg_no) {
                            // 创建调用上下文
                            let callee_obj_id = self.new_object_id();
                            let mut callee_context = self.current_context.clone();
                            callee_context.push(callee_obj_id);
                            
                            // 创建函数参数和返回值的约束
                            let mut arg_vars = Vec::new();
                            let mut param_vars = Vec::new();
                            
                            // 处理参数
                            for (i, arg) in args.iter().enumerate() {
                                if let Ok((arg_var, arg_ctx)) = self.analyze_expr_to_var(arg, block_idx) {
                                    arg_vars.push((arg_var, arg_ctx));
                                    
                                    // 如果参数i存在于被调用的函数中
                                    if i < callee_cfg.params.len() {
                                        // 假设参数位置匹配
                                        param_vars.push(i);
                                    }
                                }
                            }
                            
                            // 处理返回值
                            let ret_vars = res.clone();
                            let mut return_vars = Vec::new();
                            
                            for ret_var in &ret_vars {
                                return_vars.push((*ret_var, self.current_context.clone()));
                            }
                            
                            // 创建调用约束
                            constraints.push(PointerConstraint::Call {
                                caller_context: self.current_context.clone(),
                                callee_context,
                                args: arg_vars,
                                params: param_vars,
                                returns: return_vars,
                                ret_vals: ret_vars,
                            });
                        }
                    }
                    // 暂时不处理动态调用和内置函数
                    _ => {}
                }
                
                Some(constraints)
            }
            Instr::LoadStorage { res, storage, .. } => {
                // 处理存储加载
                let mut constraints = Vec::new();
                
                // 创建存储对象
                if let Ok(storage_obj) = self.create_storage_object_from_expr(storage) {
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (*res, self.current_context.clone()),
                        var: storage_obj,
                    });
                }
                
                Some(constraints)
            }
            Instr::MemCopy { source, destination, bytes, .. } => {
                // 处理内存复制
                let mut constraints = Vec::new();
                
                if let Ok((src_var, src_ctx)) = self.analyze_expr_to_var(source, block_idx) {
                    if let Ok((dest_var, dest_ctx)) = self.analyze_expr_to_var(destination, block_idx) {
                        // 将源指针的所有指向关系复制到目标指针
                        constraints.push(PointerConstraint::Copy {
                            dst: (dest_var, dest_ctx),
                            src: (src_var, src_ctx),
                        });
                    }
                }
                
                Some(constraints)
            }
            // 其他指令暂时不处理
            _ => None,
        }
    }
    
    /// 处理约束
    fn process_constraint(&mut self, constraint: PointerConstraint) -> Result<()> {
        match constraint {
            PointerConstraint::AddressOf { ptr, var } => {
                // 处理地址获取约束: ptr = &var
                let (ptr_var, ptr_ctx) = ptr;
                if self.result.add_points_to(ptr_var, &ptr_ctx, var.clone()) {
                    // 更新了指向关系，需要更新工作列表
                    self.update_worklist_after_points_to_change(ptr_var, &ptr_ctx);
                }
            }
            PointerConstraint::Copy { dst, src } => {
                // 处理指针复制约束: dst = src
                let (dst_var, dst_ctx) = dst;
                let (src_var, src_ctx) = src;
                
                // 获取源变量指向的所有对象
                let src_objs = self.result.get_points_to(src_var, &src_ctx);
                
                // 将所有对象添加到目标变量的指向集合
                let mut updated = false;
                for obj in src_objs {
                    if self.result.add_points_to(dst_var, &dst_ctx, obj) {
                        updated = true;
                    }
                }
                
                if updated {
                    // 更新了指向关系，需要更新工作列表
                    self.update_worklist_after_points_to_change(dst_var, &dst_ctx);
                }
            }
            PointerConstraint::Store { ptr, val } => {
                // 处理指针存储约束: *ptr = val
                let (ptr_var, ptr_ctx) = ptr;
                let (val_var, val_ctx) = val;
                
                // 获取指针指向的所有对象
                let ptr_objs = self.result.get_points_to(ptr_var, &ptr_ctx);
                
                // 对于每个对象，创建从val到该对象的约束
                for obj in ptr_objs {
                    // 获取对象ID
                    let obj_id = obj.id();
                    
                    // 为每个"存储位置"创建一个特殊的隐式变量
                    let implicit_var = obj_id.0; // 使用对象ID作为隐式变量
                    
                    // 创建一个从val到隐式变量的复制约束
                    self.worklist.push_back(PointerConstraint::Copy {
                        dst: (implicit_var, Context::new()),
                        src: val,
                    });
                }
            }
            PointerConstraint::Load { dst, ptr } => {
                // 处理指针加载约束: dst = *ptr
                let (dst_var, dst_ctx) = dst;
                let (ptr_var, ptr_ctx) = ptr;
                
                // 获取指针指向的所有对象
                let ptr_objs = self.result.get_points_to(ptr_var, &ptr_ctx);
                
                // 对于每个对象，创建从该对象到dst的约束
                for obj in ptr_objs {
                    // 获取对象ID
                    let obj_id = obj.id();
                    
                    // 为每个"存储位置"创建一个特殊的隐式变量
                    let implicit_var = obj_id.0; // 使用对象ID作为隐式变量
                    
                    // 创建一个从隐式变量到dst的复制约束
                    self.worklist.push_back(PointerConstraint::Copy {
                        dst,
                        src: (implicit_var, Context::new()),
                    });
                }
            }
            PointerConstraint::Call { caller_context, callee_context, args, params, returns, ret_vals } => {
                // 处理函数调用约束
                // 1. 参数传递: 实参 -> 形参
                for (i, (arg_var, arg_ctx)) in args.iter().enumerate() {
                    if i < params.len() {
                        let param_var = params[i];
                        
                        // 创建从实参到形参的复制约束
                        self.worklist.push_back(PointerConstraint::Copy {
                            dst: (param_var, callee_context.clone()),
                            src: (*arg_var, arg_ctx.clone()),
                        });
                    }
                }
                
                // 2. 返回值传递: 函数返回值 -> 调用点接收值
                for (i, (ret_var, ret_ctx)) in returns.iter().enumerate() {
                    if i < ret_vals.len() {
                        let ret_val = ret_vals[i];
                        
                        // 创建从函数返回值到调用点接收值的复制约束
                        self.worklist.push_back(PointerConstraint::Copy {
                            dst: (*ret_var, ret_ctx.clone()),
                            src: (ret_val, callee_context.clone()),
                        });
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// 在指向关系更新后更新工作列表
    fn update_worklist_after_points_to_change(&mut self, var: usize, context: &Context) {
        // 查找所有以该变量为源或目标的约束，重新添加到工作列表
        // 这里的实现较为简化，实际上需要更高效的索引结构
        
        // 例如，查找所有Load约束，其中ptr是更新的变量
        let load_constraints = self.find_load_constraints_for_ptr(var, context);
        for constraint in load_constraints {
            self.worklist.push_back(constraint);
        }
        
        // 查找所有Store约束，其中ptr是更新的变量
        let store_constraints = self.find_store_constraints_for_ptr(var, context);
        for constraint in store_constraints {
            self.worklist.push_back(constraint);
        }
    }
    
    /// 查找所有以指定变量为指针的Load约束
    fn find_load_constraints_for_ptr(&self, var: usize, context: &Context) -> Vec<PointerConstraint> {
        // 实际实现中，应当维护一个索引结构来高效查找
        // 这里返回空列表作为占位符
        Vec::new()
    }
    
    /// 查找所有以指定变量为指针的Store约束
    fn find_store_constraints_for_ptr(&self, var: usize, context: &Context) -> Vec<PointerConstraint> {
        // 实际实现中，应当维护一个索引结构来高效查找
        // 这里返回空列表作为占位符
        Vec::new()
    }
    
    /// 从表达式生成约束
    fn generate_constraints_from_expr(&mut self, res: usize, expr: &Expression, block_idx: usize) -> Result<Vec<PointerConstraint>> {
        let mut constraints = Vec::new();
        
        match expr {
            Expression::Variable { var_no, .. } => {
                // 变量赋值：res = var_no
                constraints.push(PointerConstraint::Copy {
                    dst: (res, self.current_context.clone()),
                    src: (*var_no, self.current_context.clone()),
                });
            }
            Expression::Load { expr: inner_expr, .. } => {
                // 内存加载：res = *expr
                if let Ok((ptr_var, ptr_ctx)) = self.analyze_expr_to_var(inner_expr, block_idx) {
                    constraints.push(PointerConstraint::Load {
                        dst: (res, self.current_context.clone()),
                        ptr: (ptr_var, ptr_ctx),
                    });
                }
            }
            Expression::GetRef { expr: inner_expr, .. } => {
                // 获取引用：res = &expr
                if let Ok(obj) = self.create_object_from_expr(inner_expr) {
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (res, self.current_context.clone()),
                        var: obj,
                    });
                }
            }
            Expression::AdvancePointer { pointer, bytes_offset, .. } => {
                // 指针偏移：res = pointer + offset
                if let Ok((ptr_var, ptr_ctx)) = self.analyze_expr_to_var(pointer, block_idx) {
                    // 将原指针指向的所有对象复制给结果变量
                    constraints.push(PointerConstraint::Copy {
                        dst: (res, self.current_context.clone()),
                        src: (ptr_var, ptr_ctx),
                    });
                }
            }
            Expression::Builtin { kind, args, .. } => {
                // 处理内置函数
                match kind {
                    Builtin::GetAddress => {
                        // GetAddress返回指针
                        if let Some(obj) = self.create_address_object() {
                            constraints.push(PointerConstraint::AddressOf {
                                ptr: (res, self.current_context.clone()),
                                var: obj,
                            });
                        }
                    }
                    Builtin::ReadFromBuffer => {
                        // 从缓冲区读取，参数0是缓冲区指针
                        if args.len() > 0 {
                            if let Ok((buf_var, buf_ctx)) = self.analyze_expr_to_var(&args[0], block_idx) {
                                constraints.push(PointerConstraint::Load {
                                    dst: (res, self.current_context.clone()),
                                    ptr: (buf_var, buf_ctx),
                                });
                            }
                        }
                    }
                    Builtin::WriteBytes | Builtin::WriteAddress | 
                    Builtin::WriteInt8 | Builtin::WriteInt16LE | 
                    Builtin::WriteInt32LE | Builtin::WriteInt64LE | 
                    Builtin::WriteInt128LE | Builtin::WriteInt256LE |
                    Builtin::WriteUint16LE | Builtin::WriteUint32LE |
                    Builtin::WriteUint64LE | Builtin::WriteUint128LE |
                    Builtin::WriteUint256LE => {
                        // 写入缓冲区，参数0是目标指针，参数1是偏移，参数2是要写入的值
                        if args.len() >= 3 {
                            if let Ok((dest_var, dest_ctx)) = self.analyze_expr_to_var(&args[0], block_idx) {
                                if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(&args[2], block_idx) {
                                    constraints.push(PointerConstraint::Store {
                                        ptr: (dest_var, dest_ctx),
                                        val: (val_var, val_ctx),
                                    });
                                }
                            }
                        }
                    }
                    // 其他内置函数暂不处理
                    _ => {}
                }
            }
            Expression::InternalFunctionCfg { cfg_no, .. } => {
                // 创建函数对象
                let func_obj = AbstractObject::Function {
                    id: self.new_object_id(),
                    function_no: *cfg_no,
                };
                
                constraints.push(PointerConstraint::AddressOf {
                    ptr: (res, self.current_context.clone()),
                    var: func_obj,
                });
            }
            Expression::AllocDynamicBytes { ty, size, .. } => {
                // 动态内存分配
                let alloc_obj = AbstractObject::Allocation {
                    id: self.new_object_id(),
                    ty: ty.clone(),
                    size: None, // 动态大小，暂不确定
                };
                
                constraints.push(PointerConstraint::AddressOf {
                    ptr: (res, self.current_context.clone()),
                    var: alloc_obj,
                });
            }
            // 其他表达式类型暂不处理
            _ => {}
        }
        
        Ok(constraints)
    }
    
    /// 分析表达式并返回对应的变量和上下文
    fn analyze_expr_to_var(&mut self, expr: &Expression, block_idx: usize) -> Result<(usize, Context)> {
        match expr {
            Expression::Variable { var_no, .. } => {
                // 直接变量引用
                Ok((*var_no, self.current_context.clone()))
            }
            _ => {
                // 为复杂表达式创建临时变量
                let temp_var = self.next_object_id;
                self.next_object_id += 1;
                
                // 为临时变量生成约束
                if let Ok(constraints) = self.generate_constraints_from_expr(temp_var, expr, block_idx) {
                    for constraint in constraints {
                        self.worklist.push_back(constraint);
                    }
                }
                
                Ok((temp_var, self.current_context.clone()))
            }
        }
    }
    
    /// 从表达式创建抽象对象
    fn create_object_from_expr(&mut self, expr: &Expression) -> Result<AbstractObject> {
        match expr {
            Expression::Variable { var_no, ty, .. } => {
                Ok(AbstractObject::Allocation {
                    id: self.new_object_id(),
                    ty: ty.clone(),
                    size: None,
                })
            }
            Expression::StorageVariable { contract_no, var_no, .. } => {
                Ok(AbstractObject::Global {
                    id: self.new_object_id(),
                    var_no: *var_no,
                    contract_no: Some(*contract_no),
                })
            }
            // 其他表达式类型，创建未知对象
            _ => Ok(AbstractObject::Unknown {
                id: self.new_object_id(),
            }),
        }
    }
    
    /// 从存储表达式创建存储对象
    fn create_storage_object_from_expr(&mut self, expr: &Expression) -> Result<AbstractObject> {
        // 这里简化处理，实际上需要解析存储槽计算
        Ok(AbstractObject::StorageSlot {
            id: self.new_object_id(),
            slot: BigInt::from(0),
        })
    }
    
    /// 创建一个代表地址的对象
    fn create_address_object(&mut self) -> Option<AbstractObject> {
        Some(AbstractObject::Allocation {
            id: self.new_object_id(),
            ty: Type::Address(false),
            size: None,
        })
    }
}

/// 公共API函数：分析指定合约中的CFG
pub fn analyze_contract_pointers(
    contract_no: usize,
    ns: &Namespace,
) -> Result<HashMap<usize, PointerAnalysisResult>> {
    let mut results = HashMap::new();
    
    // 获取合约的所有CFG
    if let Some(contract) = ns.contracts.get(contract_no) {
        let all_cfgs = &contract.cfg;
        
        // 分析每个CFG
        for (cfg_idx, cfg) in all_cfgs.iter().enumerate() {
            if !cfg.is_placeholder() {
                let mut analyzer = PointerAnalyzer::new(ns, cfg, all_cfgs);
                let result = analyzer.analyze()?;
                results.insert(cfg_idx, result);
            }
        }
    }
    
    Ok(results)
}

/// 公共API函数：分析单个函数的指针关系
pub fn analyze_function_pointers(
    contract_no: usize,
    function_idx: usize,
    ns: &Namespace,
) -> Result<PointerAnalysisResult> {
    if let Some(contract) = ns.contracts.get(contract_no) {
        if let Some(cfg) = contract.cfg.get(function_idx) {
            if !cfg.is_placeholder() {
                let mut analyzer = PointerAnalyzer::new(ns, cfg, &contract.cfg);
                return analyzer.analyze();
            }
        }
    }
    
    Err(PointerAnalysisError::Other(format!(
        "函数 #{} 在合约 #{} 中不存在或是占位符",
        function_idx, contract_no
    )))
}

/// 公共API函数：检查两个变量是否可能是别名
pub fn may_alias(
    var1: usize,
    var2: usize,
    result: &PointerAnalysisResult,
) -> bool {
    let ctx = Context::new(); // 使用默认上下文
    result.may_alias(var1, &ctx, var2, &ctx)
}

/// 公共API函数：获取变量的所有可能指向对象
pub fn get_points_to_set(
    var: usize,
    result: &PointerAnalysisResult,
) -> HashSet<AbstractObject> {
    let ctx = Context::new(); // 使用默认上下文
    result.get_points_to(var, &ctx)
}

/// 公共API函数：在特定上下文中检查别名关系
pub fn may_alias_in_context(
    var1: usize,
    ctx1: &Context,
    var2: usize,
    ctx2: &Context,
    result: &PointerAnalysisResult,
) -> bool {
    result.may_alias(var1, ctx1, var2, ctx2)
}

/// 公共API函数：在特定上下文中获取指向集合
pub fn get_points_to_set_in_context(
    var: usize,
    ctx: &Context,
    result: &PointerAnalysisResult,
) -> HashSet<AbstractObject> {
    result.get_points_to(var, ctx)
}

/// 工具函数：将指针分析结果转换为人类可读的字符串
pub fn result_to_string(result: &PointerAnalysisResult, ns: &Namespace) -> String {
    let mut output = String::new();
    
    // 添加指向关系信息
    output.push_str("指向关系分析结果:\n");
    for ((var, ctx), objs) in &result.points_to_map {
        output.push_str(&format!("变量 #{} 在上下文 {:?} 中可能指向:\n", var, ctx));
        
        for obj in objs {
            output.push_str(&format!("  - {:?}\n", obj));
        }
    }
    
    // 添加别名关系信息
    output.push_str("\n别名关系分析结果:\n");
    for ((var1, ctx1), aliases) in &result.alias_map {
        output.push_str(&format!("变量 #{} 在上下文 {:?} 中的可能别名:\n", var1, ctx1));
        
        for (var2, ctx2) in aliases {
            output.push_str(&format!("  - 变量 #{} 在上下文 {:?}\n", var2, ctx2));
        }
    }
    
    output
}
