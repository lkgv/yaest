// SPDX-License-Identifier: Apache-2.0

//! 指针分析模块，实现了上下文敏感的指针分析（k-CFA Anderson算法）
//! 该模块分析Solang的CFG，构建指向关系，支持上下文敏感的查询
//! 
//! TODO 添加对更多的IR （codegen::Builtin, codegen::Expression, cfg::Instr )的处理.
//! TODO 修复指针分析潜在的bug.
//! TODO 添加函数，收集信息：1. state variables 及相关的读写指令 2. events 以及相关的emit指令.


use crate::codegen::{
    cfg::{ControlFlowGraph, Instr, InternalCallTy, BasicBlock},
    vartable::Vartable,
    Expression, Builtin,
};
use crate::sema::ast::{Type, Namespace, ExternalCallAccounts, RetrieveType};
use ink_env::call;
use solang_parser::pt;
use std::{collections::{BTreeMap, HashMap, HashSet, VecDeque}, ops::Deref};
use std::rc::Rc;
use std::fmt;
use std::sync::Arc;
use indexmap::IndexMap;
use num_bigint::BigInt;

/// 指针分析的结果
#[derive(Default, Debug, Clone)]
pub struct PointerAnalysisResult {
    /// 指针指向关系：(变量ID, 上下文) -> 可能指向的对象集合
    points_to_map: HashMap<(usize, Context), HashSet<AbstractObject>>,
    
    /// 指针别名关系：(变量ID, 上下文) -> 可能的别名变量
    alias_map: HashMap<(usize, Context), HashSet<(usize, Context)>>,
}

/// 表示分析上下文的类型
/// 对于2-objpointer分析，我们使用两个对象ID作为上下文
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord)]
pub struct Context {
    /// 上下文对象，最多保留K个（这里K=2）
    objects: Vec<ObjectId>,
}

/// 表示抽象对象的唯一标识符
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
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
    /// 结构体字段对象，用于支持字段敏感分析
    Field {
        id: ObjectId,
        base: Box<AbstractObject>,
        field: usize,
        ty: Type,
    },
    /// 数组元素对象，用于支持数组索引敏感分析
    ArrayElement {
        id: ObjectId,
        base: Box<AbstractObject>,
        index: Option<BigInt>, // None表示任意索引，用于过程间分析
        ty: Type,
    },
    /// 未知/未定义对象
    Unknown {
        id: ObjectId,
    },
}

/// 指针分析约束
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
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
    StaticCall {
        caller_context: Context,
        callee_context: Context,
        args: Vec<(usize, Context)>,
        params: Vec<usize>,
        returns: Vec<(usize, Context)>,
        ret_vals: Vec<usize>,
    },
    DynamicCall {
        caller: (usize, Context),
        args: Vec<Expression>,
        returns: Vec<(usize, Context)>,
        block_idx: usize
    }
}

#[derive(Clone, Debug)]
struct Constraints {
    constraints: Vec<PointerConstraint>,
    var_constraints: BTreeMap<(usize, Context), HashSet<PointerConstraint>>,
}

impl Constraints {
    pub fn new () -> Constraints {
        Constraints {
            constraints: Vec::<PointerConstraint>::new(),
            var_constraints: BTreeMap::<(usize, Context), HashSet<PointerConstraint>>::new()
        }
    }

    pub fn push(self: &mut Constraints, constraint: PointerConstraint) {
        self.constraints.push(constraint.clone());

        match constraint.clone() {
            PointerConstraint::AddressOf { ptr, .. } |
            PointerConstraint::Store { ptr, .. } |
            PointerConstraint::Load { ptr , .. } => {
                if let Some(constraint_set) = self.var_constraints.get_mut(&ptr) {
                    constraint_set.insert(constraint.clone());
                } else {
                    let mut cset = HashSet::new();
                    cset.insert(constraint.clone());
                    self.var_constraints.insert(ptr, cset);
                }
            },
            PointerConstraint::DynamicCall { caller, .. } => {
                if let Some(constraint_set) = self.var_constraints.get_mut(&caller) {
                    constraint_set.insert(constraint.clone());
                } else {
                    let mut cset = HashSet::new();
                    cset.insert(constraint.clone());
                    self.var_constraints.insert(caller, cset);
                }
            },
            _ => {}
        }
    }

    pub fn get(self: &Constraints, var: (usize, Context)) -> Option<&HashSet<PointerConstraint>> {
        self.var_constraints.get(&var)
    }
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

    /// 当前函数编号
    current_function_no: usize,

    /// 调用栈
    call_stack: Vec<(usize, Context)>,

    /// 调用图
    call_graph: CallGraph,

    var_constraints: Constraints
}

/// 指针分析结果与调用图
#[derive(Clone, Debug)]
pub struct PointerAnalysisComplete {
    /// 指针分析结果
    pub result: PointerAnalysisResult,
    /// 调用图
    pub call_graph: CallGraph,
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
            AbstractObject::Field { id, .. } => *id,
            AbstractObject::ArrayElement { id, .. } => *id,
            AbstractObject::Unknown { id } => *id,
        }
    }
    
    /// 获取对象的类型
    pub fn get_type(&self) -> Option<&Type> {
        match self {
            AbstractObject::Allocation { ty, .. } => Some(ty),
            AbstractObject::Field { ty, .. } => Some(ty),
            AbstractObject::ArrayElement { ty, .. } => Some(ty),
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

trait CFGExtension {
    fn local_num(self: &Self) -> usize;
    fn param_num(self: &Self) -> usize;
    fn return_num(self: &Self) -> usize;
    fn get_ret_no(self: &Self, idx: usize) -> usize;
    fn get_param_no(self: &Self, idx: usize) -> usize;
}

/// 为函数的返回变量和参数生成编号与局部变量一致的index
impl CFGExtension for ControlFlowGraph {
    fn local_num(self: &Self) -> usize {
        return self.vars.len();
    }

    fn param_num(self: &Self) -> usize {
        return self.params.len();
    }

    fn return_num(self: &Self) -> usize {
        return self.returns.len();
    }

    fn get_ret_no(self: &Self, idx: usize) -> usize {
        return self.local_num() + self.param_num() + idx;
    }

    fn get_param_no(self: &Self, idx: usize) -> usize {
        return self.local_num() + idx;
    }
}

impl<'a> PointerAnalyzer<'a> {
    /// 创建一个新的指针分析器
    pub fn new(ns: &'a Namespace, cfg: &'a ControlFlowGraph, all_cfgs: &'a [ControlFlowGraph], function_no: usize) -> Self {
        PointerAnalyzer {
            ns,
            cfg,
            all_cfgs,
            current_context: Context::new(),
            result: PointerAnalysisResult::new(),
            worklist: VecDeque::new(),
            next_object_id: 0,
            analyzed_functions: HashSet::new(),
            call_stack: Vec::new(),
            call_graph: CallGraph::new(),
            current_function_no: function_no,
            var_constraints: Constraints::new()
        }
    }
    
    /// 创建一个新的对象ID
    fn new_object_id(&mut self) -> ObjectId {
        let id = self.next_object_id;
        self.next_object_id += 1;
        ObjectId(id)
    }
    
    /// 分析指针关系，返回分析结果和调用图
    pub fn analyze(&mut self) -> Result<(PointerAnalysisResult, CallGraph)> {
        // 将当前函数添加到调用栈
        self.call_stack.push((self.current_function_no, self.current_context.clone()));
        
        // 初始化工作列表
        self.initialize_constraints();
        
        // 不断处理约束直到工作列表为空
        while let Some(constraint) = self.worklist.pop_front() {
            self.process_constraint(constraint)?;
        }
        
        // 移除调用栈中的当前函数
        self.call_stack.pop();
        
        Ok((self.result.clone(), self.call_graph.clone()))
    }
    
    /// 初始化分析约束
    fn initialize_constraints(&mut self) {
        // 遍历CFG中的每个基本块和指令，生成初始约束
        for (block_idx, block) in self.cfg.blocks.iter().enumerate() {
            for instr in &block.instr {
                if let Some(constraints) = self.generate_constraints_from_instr(instr, block_idx) {
                    for constraint in constraints {
                        self.worklist.push_back(constraint.clone());
                        self.var_constraints.push(constraint);
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
            Instr::Return { value } => {
                let mut constraints = Vec::new();

                for (i, val) in value.iter().enumerate() {
                    if let Ok((ret_val, ret_ctx)) = self.analyze_expr_to_var(val, block_idx) {
                        if i < self.cfg.return_num() {
                            let ret_no = self.cfg.get_ret_no(i);
                            constraints.push(PointerConstraint::Copy {
                                dst: (ret_no, self.current_context.clone()),
                                src: (ret_val, ret_ctx)
                            })
                        }
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
                            // 处理继承和虚函数解析
                            let actual_cfg_no = if let Some(function) = self.ns.functions.get(*cfg_no) {
                                if function.is_virtual {
                                    self.resolve_virtual_function(*cfg_no)
                                } else {
                                    *cfg_no
                                }
                            } else {
                                *cfg_no
                            };
                            
                            // 创建调用上下文
                            let callee_obj_id = self.new_object_id();
                            let mut callee_context = self.current_context.clone();
                            callee_context.push(callee_obj_id);
                            
                            // 添加到调用图
                            self.call_graph.add_edge(
                                (self.current_function_no, self.current_context.clone()),
                                (actual_cfg_no, callee_context.clone()),
                                Some(block_idx)
                            );

                            // 创建函数参数和返回值的约束
                            let mut arg_vars = Vec::new();
                            let mut param_vars = Vec::new();
                            
                            // 处理参数
                            for (i, arg) in args.iter().enumerate() {
                                if let Ok((arg_var, arg_ctx)) = self.analyze_expr_to_var(arg, block_idx) {
                                    arg_vars.push((arg_var, arg_ctx));
                                    
                                    // 如果参数i存在于被调用的函数中
                                    if i < callee_cfg.params.len() {
                                        param_vars.push(callee_cfg.get_param_no(i));
                                    }
                                }
                            }
                            
                            // 处理返回值
                            let mut return_vars = Vec::new();
                            let mut ret_vals = Vec::new();
                            
                            for (i, ret_var) in res.iter().enumerate() {
                                return_vars.push((*ret_var, self.current_context.clone()));
                                ret_vals.push(callee_cfg.get_ret_no(i));
                            }
                            
                            // 检查递归调用
                            if self.call_stack.contains(&(actual_cfg_no, callee_context.clone())) {
                                // 发现递归，添加特殊处理
                                return self.handle_recursive_call(actual_cfg_no, callee_context, return_vars);
                            }
                            
                            // 防止重复分析
                            if !self.analyzed_functions.contains(&(actual_cfg_no, callee_context.clone())) {
                                // 标记函数在该上下文中已经被分析
                                self.analyzed_functions.insert((actual_cfg_no, callee_context.clone()));
                                
                                // 递归分析被调用函数
                                if let Some(()) = self.analyze_callee_function(actual_cfg_no, callee_context.clone(), args, res, block_idx) {
                                    // 递归分析成功
                                }
                            }
                            
                            // 创建调用约束
                            constraints.push(PointerConstraint::StaticCall {
                                caller_context: self.current_context.clone(),
                                callee_context,
                                args: arg_vars,
                                params: param_vars,
                                returns: return_vars,
                                ret_vals: ret_vals
                            });
                        }
                    }
                    InternalCallTy::Dynamic ( function_expr ) => {
                        // 处理动态函数调用（通过函数指针）
                        if let Ok((func_var, func_ctx)) = self.analyze_expr_to_var(function_expr, block_idx) {

                            // 创建函数参数和返回值的约束
                            let mut arg_vars = Vec::new();
                            
                            // 处理参数
                            for (i, arg) in args.iter().enumerate() {
                                if let Ok((arg_var, arg_ctx)) = self.analyze_expr_to_var(arg, block_idx) {
                                    arg_vars.push((i, (arg_var, arg_ctx)));
                                }
                            }
                            
                            // 处理返回值
                            let ret_vars = res.clone();
                            let mut return_vars = Vec::new();
                            
                            for ret_var in &ret_vars {
                                return_vars.push((*ret_var, self.current_context.clone()));
                            }

                            constraints.push(PointerConstraint::DynamicCall {
                                caller: (func_var, func_ctx),
                                args: args.clone(),
                                returns: return_vars,
                                block_idx: block_idx,
                            });
                        }
                    }
                    // 处理外部调用和内置函数
                    _ => {
                        // 对于无法精确分析的调用，可以添加一些保守的约束
                        // 例如，假设返回值可能指向任何对象
                        for ret_var in res {
                            let unknown_obj = AbstractObject::Unknown {
                                id: self.new_object_id(),
                            };
                            
                            constraints.push(PointerConstraint::AddressOf {
                                ptr: (*ret_var, self.current_context.clone()),
                                var: unknown_obj,
                            });
                        }
                    }
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
            Instr::SetStorage { storage, value, .. } => {
                // 处理存储设置指令
                let mut constraints = Vec::new();
                
                // 创建存储对象
                if let Ok(storage_obj) = self.create_storage_object_from_expr(storage) {
                    // 获取存储对象ID作为特殊变量
                    let storage_var = storage_obj.id().0;
                    
                    // 为存储对象创建一个指向关系
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (storage_var, Context::new()),
                        var: storage_obj,
                    });
                    
                    // 创建值到存储的指向关系
                    if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(value, block_idx) {
                        constraints.push(PointerConstraint::Store {
                            ptr: (storage_var, Context::new()),
                            val: (val_var, val_ctx),
                        });
                    }
                }
                
                Some(constraints)
            }
            Instr::ClearStorage { storage, .. } => {
                // 处理存储清除指令
                // 此处无需添加特别的约束，因为清除只会影响值而不是指向关系
                Some(Vec::new())
            }
            Instr::SetStorageBytes { storage, value, offset } => {
                // 处理存储字节设置指令
                let mut constraints = Vec::new();
                
                // 创建存储对象
                if let Ok(storage_obj) = self.create_storage_object_from_expr(storage) {
                    // 获取存储对象ID作为特殊变量
                    let storage_var = storage_obj.id().0;
                    
                    // 为存储对象创建一个指向关系
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (storage_var, Context::new()),
                        var: storage_obj,
                    });
                    
                    // 创建值到存储的指向关系
                    if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(value, block_idx) {
                        constraints.push(PointerConstraint::Store {
                            ptr: (storage_var, Context::new()),
                            val: (val_var, val_ctx),
                        });
                    }
                }
                
                Some(constraints)
            }
            Instr::PushStorage { res, storage, value: Some(value), .. } => {
                // 处理存储数组Push指令
                let mut constraints = Vec::new();
                
                // 创建存储对象
                if let Ok(storage_obj) = self.create_storage_object_from_expr(storage) {
                    // 创建数组元素对象，表示新添加的元素
                    let element_obj = AbstractObject::ArrayElement {
                        id: self.new_object_id(),
                        base: Box::new(storage_obj),
                        index: None, // 未知索引（动态增长的数组）
                        ty: value.ty().clone(),
                    };
                    
                    // 为数组元素创建一个指向关系
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (*res, self.current_context.clone()),
                        var: element_obj.clone(),
                    });
                    
                    // 创建值到数组元素的约束
                    if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(value, block_idx) {
                        let element_var = element_obj.id().0;
                        
                        constraints.push(PointerConstraint::AddressOf {
                            ptr: (element_var, Context::new()),
                            var: element_obj,
                        });
                        
                        constraints.push(PointerConstraint::Store {
                            ptr: (element_var, Context::new()),
                            val: (val_var, val_ctx),
                        });
                    }
                }
                
                Some(constraints)
            }
            Instr::PopStorage { res: Some(res), storage, .. } => {
                // 处理存储数组Pop指令
                let mut constraints = Vec::new();
                let ref var = self.cfg.vars[res];
                
                // 创建存储对象
                if let Ok(storage_obj) = self.create_storage_object_from_expr(storage) {
                    // 创建数组元素对象，表示弹出的元素
                    let element_obj = AbstractObject::ArrayElement {
                        id: self.new_object_id(),
                        base: Box::new(storage_obj),
                        index: None, // 未知索引（数组末尾元素）
                        ty: var.ty.clone(),
                    };
                    
                    // 为弹出的元素创建一个指向关系到结果变量
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (*res, self.current_context.clone()),
                        var: element_obj,
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
            // 处理Push/Pop Memory
            Instr::PushMemory { res, array, value, .. } => {
                // 处理内存数组Push操作
                let mut constraints = Vec::new();
                
                if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(value, block_idx) {
                    let array_var = *array;
                    let array_ctx = self.current_context.clone();
                    // 获取数组对象
                    let array_objs = self.result.get_points_to(array_var, &array_ctx);
                    
                    for array_obj in array_objs {
                        // 创建新元素对象
                        let element_obj = AbstractObject::ArrayElement {
                            id: self.new_object_id(),
                            base: Box::new(array_obj.clone()),
                            index: None, // 动态添加的元素
                            ty: value.ty().clone(),
                        };
                        
                        // 创建元素变量和结果变量的关联
                        constraints.push(PointerConstraint::AddressOf {
                            ptr: (*res, self.current_context.clone()),
                            var: element_obj.clone(),
                        });
                        
                        // 创建值到元素的约束
                        let element_var = element_obj.id().0;
                        
                        constraints.push(PointerConstraint::Copy {
                            dst: (element_var, Context::new()),
                            src: (val_var, val_ctx.clone()),
                        });
                    }
                }
                
                Some(constraints)
            }
            Instr::PopMemory { res, array, .. } => {
                // 处理内存数组Pop操作
                let mut constraints = Vec::new();
                let array_var = *array;
                let array_ctx = self.current_context.clone();

                // 获取数组对象
                let array_objs = self.result.get_points_to(array_var, &array_ctx);
                
                for array_obj in array_objs {
                    // 创建表示弹出元素的对象
                    let element_obj = AbstractObject::ArrayElement {
                        id: self.new_object_id(),
                        base: Box::new(array_obj.clone()),
                        index: None, // 最后一个元素
                        ty: self.cfg.vars[*res].ty.clone(),
                    };
                    
                    // 关联元素和结果变量
                    constraints.push(PointerConstraint::AddressOf {
                        ptr: (*res, self.current_context.clone()),
                        var: element_obj,
                    });
                }
                
                Some(constraints)
            },
            // 其他指令暂时不处理
            _ => None,
        }
    }
    
    /// 处理约束
    fn process_constraint(&mut self, constraint: PointerConstraint) -> Result<()> {
        println! ("constraint: {:?}", constraint);
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
                        src: val.clone(),
                    });
                }
            }
            PointerConstraint::Load { dst, ptr } => {
                // 处理指针加载约束: dst = *ptr
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
                        dst: dst.clone(),
                        src: (implicit_var, Context::new()),
                    });
                }
            }
            PointerConstraint::StaticCall { caller_context, callee_context, args, params, returns, ret_vals } => {
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
            PointerConstraint::DynamicCall { caller, args, returns , block_idx} => {
                // 获取函数变量指向的所有对象
                let (func_var, func_ctx) = caller;
                let func_objs = self.result.get_points_to(func_var, &func_ctx);
                let res = returns.iter().map(|(x, _)| { *x }).collect::<Vec<_>>();
                
                // 对于每个可能的函数对象，创建调用约束
                for func_obj in func_objs {
                    if let AbstractObject::Function { function_no, .. } = func_obj {
                        // 只有函数对象才能被调用
                        if let Some(callee_cfg) = self.all_cfgs.get(function_no) {
                            // 创建调用上下文
                            let callee_obj_id = self.new_object_id();
                            let mut callee_context = self.current_context.clone();
                            callee_context.push(callee_obj_id);
                            
                            // 添加到调用图
                            self.call_graph.add_edge(
                                (self.current_function_no, self.current_context.clone()),
                                (function_no, callee_context.clone()),
                                Some(block_idx)
                            );
                            
                            // 检查递归调用
                            if self.call_stack.contains(&(function_no, callee_context.clone())) {
                                // 发现递归，返回保守约束
                                let recursive_constraints = self.handle_recursive_call(function_no, callee_context.clone(), returns.clone());
                                if let Some(rc) = recursive_constraints {
                                    for c in rc {
                                        self.worklist.push_back(c.clone());
                                        self.var_constraints.push(c.clone());
                                    }
                                }
                                continue;
                            }
                            
                            // 防止重复分析
                            if !self.analyzed_functions.contains(&(function_no, callee_context.clone())) {
                                // 标记函数在该上下文中已经被分析
                                self.analyzed_functions.insert((function_no, callee_context.clone()));
                                
                                // 递归分析被调用函数
                                if let Some(()) = self.analyze_callee_function(function_no, callee_context.clone(), args.as_slice(), res.as_slice(), block_idx) {
                                    // 递归分析成功
                                }
                            }

                            // 处理参数
                            for (i, arg) in args.iter().enumerate() {
                                if let Ok((arg_no, arg_ctx)) = self.analyze_expr_to_var(arg, block_idx) {
                                    // 如果参数i存在于被调用的函数中
                                    if i < callee_cfg.param_num() {
                                        let param_no = callee_cfg.get_param_no(i);
                                        self.worklist.push_back(PointerConstraint::Copy {
                                            dst: (param_no, callee_context.clone()),
                                            src: (arg_no, arg_ctx)
                                        });
                                    }
                                }
                            }
                            
                            // 处理返回值
                            for (i, ret_var) in returns.iter().enumerate() {
                                let ret_val_no = callee_cfg.get_ret_no(i);
                                self.worklist.push_back(PointerConstraint::Copy {
                                    dst: ret_var.clone(),
                                    src: (ret_val_no, callee_context.clone()) 
                                });
                            }
                        }
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// 在指向关系更新后更新工作列表
    fn update_worklist_after_points_to_change(&mut self, var: usize, context: &Context) {
        /*
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
        */

        if let Some(constraints) = self.var_constraints.get((var, context.clone())) {
            for constraint in constraints {
                self.worklist.push_back(constraint.clone());
            }
        }
    }
    
    /// 查找所有以指定变量为指针的Load约束
    fn find_load_constraints_for_ptr(&mut self, var: usize, context: &Context) -> Vec<PointerConstraint> {
        // 创建一个新的约束列表来收集结果
        let mut load_constraints = Vec::new();
        
        // 遍历所有已处理的约束
        for (block_idx, block) in self.cfg.blocks.iter().enumerate() {
            for instr in &block.instr {
                // 检查Load指令
                if let Instr::Set { res, expr, .. } = instr {
                    if let Expression::Load { expr: inner_expr, .. } = expr {
                        // 分析表达式，检查是否使用了我们的变量
                        if let Ok((ptr_var, ptr_ctx)) = self.analyze_expr_to_var(inner_expr, block_idx) {
                            if ptr_var == var && ptr_ctx == *context {
                                // 找到了对应的Load约束
                                load_constraints.push(PointerConstraint::Load {
                                    dst: (*res, self.current_context.clone()),
                                    ptr: (var, context.clone()),
                                });
                            }
                        }
                    }
                }
            }
        }
        
        load_constraints
    }
    
    /// 查找所有以指定变量为指针的Store约束
    fn find_store_constraints_for_ptr(&mut self, var: usize, context: &Context) -> Vec<PointerConstraint> {
        let mut store_constraints = Vec::new();
        
        // 遍历所有已处理的约束
        for (block_idx, block) in self.cfg.blocks.iter().enumerate() {
            for instr in &block.instr {
                // 检查Store指令
                if let Instr::Store { dest, data, .. } = instr {
                    if let Ok((ptr_var, ptr_ctx)) = self.analyze_expr_to_var(dest, block_idx) {
                        if ptr_var == var && ptr_ctx == *context {
                            // 找到了对应的Store约束
                            if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(data, block_idx) {
                                store_constraints.push(PointerConstraint::Store {
                                    ptr: (var, context.clone()),
                                    val: (val_var, val_ctx),
                                });
                            }
                        }
                    }
                }
                
                // 检查WriteBuffer指令等同样是存储操作的指令
                if let Instr::WriteBuffer { buf, value, offset } = instr {
                    if let Ok((buf_var, buf_ctx)) = self.analyze_expr_to_var(buf, block_idx) {
                        if buf_var == var && buf_ctx == *context {
                            // 找到了对应的存储约束
                            if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(value, block_idx) {
                                store_constraints.push(PointerConstraint::Store {
                                    ptr: (var, context.clone()),
                                    val: (val_var, val_ctx),
                                });
                            }
                        }
                    }
                }
            }
        }
        
        store_constraints
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
            },
            Expression::FunctionArg { arg_no, .. } => {
                let var_no = self.cfg.get_param_no(*arg_no);
                constraints.push(PointerConstraint::Copy {
                    dst: (res, self.current_context.clone()),
                    src: (var_no, self.current_context.clone()),
                });
            },
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
                        // 写入缓冲区，参数0是目标指针，参数1是值，参数2是偏移
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

                    /*
                    Builtin::ArrayPush => {
                        // 处理数组Push操作
                        if args.len() >= 2 {
                            if let Ok((array_var, array_ctx)) = self.analyze_expr_to_var(&args[0], block_idx) {
                                if let Ok((val_var, val_ctx)) = self.analyze_expr_to_var(&args[1], block_idx) {
                                    // 获取数组指向的对象
                                    let array_objs = self.result.get_points_to(array_var, &array_ctx);
                                    
                                    for array_obj in array_objs {
                                        // 为新的数组元素创建抽象对象
                                        let element_obj = AbstractObject::ArrayElement {
                                            id: self.new_object_id(),
                                            base: Box::new(array_obj.clone()),
                                            index: None, // 未知索引（动态增长）
                                            ty: args[1].ty().clone(),
                                        };
                                        
                                        // 创建从值到新元素的约束
                                        let element_var = element_obj.id().0;
                                        
                                        self.worklist.push_back(PointerConstraint::AddressOf {
                                            ptr: (element_var, Context::new()),
                                            var: element_obj,
                                        });
                                        
                                        self.worklist.push_back(PointerConstraint::Copy {
                                            dst: (element_var, Context::new()),
                                            src: (val_var, val_ctx.clone()),
                                        });
                                        
                                        // 将函数结果设置为新元素的引用
                                        constraints.push(PointerConstraint::Copy {
                                            dst: (res, self.current_context.clone()),
                                            src: (element_var, Context::new()),
                                        });
                                    }
                                }
                            }
                        }
                    }
                    Builtin::ArrayPop => {
                        // 处理数组Pop操作
                        if args.len() >= 1 {
                            if let Ok((array_var, array_ctx)) = self.analyze_expr_to_var(&args[0], block_idx) {
                                // 获取数组指向的对象
                                let array_objs = self.result.get_points_to(array_var, &array_ctx);
                                
                                for array_obj in array_objs {
                                    // 创建一个表示数组末尾元素的抽象对象
                                    let element_obj = AbstractObject::ArrayElement {
                                        id: self.new_object_id(),
                                        base: Box::new(array_obj.clone()),
                                        index: None, // 未知索引（最后一个元素）
                                        ty: expr.ty().clone(),
                                    };
                                    
                                    // 创建从末尾元素到结果的约束
                                    constraints.push(PointerConstraint::AddressOf {
                                        ptr: (res, self.current_context.clone()),
                                        var: element_obj,
                                    });
                                }
                            }
                        }
                    }
                    */
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
            Expression::StructMember { expr: base_expr, member, ty, .. } => {
                // 处理结构体成员访问：res = base.field
                if let Ok((base_var, base_ctx)) = self.analyze_expr_to_var(base_expr, block_idx) {
                    // 获取基址指向的对象
                    let base_objs = self.result.get_points_to(base_var, &base_ctx);
                    
                    if base_objs.is_empty() {
                        // 基址对象不存在，创建一个通用的对象
                        let field_obj = AbstractObject::Field {
                            id: self.new_object_id(),
                            base: Box::new(AbstractObject::Unknown {
                                id: self.new_object_id(),
                            }),
                            field: *member,
                            ty: ty.clone(),
                        };
                        
                        constraints.push(PointerConstraint::AddressOf {
                            ptr: (res, self.current_context.clone()),
                            var: field_obj,
                        });
                    } else {
                        for base_obj in base_objs {
                            // 创建表示字段的抽象对象
                            let field_obj = AbstractObject::Field {
                                id: self.new_object_id(),
                                base: Box::new(base_obj.clone()),
                                field: *member,
                                ty: ty.clone(),
                            };
                            
                            // 创建从字段到结果的约束
                            constraints.push(PointerConstraint::AddressOf {
                                ptr: (res, self.current_context.clone()),
                                var: field_obj,
                            });
                        }
                    }
                }
            }
            Expression::Subscript { expr, index, ty, .. } => {
                // 处理数组索引：res = array[index]
                if let Ok((array_var, array_ctx)) = self.analyze_expr_to_var(expr, block_idx) {
                    // 获取数组指向的对象
                    let array_objs = self.result.get_points_to(array_var, &array_ctx);
                    
                    // 尝试计算索引的具体值
                    let index_value = if let Expression::NumberLiteral { value, .. } = index.deref() {
                        Some(value.clone())
                    } else {
                        None
                    };
                    
                    if array_objs.is_empty() {
                        // 数组对象不存在，创建一个通用的元素对象
                        let element_obj = AbstractObject::ArrayElement {
                            id: self.new_object_id(),
                            base: Box::new(AbstractObject::Unknown {
                                id: self.new_object_id(),
                            }),
                            index: index_value,
                            ty: ty.clone(),
                        };
                        
                        constraints.push(PointerConstraint::AddressOf {
                            ptr: (res, self.current_context.clone()),
                            var: element_obj,
                        });
                    } else {
                        for array_obj in array_objs {
                            // 创建表示数组元素的抽象对象
                            let element_obj = AbstractObject::ArrayElement {
                                id: self.new_object_id(),
                                base: Box::new(array_obj.clone()),
                                index: index_value.clone(),
                                ty: ty.clone(),
                            };
                            
                            // 创建从元素到结果的约束
                            constraints.push(PointerConstraint::AddressOf {
                                ptr: (res, self.current_context.clone()),
                                var: element_obj,
                            });
                        }
                    }
                }
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
            /*
            Expression::StorageVariable { contract_no, var_no, .. } => {
                Ok(AbstractObject::Global {
                    id: self.new_object_id(),
                    var_no: *var_no,
                    contract_no: Some(*contract_no),
                })
            }
            */
            // 其他表达式类型，创建未知对象
            _ => Ok(AbstractObject::Unknown {
                id: self.new_object_id(),
            }),
        }
    }
    
    /// 从存储表达式创建存储对象
    fn create_storage_object_from_expr(&mut self, expr: &Expression) -> Result<AbstractObject> {
        // 尝试解析存储槽表达式，计算实际的存储槽位置
        match expr {
            Expression::NumberLiteral { value, .. } => {
                // 直接使用字面量槽位
                Ok(AbstractObject::StorageSlot {
                    id: self.new_object_id(),
                    slot: value.clone(),
                })
            }
            Expression::Add { left, right, .. } => {
                // 处理存储槽偏移计算
                if let Expression::NumberLiteral { value: left_val, .. } = &**left {
                    if let Expression::NumberLiteral { value: right_val, .. } = &**right {
                        // 如果两个操作数都是常量，直接计算偏移
                        let slot = left_val + right_val;
                        return Ok(AbstractObject::StorageSlot {
                            id: self.new_object_id(),
                            slot,
                        });
                    }
                }
                
                // 无法精确计算存储槽位置，创建一个通用的存储槽对象
                Ok(AbstractObject::StorageSlot {
                    id: self.new_object_id(),
                    slot: BigInt::from(0), // 使用0作为通用槽
                })
            }
            // 处理映射存储槽的计算 (例如 keccak256(key . slot))
            Expression::Builtin { kind: Builtin::Keccak256, args, .. } => {
                // 标记为特殊的散列存储槽
                Ok(AbstractObject::StorageSlot {
                    id: self.new_object_id(),
                    slot: BigInt::from(-1), // -1表示散列槽
                })
            }
            Expression::Variable { var_no, .. } => {
                // 对于变量表示的存储位置，尝试查找其可能的值
                let objects = self.result.get_points_to(*var_no, &self.current_context);
                
                if objects.is_empty() {
                    // 如果没有找到指向关系，创建新的存储对象
                    Ok(AbstractObject::StorageSlot {
                        id: self.new_object_id(),
                        slot: BigInt::from(-2), // -2表示未知槽
                    })
                } else {
                    // 从已有对象中寻找存储槽
                    for obj in objects {
                        if let AbstractObject::StorageSlot { slot, .. } = obj {
                            return Ok(AbstractObject::StorageSlot {
                                id: self.new_object_id(),
                                slot,
                            });
                        }
                    }
                    
                    // 找不到存储槽，创建一个新的
                    Ok(AbstractObject::StorageSlot {
                        id: self.new_object_id(),
                        slot: BigInt::from(-2), // -2表示未知槽
                    })
                }
            }
            // 其他存储表达式类型
            _ => Ok(AbstractObject::StorageSlot {
                id: self.new_object_id(),
                slot: BigInt::from(-2), // -2表示未知槽
            }),
        }
    }
    
    /// 创建一个代表地址的对象
    fn create_address_object(&mut self) -> Option<AbstractObject> {
        Some(AbstractObject::Allocation {
            id: self.new_object_id(),
            ty: Type::Address(false),
            size: None,
        })
    }

    /// 解析虚函数，找到实际实现
    fn resolve_virtual_function(&self, func_no: usize) -> usize {
        // 在实际实现中，需要查找合约继承链以找到正确的实现
        if let Some(function) = self.ns.functions.get(func_no) {
            if function.is_virtual && function.contract_no.is_some() {
                // 在合约中查找可能的覆盖实现
                if let Some(contract_no) = function.contract_no {
                    if let Some(contract) = self.ns.contracts.get(contract_no) {
                        // 检查合约的基类，查找覆盖实现
                        for base in &contract.bases {
                            let ref base_no = base.contract_no;
                            // 在基类中查找函数，递归向下
                            if let Some(base_contract) = self.ns.contracts.get(*base_no) {
                                for (f_no, base_func_no) in base_contract.functions.iter().enumerate() {
                                    if let Some(base_func) = self.ns.functions.get(*base_func_no) {
                                        if base_func.signature == function.signature {
                                            // 找到覆盖实现
                                            return f_no;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        func_no // 如果找不到覆盖实现，返回原始函数
    }

    /// 处理递归调用，返回保守的约束
    fn handle_recursive_call(
        &mut self,
        func_no: usize,
        context: Context, 
        ret_vars: Vec<(usize, Context)>
    ) -> Option<Vec<PointerConstraint>> {
        let mut constraints = Vec::new();
        
        // 为递归调用添加保守的约束
        // 例如，假设返回值可能指向任何对象
        for ret_var in ret_vars {
            let unknown_obj = AbstractObject::Unknown {
                id: self.new_object_id(),
            };
            
            constraints.push(PointerConstraint::AddressOf {
                ptr: ret_var,
                var: unknown_obj,
            });
        }
        
        // 添加到调用图以表示递归关系
        self.call_graph.add_edge(
            (self.current_function_no, self.current_context.clone()),
            (func_no, context),
            None // 不指定调用点，因为它只是为了记录递归关系
        );
        
        Some(constraints)
    }
    
    /// 递归分析被调用函数
    fn analyze_callee_function(
        &mut self,
        func_no: usize,
        context: Context,
        args: &[Expression],
        ret_vars: &[usize],
        call_block: usize
    ) -> Option<()> {
        // 保存当前状态
        let saved_context = self.current_context.clone();
        let saved_function_no = self.current_function_no;
        
        // 设置新状态
        self.current_context = context.clone();
        self.current_function_no = func_no;
        
        // 添加到调用图
        self.call_graph.add_edge(
            (saved_function_no, saved_context.clone()),
            (func_no, context.clone()),
            Some(call_block)
        );
        
        // 将被调用函数添加到调用栈
        self.call_stack.push((func_no, context.clone()));
        
        if let Some(callee_cfg) = self.all_cfgs.get(func_no) {
            // 创建一个新的分析器来分析被调用函数
            let mut callee_analyzer = PointerAnalyzer {
                ns: self.ns,
                cfg: callee_cfg,
                all_cfgs: self.all_cfgs,
                current_context: context.clone(),
                result: self.result.clone(),
                worklist: VecDeque::new(),
                next_object_id: self.next_object_id,
                analyzed_functions: self.analyzed_functions.clone(),
                call_stack: self.call_stack.clone(),
                call_graph: self.call_graph.clone(),
                current_function_no: func_no,
                var_constraints: Constraints::new()
            };
            
            // 初始化并分析被调用函数
            callee_analyzer.initialize_constraints();
            
            // 处理约束
            while let Some(constraint) = callee_analyzer.worklist.pop_front() {
                if let Err(_) = callee_analyzer.process_constraint(constraint) {
                    // 错误处理
                }
            }
            
            // 更新我们的状态
            self.result = callee_analyzer.result;
            self.next_object_id = callee_analyzer.next_object_id;
            self.analyzed_functions = callee_analyzer.analyzed_functions;
            self.call_graph = callee_analyzer.call_graph;
        }
        
        // 从调用栈中移除
        self.call_stack.pop();
        
        // 恢复状态
        self.current_context = saved_context;
        self.current_function_no = saved_function_no;
        
        Some(())
    }
}

/// Call graph representation for interprocedural analysis
#[derive(Default, Debug, Clone)]
pub struct CallGraph {
    /// Maps caller function to its callees: (caller_func_no, caller_context) -> [(callee_func_no, callee_context)]
    edges: HashMap<(usize, Context), HashSet<(usize, Context)>>,
    
    /// Tracks call sites: (caller_func_no, caller_context, call_site_block) -> (callee_func_no, callee_context)
    call_sites: HashMap<(usize, Context, usize), HashSet<(usize, Context)>>,
    
    /// Tracks reverse call edges for faster lookups
    reverse_edges: HashMap<(usize, Context), HashSet<(usize, Context)>>,
}

impl CallGraph {
    /// Create a new empty call graph
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
            call_sites: HashMap::new(),
            reverse_edges: HashMap::new(),
        }
    }
    
    /// Add an edge to the call graph
    pub fn add_edge(
        &mut self, 
        caller: (usize, Context), 
        callee: (usize, Context),
        call_site_block: Option<usize>
    ) {
        // Add forward edge
        self.edges
            .entry(caller.clone())
            .or_insert_with(HashSet::new)
            .insert(callee.clone());
        
        // Add reverse edge
        self.reverse_edges
            .entry(callee.clone())
            .or_insert_with(HashSet::new)
            .insert(caller.clone());
        
        // Add call site if provided
        if let Some(block) = call_site_block {
            self.call_sites
                .entry((caller.0, caller.1.clone(), block))
                .or_insert_with(HashSet::new)
                .insert(callee);
        }
    }
    
    /// Get all callees of a function
    pub fn get_callees(&self, func_no: usize, context: &Context) -> HashSet<(usize, Context)> {
        self.edges
            .get(&(func_no, context.clone()))
            .cloned()
            .unwrap_or_default()
    }
    
    /// Get all callers of a function
    pub fn get_callers(&self, func_no: usize, context: &Context) -> HashSet<(usize, Context)> {
        self.reverse_edges
            .get(&(func_no, context.clone()))
            .cloned()
            .unwrap_or_default()
    }
    
    /// Check if there's a path between two functions
    pub fn has_path(&self, from: (usize, Context), to: (usize, Context)) -> bool {
        let mut visited = HashSet::new();
        let mut stack = vec![from];
        
        while let Some(node) = stack.pop() {
            if node == to {
                return true;
            }
            
            if visited.insert(node.clone()) {
                if let Some(callees) = self.edges.get(&node) {
                    for callee in callees {
                        stack.push(callee.clone());
                    }
                }
            }
        }
        
        false
    }
    
    /// Find recursive cycles in the call graph
    pub fn find_recursive_cycles(&self) -> Vec<Vec<(usize, Context)>> {
        let mut cycles = Vec::new();
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        let mut curr_path = Vec::new();
        
        for node in self.edges.keys() {
            if !visited.contains(node) {
                self.dfs_find_cycles(
                    node, 
                    &mut visited, 
                    &mut rec_stack, 
                    &mut curr_path, 
                    &mut cycles
                );
            }
        }
        
        cycles
    }
    
    /// DFS helper for finding cycles
    fn dfs_find_cycles(
        &self,
        node: &(usize, Context),
        visited: &mut HashSet<(usize, Context)>,
        rec_stack: &mut HashSet<(usize, Context)>,
        curr_path: &mut Vec<(usize, Context)>,
        cycles: &mut Vec<Vec<(usize, Context)>>
    ) {
        visited.insert(node.clone());
        rec_stack.insert(node.clone());
        curr_path.push(node.clone());
        
        if let Some(neighbors) = self.edges.get(node) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    self.dfs_find_cycles(neighbor, visited, rec_stack, curr_path, cycles);
                } else if rec_stack.contains(neighbor) {
                    // Found a cycle
                    let cycle_start = curr_path.iter().position(|x| x == neighbor).unwrap();
                    let cycle = curr_path[cycle_start..].to_vec();
                    cycles.push(cycle);
                }
            }
        }
        
        rec_stack.remove(node);
        curr_path.pop();
    }
    
    /// Generate a graphical representation of the call graph
    pub fn to_dot(&self, ns: &Namespace) -> String {
        let mut result = String::from("digraph CallGraph {\n");
        result.push_str("  node [shape=box];\n");
        
        // Add nodes
        for ((func_no, ctx), _) in &self.edges {
            let func_name = if let Some(func) = ns.functions.get(*func_no) {
                func.id.name.clone()
            } else {
                format!("Function_{}", func_no)
            };
            
            let node_id = format!("\"{}_{:?}\"", func_name, ctx);
            result.push_str(&format!("  {} [label=\"{}\"];\n", node_id, func_name));
        }
        
        // Add edges
        for ((caller_no, caller_ctx), callees) in &self.edges {
            let caller_name = if let Some(func) = ns.functions.get(*caller_no) {
                func.id.name.clone()
            } else {
                format!("Function_{}", caller_no)
            };
            
            let caller_id = format!("\"{}_{:?}\"", caller_name, caller_ctx);
            
            for (callee_no, callee_ctx) in callees {
                let callee_name = if let Some(func) = ns.functions.get(*callee_no) {
                    func.id.name.clone()
                } else {
                    format!("Function_{}", callee_no)
                };
                
                let callee_id = format!("\"{}_{:?}\"", callee_name, callee_ctx);
                result.push_str(&format!("  {} -> {};\n", caller_id, callee_id));
            }
        }
        
        result.push_str("}\n");
        result
    }

    /// Get all functions in the call graph
    pub fn get_all_functions(&self) -> HashSet<usize> {
        let mut result = HashSet::new();
        
        // Add all callers
        for (func_no, _) in self.edges.keys() {
            result.insert(*func_no);
        }
        
        // Add all callees 
        for callees in self.edges.values() {
            for (func_no, _) in callees {
                result.insert(*func_no);
            }
        }
        
        result
    }
    
    /// Find entry points (functions that are not called by anyone else)
    pub fn find_entry_points(&self) -> HashSet<usize> {
        let mut entry_points = self.get_all_functions();
        
        // Remove functions that are called by others
        for callees in self.edges.values() {
            for (func_no, _) in callees {
                entry_points.remove(func_no);
            }
        }
        
        entry_points
    }
    
    /// Find leaf functions (functions that don't call any other function)
    pub fn find_leaf_functions(&self) -> HashSet<usize> {
        let mut result = HashSet::new();
        
        for ((func_no, _), callees) in &self.edges {
            if callees.is_empty() {
                result.insert(*func_no);
            }
        }
        
        // Also add functions that are called but don't have any outgoing edges
        for callees in self.edges.values() {
            for (func_no, _) in callees {
                if !self.edges.contains_key(&(*func_no, Context::new())) {
                    result.insert(*func_no);
                }
            }
        }
        
        result
    }
    
    /// Compute function reachability from a given function
    pub fn compute_reachable_functions(&self, from_func: usize) -> HashSet<usize> {
        let mut visited = HashSet::new();
        let mut stack = vec![(from_func, Context::new())];
        
        while let Some(node) = stack.pop() {
            if !visited.insert(node.clone()) {
                continue;
            }
            
            if let Some(callees) = self.edges.get(&node) {
                for callee in callees {
                    stack.push(callee.clone());
                }
            }
        }
        
        visited.into_iter().map(|(func_no, _)| func_no).collect()
    }
}

/// 公共API函数：分析指定合约中的CFG
pub fn analyze_contract_pointers(
    contract_no: usize,
    ns: &Namespace,
) -> Result<HashMap<usize, PointerAnalysisComplete>> {
    let mut results = HashMap::new();
    let mut global_call_graph = CallGraph::new();
    
    // 获取合约的所有CFG
    if let Some(contract) = ns.contracts.get(contract_no) {
        let all_cfgs = &contract.cfg;
        
        // 分析每个CFG
        for (cfg_idx, cfg) in all_cfgs.iter().enumerate() {
            if !cfg.is_placeholder() {
                let mut analyzer = PointerAnalyzer::new(ns, cfg, all_cfgs, cfg_idx);
                let (result, call_graph) = analyzer.analyze()?;
                
                // 合并调用图
                for ((caller, caller_ctx), callees) in &call_graph.edges {
                    for callee in callees {
                        global_call_graph.add_edge(
                            (*caller, caller_ctx.clone()),
                            callee.clone(),
                            None
                        );
                    }
                }
                
                results.insert(cfg_idx, PointerAnalysisComplete {
                    result,
                    call_graph: global_call_graph.clone(),
                });
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
) -> Result<PointerAnalysisComplete> {
    if let Some(contract) = ns.contracts.get(contract_no) {
        if let Some(cfg) = contract.cfg.get(function_idx) {
            if !cfg.is_placeholder() {
                let mut analyzer = PointerAnalyzer::new(ns, cfg, &contract.cfg, function_idx);
                let (result, call_graph) = analyzer.analyze()?;
                
                return Ok(PointerAnalysisComplete {
                    result,
                    call_graph,
                });
            }
        }
    }
    
    Err(PointerAnalysisError::Other(format!(
        "函数 #{} 在合约 #{} 中不存在或是占位符",
        function_idx, contract_no
    )))
}

/// 公共API函数：获取函数调用图
pub fn get_call_graph(
    results: &HashMap<usize, PointerAnalysisComplete>,
) -> CallGraph {
    // 合并所有函数的调用图
    let mut combined_graph = CallGraph::new();
    
    for (_, complete) in results {
        for ((caller, caller_ctx), callees) in &complete.call_graph.edges {
            for callee in callees {
                combined_graph.add_edge(
                    (*caller, caller_ctx.clone()),
                    callee.clone(),
                    None
                );
            }
        }
    }
    
    combined_graph
}

/// 将调用图导出为DOT格式
pub fn call_graph_to_dot(call_graph: &CallGraph, ns: &Namespace) -> String {
    call_graph.to_dot(ns)
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
