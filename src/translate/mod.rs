use quote::{format_ident, quote, ToTokens};
use proc_macro2::TokenStream;
use forge_fmt::visit;
use solang_parser::helpers::CodeLocation;

use crate::codegen::cfg::ControlFlowGraph;
use crate::sema::symtable::Symtable;
use crate::sema::ast::{self, FunctionAttributes, Namespace};

mod analysis;
use analysis::pointer::{ PointerAnalyzer, analyze_contract_pointers };

pub fn visit_namespace(ns: &ast::Namespace) {
    // Visit other top-level declarations like pragmas, imports, etc.
    if !ns.pragmas.is_empty() {
        println!("Pragmas:");
        for pragma in &ns.pragmas {
            println!("    {:#?}", pragma);
        }
    }

    println!("Events:");
    ns.events.iter().for_each(|event| {
        println!("Event: {} (fields: {:#?})", event.id.name, event.fields);
    });
    println!("Structs:");
    ns.structs.iter().for_each(|struct_| {
        println!("Struct: {} (fields: {:#?})", struct_.id.name, struct_.fields);
    });

    println!("Namespace Structure:");

    for (ref contract_no, contract) in ns.contracts.iter().enumerate() {
        visit_contract(contract_no, contract, 0, ns);
    }

}

fn visit_contract(contract_no: &usize, contract: &ast::Contract, indent: usize, ns: &ast::Namespace) {
    let indent_str = "  ".repeat(indent);

    if contract.id.name != "ERC20" {
        return;
    }
    println!("{}Contract: {} (type: {:?})", indent_str, contract.id.name, contract.ty);
    // println! ("{}  Contract content: {:#?}", indent_str, contract);
    // println! ("{}  content: {:#?}", indent_str, contract);

    /*
    if !contract.variables.is_empty() {
        println!("{}Variables:", indent_str);
        for var in &contract.variables {
            println!("{}  {} : {:?}", indent_str, var.name, var.ty);
        }
    }
    
    // Print functions
    if !contract.functions.is_empty() {
        println!("{}Functions:", indent_str);
        for fid in &contract.functions {
            let function_entity = &ns.functions[*fid];
            visit_function(function_entity, indent + 1, ns);
        }
    }
    */
    let ref result = analyze_contract_pointers(*contract_no, ns);

    for cfg in &contract.cfg {        
        println!("{}Control Flow Graph: {:#?} [{}]", indent_str, cfg.name, cfg.blocks.len());
        println!("{}  {:#?}", indent_str, cfg.params);
        println!("{}  {:#?}", indent_str, cfg.returns);
        println!("{}  points-to results: {:#?}", indent_str, result);
        // analysis::ownership_analysis(cfg);

        /*
        if cfg.blocks.len() > 0 {
            let ptr_map = analysis::pointer::analyze_cfg(cfg);
            for i in 0..cfg.blocks.len() {
                let block = &cfg.blocks[i];
                println!("{}Block: {} (pointers {:?})", indent_str, block.name, ptr_map[&i]);
            }
        }
        */

        for block in &cfg.blocks {
            for instr in &block.instr {
                println!("{}  Instruction: {:?}", indent_str, instr);
            }
        }
    }
}

fn visit_function(function: &ast::Function, indent: usize, ns: &ast::Namespace) {
    let mut indent_str = "  ".repeat(indent);
    let symtbl = &function.symtable;
    println!("{}Function: {}", indent_str, function.id.name);
    indent_str = indent_str + " ";
    println!("{}Tag: {:?}", indent_str, function.tags);
    println!("{}Signature: {:?}", indent_str, function.signature);
    
    if function.modifiers.len() > 0 {
        println!("{}Modifiers:", indent_str);
        for modifier in function.modifiers.iter() {
            println!("{}  {}", indent_str, visit_expression(modifier, symtbl, ns));
        }
    }
    
    // Print parameters
    if !function.params.is_empty() {
        println!("{}Parameters:", indent_str);
        for param in function.params.iter() {
            let name = param.id.as_ref().map(|id| id.name.clone()).unwrap_or_else(|| "Unnamed".to_string());
            println!("{}  {} : {:?}", indent_str, name, param.ty);
        }
    }

    // Print return values
    if !function.returns.is_empty() {
        println!("{}Returns:", indent_str);
        for ret in function.returns.iter() {
            let name = ret.id.as_ref().map(|id| id.name.clone()).unwrap_or_else(|| "Unnamed".to_string());
            println!("{}  {} : {:?}", indent_str, name, ret.ty);
        }
    }
    if function.has_body {
        println!("{}Body:", indent_str);
        // Visit function body if available
        for stmt in function.body.iter() {
            visit_statement(stmt, indent + 1, symtbl, ns);
        }
    }
}

#[inline(always)]
fn visit_statement(stmt: &ast::Statement, indent: usize, symtbl: &Symtable, ns: &ast::Namespace) {
    let indent_str = "  ".repeat(indent);
    match stmt {
        ast::Statement::Block { unchecked, statements, .. } => {
            for stmt in statements {
                if *unchecked {
                    println!("{}unchecked {{", indent_str);
                } else {
                    println!("{}{{", indent_str);
                }
                visit_statement(stmt, indent + 1, symtbl, ns);
                println!("{}}}", indent_str);
            }
        }
        ast::Statement::If(_, _, cond, then_stmt, else_stmt) => {
            println!("{}if {} {{", indent_str, visit_expression(cond, symtbl, ns).to_string());
            for stmt in then_stmt {
                visit_statement(stmt, indent + 1, symtbl, ns);
            }
            println!("{}}} else {{", indent_str);
            for stmt in else_stmt {
                visit_statement(stmt, indent + 1, symtbl, ns);
            }
            println!("}}")
        }
        ast::Statement::Expression(_, _, ref expr) => {
            println!("{}E[[ {} ]];", indent_str, visit_expression(expr, symtbl, ns).to_string());
        }
        ast::Statement::Emit { event_no, ref args, .. } => {
            let event_name = &ns.events[*event_no].id.name.as_str();
            let args_tokens = args.iter()
                .map(|arg| visit_expression(arg, symtbl, ns))
                .collect::<Vec<_>>();
            let args = quote! { #(#args_tokens) ,* };
            println! ("{}emit {} ({});", indent_str,  event_name, args.to_string());
        }
        ast::Statement::Return(_, expr) => {
            if let Some(ref expr) = expr {
                println! ("{}return {};", indent_str, visit_expression(expr, symtbl, ns).to_string());
            } else {
                println! ("{}return;", indent_str);
            }
        }
        ast::Statement::VariableDecl(_, size, par, expr) => {
            let ty = format_ident! ("{}", par.ty.to_string(ns));
            let var_name = format_ident!("{}", par.name_as_str());
            let expr_tokens = expr.iter()
                .map(|e| visit_expression(e, symtbl, ns))
                .collect::<Vec<_>>();
            let expr = quote! { #(#expr_tokens) ,* };
            println! ("{}let {}: {}({}) = {};", indent_str, var_name, ty, (*size), expr.to_string());
        }
        ast::Statement::Underscore(_) => {
            println! ("_;");
        }
        _ => {
            // Handle other statement types as needed
            println!("{}Unknown statement: {:?}", indent_str, stmt);
        }    
    }
}

#[inline(always)]
fn visit_expression(expr: &ast::Expression, symtbl: &Symtable, ns: &Namespace) -> TokenStream {
    // Visit sub-expressions if applicable
    match expr {
        ast::Expression::BoolLiteral { value, .. } => {
            if *value {
                quote! { true }
            } else {
                quote! { false }
            }
        }
        ast::Expression::BytesLiteral { value, .. } => {
            let bytes = format! ("{:?}", value);
            quote! { BYTE(#bytes) }
        }
        ast::Expression::NumberLiteral { value, .. } => {
            let num = format! ("{:?}", value);
            quote! { NUM(#num) }
        }
        ast::Expression::RationalNumberLiteral { value, .. } => {
            let num = format! ("{:?}", value);
            quote! { RATIONAL(#num) }
        }
        /*
        ast::Expression::StructLiteral { id, ty, values, .. } => {
            let struct_name = id.identifiers.concat::<String>();
            let mut fields = Vec::new();
            for (i, value) in values.iter().enumerate() {
                let field_name = format_ident!("field_{}", i);
                let field_value = visit_expression(value);
                fields.push(quote! { #field_name: #field_value });
            }
            quote! { #struct_name { #(#fields),* } }
        } */
        ast::Expression::Assign { left, right, .. } => {
            let lvar = visit_expression(left, symtbl, ns);
            let rvar = visit_expression(right, symtbl, ns);
            quote! { #lvar = #rvar }
        }
        ast::Expression::Variable { var_no, .. } => {
            let name = format_ident!("{}", symtbl.get_name(*var_no));
            quote!{ #name }
        }
        ast::Expression::StorageVariable { contract_no, var_no, .. } => {
            let name = format_ident!("{}", ns.contracts[*contract_no].variables[*var_no].name);
            quote! { #name }
        }
        ast::Expression::ConstantVariable { contract_no, var_no, .. } => {
            let name = format_ident!("{}", match contract_no {
                Some(c) => ns.contracts[*c].variables[*var_no].name.as_str(),
                None => ns.constants[*var_no].name.as_str(),
            });
            quote! { #name };
            quote! { CONSTANT }
        }
        ast::Expression::NotEqual { left, right, .. } => {
            let lvar = visit_expression(left, symtbl, ns);
            let rvar = visit_expression(right, symtbl, ns);
            quote! { #lvar != #rvar }
        }
        ast::Expression::Add { left, right, .. } => {
            let lvar = visit_expression(left, symtbl, ns);
            let rvar = visit_expression(right, symtbl, ns);
            quote! { #lvar + #rvar }
        }
        ast::Expression::Subtract { left, right, .. } => {
            let lvar = visit_expression(left, symtbl, ns);
            let rvar = visit_expression(right, symtbl, ns);
            quote! { #lvar - #rvar }
        }
        ast::Expression::Subscript { array, index , .. } => {
            let array_var = visit_expression(array, symtbl, ns);
            let index_var = visit_expression(index, symtbl, ns);
            quote! { #array_var[#index_var] }
        }
        ast::Expression::Builtin { kind, args, .. }  => {
            let args = args.iter().map(|arg| visit_expression(arg, symtbl, ns));
            let s = format_ident!("{}", format! ("{:?}", kind));
            quote! { #s ( #(#args) ,* ) }
            
        }
        
        x => {
            let s = format! ("{:?}", x);
            quote! { (#s) }
        }
    }
}
