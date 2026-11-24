// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Kotlin/JVM lowers a non-capturing local extension to a private static
//! helper. Its JVM name alone does not establish either scope or receiver.

use crate::{
    classfile::LocalVariable,
    context::ClassGroup,
    kotlin::{Flags, PackageDeclaration, syntax::plain_identifier},
};

use super::{
    Body, Bytecode, Constant, Expr, ExpressionTrace, Extension, FINAL, Function, Instruction,
    JvmMethodSignature, JvmType, KotlinError, Member, MethodDescriptor, Operand, Primitive, STATIC,
    Type, ValueParameter, invocations,
};

pub(in crate::kotlin) struct Definition<'a, 'data> {
    pub function: Function,
    pub member: &'a Member<'data>,
    pub expr: Expr<'a>,
    pub trace: Option<ExpressionTrace>,
    pub(super) descriptor: &'a str,
}

pub(in crate::kotlin) fn recover<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    enclosing: &Function,
    signature: &JvmMethodSignature,
    caller: &'a Member<'data>,
    members: &PackageDeclaration,
    group: Option<&ClassGroup<'_>>,
    trace: bool,
) -> Result<Vec<Definition<'a, 'data>>, KotlinError> {
    if enclosing.name != signature.name || !plain_identifier(&signature.name) {
        return Ok(Vec::new());
    }
    let pool = &bytecode.class.pool;
    let mut candidates = Vec::new();
    // Most functions have no possible local helper. Avoid decoding the caller
    // twice in that case.
    for method in &bytecode.class.methods {
        if method.access_flags & !0x1000 != (0x0002 | STATIC | FINAL) {
            continue;
        }
        let jvm_name = pool.utf8(method.name_index)?;
        let Some(name) = jvm_name.strip_prefix(&signature.name).and_then(|s| s.strip_prefix('$')) else {
            continue;
        };
        if plain_identifier(name) && !members.functions.iter().any(|function| {
            function.signature.as_ref().is_some_and(|signature| signature.name == jvm_name)
        }) {
            candidates.push((method, jvm_name, pool.utf8(method.descriptor_index)?, name));
        }
    }
    if candidates.is_empty() {
        return Ok(Vec::new());
    }
    let invalid = || invalid_local(&enclosing.name);
    let caller_code = bytecode.function_code(caller, &enclosing.name)?;
    let mut locals = Vec::new();
    for instruction in super::bytecode::decode(caller_code.bytes)? {
        let Some((owner, jvm_name, raw)) = method_ref(bytecode, &instruction)? else { continue; };
        if owner != bytecode.owner || instruction.opcode != 0xb8 {
            continue;
        }
        let Some(&(method, _, _, name)) = candidates.iter().find(|(_, candidate, descriptor, _)| {
            *candidate == jvm_name && *descriptor == raw
        }) else { continue; };
        if locals.iter().any(|local: &Definition<'_, '_>| std::ptr::eq(local.member, method)) {
            continue;
        }
        if locals.iter().any(|local| local.function.name == name)
            || enclosing.parameters.iter().any(|param| param.name == name)
        {
            return Err(invalid());
        }
        let descriptor = MethodDescriptor::parse(raw)?;
        let [receiver, parameter] = descriptor.parameters.as_slice() else { return Err(invalid()); };
        let receiver_ty = builtin_type(receiver).ok_or_else(invalid)?;
        let parameter_ty = builtin_type(parameter).ok_or_else(invalid)?;
        let returns = builtin_type(&descriptor.return_type).ok_or_else(invalid)?;
        let code = bytecode.code(method, &enclosing.name)?;
        let debug = code.local_variables(pool)?;
        let name_at = |slot, jvm| debug_parameter(&debug, code.bytes.len(), slot, jvm).ok_or_else(invalid);
        let receiver_name = name_at(0, receiver)?;
        if receiver_name.strip_prefix("$this$")
            .and_then(|label| label.strip_prefix(&signature.name))
            .and_then(|label| label.strip_prefix("_u24")) != Some(name)
        {
            return Err(invalid());
        }
        let parameter_name = name_at(receiver.slots(), parameter)?;
        if !plain_identifier(parameter_name) {
            return Err(invalid());
        }
        let signature = JvmMethodSignature { name: jvm_name.to_owned(), descriptor };
        let function = Function {
            name: name.to_owned(),
            returns,
            type_parameters: Vec::new(),
            parameters: vec![ValueParameter {
                name: parameter_name.to_owned(), ty: parameter_ty, vararg_element: None, flags: Flags(0),
            }],
            receiver: Some(receiver_ty),
            context_receivers: Vec::new(),
            context_parameters: Vec::new(),
            // The local helper has no metadata infix bit. A single plain
            // argument admits an infix declaration; lexical binding is
            // checked independently when the original call is lowered.
            flags: Flags((5 << 1) | (1 << 9)),
            signature: Some(signature),
            contract: Vec::new(),
        };
        let signature = function.signature.as_ref().unwrap();
        let context = Extension::new(&function, signature, method, members, group)?;
        let Body::Expression(expr, trace) = bytecode.function(
            method, &signature.descriptor, &function.parameters, &function.returns,
            &members.properties, Some(context), name, trace,
        )? else { return Err(invalid()); };
        locals.push(Definition { function, member: method, expr, trace, descriptor: raw });
    }
    if !locals.is_empty() {
        // Hoisting a local `repeat` into another helper's lexical scope could
        // redirect that helper's separately recovered stdlib extension call.
        if locals.len() > 1 && locals.iter().any(|local| local.function.name == "repeat") {
            return Err(invalid());
        }
        let refers_to_local = |(owner, name, raw)| owner == bytecode.owner && locals.iter().any(|local| {
            local.function.signature.as_ref().unwrap().name == name && local.descriptor == raw
        });
        for method in &bytecode.class.methods {
            if std::ptr::eq(method, caller) {
                continue;
            }
            if let Some(code) = method.code(pool)? {
                for instruction in super::bytecode::decode(code.bytes)? {
                    if method_ref(bytecode, &instruction)?.is_some_and(refers_to_local) {
                        return Err(invalid());
                    }
                }
            }
        }
        for entry in pool.iter() {
            if let Constant::MethodHandle { reference_index, .. } = entry
                && matches!(pool.get(*reference_index)?, Constant::Methodref { .. } | Constant::InterfaceMethodref { .. })
                && refers_to_local(pool.member_ref(*reference_index)?)
            {
                return Err(invalid());
            }
        }
    }
    Ok(locals)
}

fn method_ref<'a>(
    bytecode: &Bytecode<'a, '_>,
    instruction: &Instruction,
) -> Result<Option<(&'a str, &'a str, &'a str)>, KotlinError> {
    let index = match (instruction.opcode, &instruction.operand) {
        (0xb6..=0xb8, Operand::Constant(index)) | (0xb9, Operand::InvokeInterface { index, .. }) => *index,
        _ => return Ok(None),
    };
    Ok(Some(bytecode.class.pool.member_ref(index)?))
}

fn debug_parameter<'a>(
    entries: &[LocalVariable<'a>],
    len: usize,
    slot: u16,
    jvm: &JvmType,
) -> Option<&'a str> {
    let mut matches = entries.iter().filter(|local| local.start_pc == 0 && local.index == slot);
    let local = matches.next()?;
    (matches.next().is_none() && usize::from(local.length) == len
        && JvmType::parse(local.descriptor).is_ok_and(|descriptor| descriptor == *jvm))
        .then_some(local.name)
}

pub(super) fn builtin_type(jvm: &JvmType) -> Option<Type> {
    let id = match jvm {
        JvmType::Primitive(Primitive::Boolean) => "kotlin/Boolean",
        JvmType::Primitive(Primitive::Byte) => "kotlin/Byte",
        JvmType::Primitive(Primitive::Char) => "kotlin/Char",
        JvmType::Primitive(Primitive::Short) => "kotlin/Short",
        JvmType::Primitive(Primitive::Int) => "kotlin/Int",
        JvmType::Primitive(Primitive::Long) => "kotlin/Long",
        JvmType::Primitive(Primitive::Float) => "kotlin/Float",
        JvmType::Primitive(Primitive::Double) => "kotlin/Double",
        JvmType::Object(owner) if owner == "java/lang/String" => "kotlin/String",
        JvmType::Object(owner) if owner == "java/lang/CharSequence" => "kotlin/CharSequence",
        _ => return None,
    };
    Some(invocations::kotlin_type(id))
}

fn invalid_local(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin local extension")
}
