// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::collections::HashMap;

use super::{
    Bytecode, Constant, Instruction, JvmType, KotlinError, Locals, Member, MethodDescriptor,
    Operand, bytecode, extensions::exact_type, identifier, load_opcode, local_load, local_store,
    statements,
};
use crate::kotlin::{ClassDeclaration, Constructor, ValueParameter, Visibility};

pub(in crate::kotlin) struct Secondary<'a, 'data, 'metadata> {
    pub constructor: &'metadata Constructor,
    pub method: &'a Member<'data>,
    arguments: Vec<usize>,
    body_start: usize,
    pub block: statements::StatementBlock<'a>,
}

impl Secondary<'_, '_, '_> {
    pub fn write_delegation(&self, out: &mut String, declaration: &str) -> Result<(), KotlinError> {
        out.push_str(" : this(");
        for (index, &argument) in self.arguments.iter().enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            identifier(out, &self.constructor.parameters[argument].name, declaration)?;
        }
        out.push(')');
        Ok(())
    }

    pub fn delegation(&self) -> &[Instruction] {
        // The uninitialized receiver has no source expression of its own.
        &self.block.instructions[1..self.body_start]
    }

    pub fn write_statement(
        &self,
        statement: &statements::Statement<'_>,
        out: &mut String,
        declaration: &str,
    ) -> Result<(), KotlinError> {
        statement.write_exact_print(out, &self.constructor.parameters, declaration)
    }
}

pub(in crate::kotlin) fn recover<'a, 'data, 'metadata>(
    bytecode: &Bytecode<'a, 'data>,
    declaration: &'metadata ClassDeclaration,
    primary: &'metadata Constructor,
    trace: bool,
) -> Result<Vec<Secondary<'a, 'data, 'metadata>>, KotlinError> {
    let invalid = || KotlinError::unsupported(bytecode.owner, "unproven Kotlin constructor delegation");
    let constructors = &declaration.constructors;
    let mut signatures = HashMap::with_capacity(constructors.len());
    for (index, constructor) in constructors.iter().enumerate() {
        let signature = constructor.signature.as_ref().ok_or_else(invalid)?;
        let descriptor = &signature.descriptor;
        let access = match constructor.flags.visibility()? {
            Visibility::Public | Visibility::Internal => 0x0001,
            Visibility::Private | Visibility::PrivateToThis => 0x0002,
            Visibility::Protected => 0x0004,
            Visibility::Local => return Err(invalid()),
        };
        if constructor.flags.has_annotations()
            || signature.name != "<init>"
            || descriptor.return_type != JvmType::Void
            || descriptor.parameters.len() != constructor.parameters.len()
            || !constructor.parameters.iter().zip(&descriptor.parameters).all(|(parameter, jvm)| {
                // Only signatures with a direct Kotlin/JVM type match and no
                // hidden arguments, implicit null guards or overload defaults.
                parameter.flags.0 == 0 && parameter.vararg_element.is_none()
                    && (parameter.ty.nullable || matches!(jvm, JvmType::Primitive(_)))
                    && exact_type(&parameter.ty, jvm, false)
            })
            || signatures.insert(descriptor, (index, access)).is_some()
        {
            return Err(invalid());
        }
    }
    let pool = &bytecode.class.pool;
    let mut members = vec![None; constructors.len()];
    let mut targets = HashMap::with_capacity(constructors.len());
    for method in &bytecode.class.methods {
        if pool.utf8(method.name_index)? != "<init>" {
            continue;
        }
        let raw = pool.utf8(method.descriptor_index)?;
        let &(index, access) = signatures.get(&MethodDescriptor::parse(raw)?).ok_or_else(invalid)?;
        if method.access_flags != access || members[index].replace(method).is_some() {
            return Err(invalid());
        }
        targets.insert(raw, index);
    }

    let shadows_output = |name: &str| matches!(name, "System" | "kotlin");
    if declaration.name.relative_name().split('.').any(shadows_output)
        || declaration.nested_names.iter().any(|name| shadows_output(name))
        || declaration.members.properties.iter().any(|property| shadows_output(&property.name))
    {
        return Err(invalid());
    }
    let mut secondary = Vec::with_capacity(constructors.len() - 1);
    let mut delegates = vec![None; constructors.len()];
    for (index, (constructor, method)) in constructors.iter().zip(members).enumerate() {
        let method = method.ok_or_else(invalid)?;
        if std::ptr::eq(constructor, primary) {
            continue;
        }
        let descriptor = &constructor.signature.as_ref().expect("validated constructor signature").descriptor;
        let parameters = &constructor.parameters;
        if parameters.iter().any(|parameter| shadows_output(&parameter.name)) {
            return Err(invalid());
        }
        let mut locals = Locals::new(descriptor, true, parameters, bytecode.owner)?;
        locals.templates.member = Some(method);
        locals.templates.properties = &declaration.members.properties;
        let code = bytecode.code(method, bytecode.owner)?;
        let instructions = bytecode::decode(code.bytes)?;
        let Some((body_start, target)) = delegation_call(bytecode, &instructions)? else {
            return Err(invalid());
        };
        let target = *targets.get(target).ok_or_else(invalid)?;
        let loads = &instructions[1..body_start - 1];
        let target_constructor = &constructors[target];
        let target_descriptor = &target_constructor.signature.as_ref().expect("validated constructor signature").descriptor;
        if loads.len() != target_constructor.parameters.len() {
            return Err(invalid());
        }
        let arguments = loads.iter().zip(target_constructor.parameters.iter().zip(&target_descriptor.parameters))
            .map(|(load, (parameter, jvm))| argument(&locals, parameters, load, parameter, jvm).ok_or_else(invalid))
            .collect::<Result<Vec<_>, _>>()?;
        if !instructions.get(body_start..).and_then(|body| body.last()).is_some_and(|ret| ret.opcode == 0xb1) {
            return Err(invalid());
        }
        if instructions[body_start..].iter().any(|instruction| local_store(instruction).is_some())
            && code.local_variables(pool)?.iter().any(|local| {
                local.index >= locals.next_slot() && parameters.iter().any(|parameter| parameter.name == local.name)
            })
        {
            return Err(invalid());
        }
        let statements = statements::lower(bytecode, &instructions, body_start, &code, &locals, bytecode.owner)?;
        let lines = if trace { code.line_numbers(pool)? } else { Vec::new() };
        delegates[index] = Some(target);
        secondary.push(Secondary {
            constructor,
            method,
            arguments,
            body_start,
            block: statements::StatementBlock { statements, lines, instructions, implicit_return: true },
        });
    }

    // Every chain must terminate at the primary constructor, including when
    // a secondary delegates to a later declaration in metadata order.
    let mut visited = vec![None; constructors.len()];
    for start in 0..constructors.len() {
        let mut current = start;
        while let Some(next) = delegates[current] {
            match visited[current] {
                Some(origin) if origin == start => return Err(invalid()),
                Some(_) => break,
                None => visited[current] = Some(start),
            }
            current = next;
        }
    }
    Ok(secondary)
}

fn delegation_call<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
) -> Result<Option<(usize, &'a str)>, KotlinError> {
    let [receiver, rest @ ..] = instructions else { return Ok(None); };
    if local_load(receiver) != Some((0x19, 0)) {
        return Ok(None);
    }
    // Until the initializing invokespecial, only proven parameter loads can
    // appear. Never mistake a later allocation for the this(...) invocation.
    let Some((count, call)) = rest.iter().enumerate().find(|(_, instruction)| local_load(instruction).is_none()) else {
        return Ok(None);
    };
    let Operand::Constant(index) = call.operand else { return Ok(None); };
    if let Some((owner, "<init>", descriptor)) = bytecode.reference(call, 0xb7)?
        && owner == bytecode.owner
        && matches!(bytecode.class.pool.get(index)?, Constant::Methodref { .. })
    {
        return Ok(Some((count + 2, descriptor)));
    }
    Ok(None)
}

fn argument(
    locals: &Locals<'_>,
    parameters: &[ValueParameter],
    instruction: &Instruction,
    target: &ValueParameter,
    jvm: &JvmType,
) -> Option<usize> {
    let (load, slot) = local_load(instruction)?;
    let index = locals.parameter(slot, load)?;
    // A merely assignable expression can bind a different Kotlin overload.
    // Forward only an argument whose declared Kotlin and JVM types are exact.
    (load == load_opcode(jvm) && locals.slots[index].1 == jvm && parameters[index].ty == target.ty)
        .then_some(index)
}
