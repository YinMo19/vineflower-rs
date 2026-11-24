// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{Bytecode, Constant, Instruction, KotlinError, Locals, Operand, StackValue, lambdas, templates};

const CONCAT: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
const WITH_CONSTANTS: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";
const METAFACTORY: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Factory { Concat, ConcatWithConstants, Lambda }

struct Site<'a> {
    factory: Factory,
    name: &'a str,
    descriptor: &'a str,
    arguments: &'a [u16],
}

fn site<'a>(bytecode: &'a Bytecode<'_, '_>, instruction: &Instruction, locals: &'a Locals<'_>, declaration: &str)
    -> Result<Option<Site<'a>>, KotlinError>
{
    if instruction.opcode != 0xba {
        return Ok(None);
    }
    let invalid = || KotlinError::unsupported(declaration, "invalid Kotlin invokedynamic site");
    let pool = &bytecode.class.pool;
    let Operand::Constant(index) = instruction.operand else { return Err(invalid()); };
    let Constant::InvokeDynamic { bootstrap_index, name_and_type_index } = *pool.get(index)? else {
        return Err(invalid());
    };
    if locals.bootstraps.get().is_none() {
        let _ = locals.bootstraps.set(bytecode.class.bootstrap_methods()?);
    }
    let bootstrap = locals.bootstraps.get().unwrap().get(usize::from(bootstrap_index)).ok_or_else(invalid)?;
    let Constant::MethodHandle { reference_kind: 6, reference_index } = *pool.get(bootstrap.method_ref)? else {
        return Err(invalid());
    };
    if !matches!(pool.get(reference_index)?, Constant::Methodref { .. }) {
        return Err(invalid());
    }
    let factory = match pool.member_ref(reference_index)? {
        ("java/lang/invoke/StringConcatFactory", "makeConcat", CONCAT) => Factory::Concat,
        ("java/lang/invoke/StringConcatFactory", "makeConcatWithConstants", WITH_CONSTANTS) => Factory::ConcatWithConstants,
        ("java/lang/invoke/LambdaMetafactory", "metafactory", METAFACTORY) => Factory::Lambda,
        _ => return Err(KotlinError::unsupported(declaration, "unsupported Kotlin invokedynamic bootstrap")),
    };
    let (name, descriptor) = pool.name_and_type(name_and_type_index)?;
    Ok(Some(Site { factory, name, descriptor, arguments: &bootstrap.arguments }))
}

pub(super) fn has_lambda(bytecode: &Bytecode<'_, '_>, instructions: &[Instruction], locals: &Locals<'_>, declaration: &str)
    -> Result<bool, KotlinError>
{
    for instruction in instructions {
        if site(bytecode, instruction, locals, declaration)?.is_some_and(|site| site.factory == Factory::Lambda) {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn lower<'a>(bytecode: &Bytecode<'a, '_>, instruction: &Instruction, locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>, declaration: &str) -> Result<bool, KotlinError>
{
    let Some(site) = site(bytecode, instruction, locals, declaration)? else { return Ok(false); };
    let expr = match (site.factory, site.name) {
        (Factory::Concat, "makeConcat") | (Factory::ConcatWithConstants, "makeConcatWithConstants") => {
            templates::indy(bytecode, site.descriptor, site.arguments, site.factory == Factory::ConcatWithConstants,
                locals, stack, declaration)?
        }
        (Factory::Lambda, "invoke") => lambdas::lower(bytecode, site.descriptor, site.arguments, locals, stack, declaration)?,
        _ => return Err(KotlinError::unsupported(declaration, "invokedynamic name does not match its Kotlin bootstrap")),
    };
    stack.push(StackValue::Value(expr));
    Ok(true)
}
