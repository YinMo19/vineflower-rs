// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::ops::Range;

use super::{
    Bytecode, Expected, Expr, ExprKind, Instruction, KotlinError, Literal, Locals, Primitive,
    StackValue, ValueParameter, pop_value,
};

/// Statements and their original bytecode spans. Stack shuffles do not have
/// source expressions and are excluded by the mapping consumer.
pub(in crate::kotlin) struct StatementBlock<'a> {
    pub statements: Vec<Statement<'a>>,
    pub lines: Vec<(u16, u16)>,
    pub instructions: Vec<Instruction>,
}

pub(in crate::kotlin) struct Statement<'a> {
    pub instructions: Range<usize>,
    argument: Option<(Expr<'a>, Expected<'a>)>,
}

impl Statement<'_> {
    pub fn write(&self, out: &mut String, parameters: &[ValueParameter], declaration: &str) -> Result<(), KotlinError> {
        out.push_str("System.out.println(");
        if let Some((expr, expected)) = &self.argument {
            let null = matches!(expr.kind, ExprKind::Literal(Literal::Null));
            expr.write_at(out, *expected, parameters, declaration, 0)?;
            if null { out.push_str(" as kotlin.Any?"); }
        }
        out.push(')');
        Ok(())
    }
}

pub(super) fn lower<'a>(bytecode: &Bytecode<'a, '_>, instructions: &[Instruction], start: usize, locals: &Locals<'_>, declaration: &str) -> Result<Vec<Statement<'a>>, KotlinError> {
    let mut statements = Vec::new();
    let mut stack = Vec::new();
    let mut first = start;
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin statement bytecode");
    for (index, instruction) in instructions.iter().enumerate().take(instructions.len() - 1).skip(start) {
        if bytecode.reference(instruction, 0xb2)? == Some(("java/lang/System", "out", "Ljava/io/PrintStream;")) {
            stack.push(StackValue::PrintStream);
        } else if instruction.opcode == 0x5f {
            // Kotlin's inline println often evaluates its operand first. Only
            // reorder a literal or parameter, neither of which has effects.
            if let [StackValue::Value(argument), StackValue::PrintStream] = stack.as_slice()
                && matches!(argument.kind, ExprKind::Literal(_) | ExprKind::Parameter { .. })
            {
                stack.swap(0, 1);
            } else {
                return Err(invalid());
            }
        } else if let Some(("java/io/PrintStream", "println", descriptor)) = bytecode.reference(instruction, 0xb6)? {
            let expected = println_operand(descriptor).ok_or_else(invalid)?;
            let argument = if let Some(expected) = expected {
                Some((pop_value(&mut stack, declaration)?, expected))
            } else {
                None
            };
            if !matches!(stack.as_slice(), [StackValue::PrintStream]) { return Err(invalid()); }
            stack.clear();
            statements.push(Statement { instructions: first..index + 1, argument });
            first = index + 1;
        } else {
            bytecode.expression(instruction, locals, &mut stack, declaration)?;
        }
    }
    if !stack.is_empty() { return Err(KotlinError::unsupported(declaration, "live operands at Kotlin statement return")); }
    Ok(statements)
}

fn println_operand(descriptor: &str) -> Option<Option<Expected<'static>>> {
    let argument = match descriptor {
        "()V" => return Some(None),
        "(Z)V" => Expected::Primitive(Primitive::Boolean),
        "(C)V" => Expected::Primitive(Primitive::Char),
        "(I)V" => Expected::Primitive(Primitive::Int),
        "(J)V" => Expected::Primitive(Primitive::Long),
        "(F)V" => Expected::Primitive(Primitive::Float),
        "(D)V" => Expected::Primitive(Primitive::Double),
        "(Ljava/lang/String;)V" | "(Ljava/lang/Object;)V" => Expected::Reference,
        _ => return None,
    };
    Some(Some(argument))
}
