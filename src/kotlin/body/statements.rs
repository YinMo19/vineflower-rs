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
    argument: Option<(Expr<'a>, PrintOperand)>,
}

#[derive(Clone, Copy)]
enum PrintOperand {
    Primitive(Primitive),
    Object,
    String,
}

impl Statement<'_> {
    pub fn write(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
    ) -> Result<(), KotlinError> {
        out.push_str("System.out.println(");
        if let Some((expr, expected)) = &self.argument {
            let (expected, cast) = match expected {
                PrintOperand::Primitive(primitive) => (Expected::Primitive(*primitive), ""),
                PrintOperand::Object => {
                    // Kotlin println is compiled to the Object overload. Keep
                    // nontrivial reference overloads (e.g. CharArray) distinct.
                    let cast = match &expr.kind {
                        ExprKind::Literal(Literal::String(_)) => "",
                        ExprKind::Parameter { index, .. }
                            if matches!(
                                parameters[*index].ty.class_id(),
                                Some("kotlin/Any" | "kotlin/String")
                            ) =>
                        {
                            ""
                        }
                        ExprKind::LoopLocal(local)
                            if matches!(local.element, super::loops::Element::Object) =>
                        {
                            ""
                        }
                        _ => " as kotlin.Any?",
                    };
                    (Expected::Reference, cast)
                }
                PrintOperand::String => {
                    let cast = match &expr.kind {
                        ExprKind::Literal(Literal::String(_)) => "",
                        ExprKind::Literal(Literal::Null) => " as kotlin.String?",
                        ExprKind::Parameter { index, .. }
                            if parameters[*index].ty.class_id() == Some("kotlin/String") =>
                        {
                            ""
                        }
                        ExprKind::LoopLocal(local)
                            if matches!(local.element, super::loops::Element::String) =>
                        {
                            ""
                        }
                        _ => {
                            return Err(KotlinError::unsupported(
                                declaration,
                                "non-String println argument",
                            ));
                        }
                    };
                    (Expected::Reference, cast)
                }
            };
            expr.write_at(out, expected, parameters, declaration, 0)?;
            out.push_str(cast);
        }
        out.push(')');
        Ok(())
    }
}

pub(super) fn lower<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    start: usize,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    lower_range(
        bytecode,
        instructions,
        start..instructions.len() - 1,
        locals,
        declaration,
    )
}

pub(super) fn lower_range<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    lower_scoped(bytecode, instructions, range, locals, declaration, None)
}

pub(super) fn lower_scoped<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: Option<super::loops::Binding<'a>>,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let mut statements = Vec::new();
    let mut stack = Vec::new();
    let mut index = range.start;
    let mut first = index;
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin statement bytecode");
    let first_free = scoped.map_or_else(|| locals.next_slot(), |local| local.first_free);
    while index < range.end {
        let instruction = &instructions[index];
        if let Some((store, slot)) = super::local_store(instruction)
            && slot >= first_free
            && let [get, load, ..] = &instructions[index + 1..range.end]
            && super::local_load(load) == Some((store - 0x21, slot))
            && bytecode.reference(get, 0xb2)?
                == Some(("java/lang/System", "out", "Ljava/io/PrintStream;"))
            && let [StackValue::Value(argument)] = stack.as_slice()
            && argument.stack_load() == Some(store - 0x21)
            && argument.infallible()
        {
            // The inline primitive println uses a fresh temporary instead of
            // swap. Only its proven store/reload is modeled as a stack move.
            stack.insert(0, StackValue::PrintStream);
            index += 3;
            continue;
        }
        if bytecode.reference(instruction, 0xb2)?
            == Some(("java/lang/System", "out", "Ljava/io/PrintStream;"))
        {
            stack.push(StackValue::PrintStream);
        } else if instruction.opcode == 0x5f {
            // Reordering the receiver load past an infallible argument
            // preserves which operations can be observed or fail first.
            if let [StackValue::Value(argument), StackValue::PrintStream] = stack.as_slice()
                && matches!(argument.stack_load(), Some(0x15 | 0x17 | 0x19))
                && argument.infallible()
            {
                stack.swap(0, 1);
            } else {
                return Err(invalid());
            }
        } else if let Some(("java/io/PrintStream", "println", descriptor)) =
            bytecode.reference(instruction, 0xb6)?
        {
            let expected = println_operand(descriptor).ok_or_else(invalid)?;
            let argument = if let Some(expected) = expected {
                Some((pop_value(&mut stack, declaration)?, expected))
            } else {
                None
            };
            if !matches!(stack.as_slice(), [StackValue::PrintStream]) {
                return Err(invalid());
            }
            stack.clear();
            statements.push(Statement {
                instructions: first..index + 1,
                argument,
            });
            first = index + 1;
        } else {
            bytecode.expression_with_local(instruction, locals, &mut stack, declaration, scoped)?;
        }
        index += 1;
    }
    if !stack.is_empty() {
        return Err(KotlinError::unsupported(
            declaration,
            "live operands at Kotlin statement return",
        ));
    }
    Ok(statements)
}

fn println_operand(descriptor: &str) -> Option<Option<PrintOperand>> {
    let argument = match descriptor {
        "()V" => return Some(None),
        "(Z)V" => PrintOperand::Primitive(Primitive::Boolean),
        "(C)V" => PrintOperand::Primitive(Primitive::Char),
        "(I)V" => PrintOperand::Primitive(Primitive::Int),
        "(J)V" => PrintOperand::Primitive(Primitive::Long),
        "(F)V" => PrintOperand::Primitive(Primitive::Float),
        "(D)V" => PrintOperand::Primitive(Primitive::Double),
        "(Ljava/lang/String;)V" => PrintOperand::String,
        "(Ljava/lang/Object;)V" => PrintOperand::Object,
        _ => return None,
    };
    Some(Some(argument))
}
