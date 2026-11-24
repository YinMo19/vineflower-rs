// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{ops::Range, rc::Rc};

use crate::classfile::LocalVariable;

use super::{
    Bytecode, Code, Expected, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal, Locals,
    Primitive, ScopedLocal, StackValue, ValueParameter, extensions::{Value, exact_type}, identifier,
    invocations::Call, load_opcode, local_load, local_store, pop_value,
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
    kind: Kind<'a>,
}

enum Kind<'a> {
    Print {
        argument: Option<(Expr<'a>, PrintOperand)>,
        argument_first: bool,
    },
    Declare(Rc<Binding<'a>>, Expr<'a>),
    Evaluate(Box<Call<'a>>),
}

#[derive(Debug)]
pub(super) struct Binding<'a> {
    pub(super) name: &'a str,
    pub(super) value: Value,
    slot: u16,
    range: Range<u32>,
}

#[derive(Default)]
struct DebugLocals<'a> {
    entries: Vec<LocalVariable<'a>>,
    max: u16,
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
        let (argument, argument_first) = match &self.kind {
            Kind::Print { argument, argument_first } => (argument, *argument_first),
            Kind::Declare(local, value) => {
                out.push_str("val ");
                identifier(out, local.name, declaration)?;
                out.push_str(" = ");
                return value.write(out, &local.value.ty, &local.value.jvm, parameters, declaration);
            }
            Kind::Evaluate(call) => return call.write(out, parameters, declaration),
        };
        out.push_str(if argument_first { "kotlin.io.println(" } else { "System.out.println(" });
        if let Some((expr, expected)) = argument {
            let (expected, cast) = match expected {
                PrintOperand::Primitive(primitive) => (Expected::Primitive(*primitive), ""),
                PrintOperand::Object => {
                    // Kotlin println is compiled to the Object overload. Keep
                    // nontrivial reference overloads (e.g. CharArray) distinct.
                    let cast = match &expr.kind {
                        ExprKind::Literal(Literal::String(_)) | ExprKind::Template(_) => "",
                        ExprKind::Invocation(call) if argument_first
                            && call.result().ty.class_id() == Some("kotlin/String") => "",
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
                        ExprKind::CatchLocal(_) => "",
                        _ => " as kotlin.Any?",
                    };
                    (Expected::Reference, cast)
                }
                PrintOperand::String => {
                    let cast = match &expr.kind {
                        ExprKind::Literal(Literal::String(_)) | ExprKind::Template(_) => "",
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
                        ExprKind::CatchMessage(_) => "",
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

    pub fn trace(
        &self,
        bytecode: &Bytecode<'_, '_>,
        instructions: &[Instruction],
        mut visit: impl FnMut(&Instruction),
    ) -> Result<(), KotlinError> {
        let mut instructions = instructions[self.instructions.clone()]
            .iter()
            .filter(|instruction| !matches!(instruction.opcode, 0x00 | 0x5f))
            .peekable();
        while let Some(instruction) = instructions.next() {
            if !super::templates::elided_trace(bytecode, instruction, instructions.peek().copied())? {
                visit(instruction);
            }
        }
        Ok(())
    }
}

pub(super) fn lower<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: &[Instruction],
    start: usize,
    code: &Code<'data>,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let range = start..instructions.len() - 1;
    let debug = if instructions[range.clone()].iter().any(|instruction| local_store(instruction).is_some()) {
        DebugLocals { entries: code.local_variables(&bytecode.class.pool)?, max: code.max_locals }
    } else {
        DebugLocals::default()
    };
    let (statements, value) = lower_block(bytecode, instructions, range, locals, declaration, &[], &debug)?;
    closed(statements, value, declaration)
}

pub(super) fn lower_range<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    lower_scoped(bytecode, instructions, range, locals, declaration, &[])
}

pub(super) fn lower_scoped<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: &[ScopedLocal<'a>],
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let (statements, value) = lower_open(bytecode, instructions, range, locals, declaration, scoped)?;
    closed(statements, value, declaration)
}

fn closed<'a>(
    statements: Vec<Statement<'a>>,
    value: Option<TailValue<'a>>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    if value.is_some() {
        return Err(KotlinError::unsupported(
            declaration,
            "live operands at Kotlin statement return",
        ));
    }
    Ok(statements)
}

pub(super) struct TailValue<'a> {
    pub expr: Expr<'a>,
    pub instructions: Range<usize>,
}

/// A straight block has either no result or one stack value after the
/// final statement. The caller proves how its region consumes that value.
pub(super) fn lower_open<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: &[ScopedLocal<'a>],
) -> Result<(Vec<Statement<'a>>, Option<TailValue<'a>>), KotlinError> {
    lower_block(bytecode, instructions, range, locals, declaration, scoped, &DebugLocals::default())
}

fn lower_block<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: &[ScopedLocal<'a>],
    debug: &DebugLocals<'a>,
) -> Result<(Vec<Statement<'a>>, Option<TailValue<'a>>), KotlinError> {
    let mut statements = Vec::new();
    let mut stack = Vec::new();
    let mut declared: Vec<Rc<Binding<'a>>> = Vec::new();
    let mut argument_first = false;
    let mut index = range.start;
    let mut first = index;
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin statement bytecode");
    let first_free = scoped.iter().map(|local| local.first_free())
        .fold(locals.next_slot(), u16::max);
    while index < range.end {
        let instruction = &instructions[index];
        if let Some((store, slot)) = local_store(instruction) {
            let after = instruction.offset + instruction.len;
            if slot < first_free {
                return Err(invalid());
            }
            let mut starts = debug.entries.iter().filter(|local| local.index == slot && u32::from(local.start_pc) == after);
            if let Some(local) = starts.next() {
                if starts.next().is_some() || !matches!(stack.as_slice(), [StackValue::Value(_)]) {
                    return Err(invalid());
                }
                let value = pop_value(&mut stack, declaration)?;
                let binding = debug_binding(bytecode.owner, local, instructions, debug, &declared, locals, &value, store, declaration)?;
                declared.push(Rc::clone(&binding));
                statements.push(Statement { instructions: first..index + 1, kind: Kind::Declare(binding, value) });
                first = index + 1;
                index += 1;
                continue;
            }
            if let [get, load, print, ..] = &instructions[index + 1..range.end]
                && local_load(load) == Some((store - 0x21, slot))
                && bytecode.reference(get, 0xb2)? == Some(("java/lang/System", "out", "Ljava/io/PrintStream;"))
                && matches!(bytecode.reference(print, 0xb6)?, Some(("java/io/PrintStream", "println", _)))
                && let [StackValue::Value(argument)] = stack.as_slice()
                && argument.stack_load() == Some(store - 0x21)
                && !debug.entries.iter().any(|local| local.index == slot
                    && u32::from(local.start_pc) <= load.offset
                    && instruction.offset < u32::from(local.start_pc) + u32::from(local.length))
            {
                // For a fallible value, use Kotlin's inline println, whose
                // PrintStream read must stay after the argument evaluation.
                argument_first = !argument.infallible();
                stack.insert(0, StackValue::PrintStream);
                index += 3;
                continue;
            }
            return Err(invalid());
        }
        if let Some((load, slot)) = local_load(instruction)
            && let Some(local) = declared.iter().rev().find(|local| local.slot == slot && local.range.contains(&instruction.offset))
        {
            if load != load_opcode(&local.value.jvm) {
                return Err(invalid());
            }
            stack.push(StackValue::Value(Expr { kind: ExprKind::Local(Rc::clone(local)), depth: 1 }));
            index += 1;
            continue;
        }
        if bytecode.reference(instruction, 0xb2)?
            == Some(("java/lang/System", "out", "Ljava/io/PrintStream;"))
        {
            stack.push(StackValue::PrintStream);
        } else if instruction.opcode == 0x5f {
            // Keep an effectful argument before the receiver read.
            if let [StackValue::Value(argument), StackValue::PrintStream] = stack.as_slice()
                && matches!(argument.stack_load(), Some(0x15 | 0x17 | 0x19))
            {
                argument_first = !argument.infallible();
                stack.swap(0, 1);
            } else {
                return Err(invalid());
            }
        } else if let Some(("java/io/PrintStream", "println", descriptor)) =
            bytecode.reference(instruction, 0xb6)?
        {
            let expected = println_operand(descriptor).ok_or_else(invalid)?;
            if argument_first
                && (matches!(expected, None | Some(PrintOperand::String))
                    || locals.templates.properties.iter().any(|property| property.name == "kotlin")
                    || locals.extension.as_ref().is_some_and(|context| {
                        context.parameters.iter().any(|param| param.name == "kotlin")
                    })
                    || declared.iter().any(|local| local.name == "kotlin"))
            {
                return Err(invalid());
            }
            let argument = if let Some(expected) = expected {
                let argument = pop_value(&mut stack, declaration)?;
                if argument.stack_load() != Some(expected.load()) {
                    return Err(invalid());
                }
                Some((argument, expected))
            } else {
                None
            };
            if !matches!(stack.as_slice(), [StackValue::PrintStream]) {
                return Err(invalid());
            }
            stack.clear();
            statements.push(Statement {
                instructions: first..index + 1,
                kind: Kind::Print { argument, argument_first },
            });
            argument_first = false;
            first = index + 1;
        } else if matches!(instruction.opcode, 0x57 | 0x58) {
            let ExprKind::Invocation(call) = pop_value(&mut stack, declaration)?.kind else {
                return Err(invalid());
            };
            if !stack.is_empty() || call.result().jvm.slots() != u16::from(instruction.opcode - 0x56) {
                return Err(invalid());
            }
            statements.push(Statement { instructions: first..index + 1, kind: Kind::Evaluate(call) });
            first = index + 1;
        } else {
            bytecode.expression_with_locals(instruction, locals, &mut stack, declaration, scoped)?;
            if matches!(stack.as_slice(), [StackValue::UnitCall(_)]) {
                let Some(StackValue::UnitCall(call)) = stack.pop() else { unreachable!() };
                statements.push(Statement { instructions: first..index + 1, kind: Kind::Evaluate(call) });
                first = index + 1;
            }
        }
        index += 1;
    }
    let value = if stack.is_empty() {
        None
    } else if let [StackValue::Value(_)] = stack.as_slice() {
        Some(TailValue { expr: pop_value(&mut stack, declaration)?, instructions: first..range.end })
    } else {
        return Err(invalid());
    };
    Ok((statements, value))
}

fn debug_binding<'a>(
    owner: &str,
    local: &LocalVariable<'a>,
    instructions: &[Instruction],
    debug: &DebugLocals<'a>,
    declared: &[Rc<Binding<'a>>],
    locals: &Locals<'_>,
    value: &Expr<'_>,
    store: u8,
    declaration: &str,
) -> Result<Rc<Binding<'a>>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "unproven Kotlin debug local");
    let jvm = JvmType::parse(local.descriptor)?;
    let (ty, source_jvm) = value.source_type(locals).ok_or_else(invalid)?;
    let start = u32::from(local.start_pc);
    let range = start..start + u32::from(local.length);
    let root = owner.split(['/', '$']).next().unwrap();
    let short = owner.rsplit('/').next().unwrap();
    if &jvm != source_jvm || jvm == JvmType::Void || !exact_type(ty, &jvm, false)
        || load_opcode(&jvm) + 0x21 != store
        || local.index.checked_add(jvm.slots()).is_none_or(|end| end > debug.max)
        || range.is_empty() || range.end > instructions.last().map_or(0, |last| last.offset + last.len)
        || (range.end <= instructions.last().map_or(0, |last| last.offset)
            && instructions.binary_search_by_key(&range.end, |instruction| instruction.offset).is_err())
        || matches!(local.name, "System" | "kotlin") || local.name == root || local.name == short
        || declared.iter().any(|other| other.name == local.name)
        || locals.extension.as_ref().is_some_and(|context| {
            context.parameters.iter().any(|param| param.name == local.name)
        })
    {
        return Err(invalid());
    }
    for other in &debug.entries {
        let other_start = u32::from(other.start_pc);
        if !std::ptr::eq(other, local) && range.start < other_start + u32::from(other.length)
            && other_start < range.end && other.index < local.index + jvm.slots()
            && u32::from(local.index) < u32::from(other.index) + u32::from(JvmType::parse(other.descriptor)?.slots())
        {
            return Err(invalid());
        }
    }
    Ok(Rc::new(Binding { name: local.name, value: Value { ty: ty.clone(), jvm }, slot: local.index, range }))
}

impl PrintOperand {
    fn load(self) -> u8 {
        match self {
            Self::Primitive(primitive) => load_opcode(&JvmType::Primitive(primitive)),
            Self::Object | Self::String => 0x19,
        }
    }
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
