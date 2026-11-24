// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{borrow::Cow, ops::Range, rc::Rc};

use crate::classfile::LocalVariable;

use super::{
    Bytecode, Code, Expected, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal, Locals,
    Operand, Primitive, ScopedLocal, StackValue, Type, ValueParameter, extensions::{Value, exact_type},
    identifier, invocations::{self, Call, kotlin_type}, load_opcode, local_load, local_store, logic, nullable, pop_value,
};

/// Statements and their original bytecode spans. Stack shuffles do not have
/// source expressions and are excluded by the mapping consumer.
pub(in crate::kotlin) struct StatementBlock<'a> {
    pub statements: Vec<Statement<'a>>,
    pub lines: Vec<(u16, u16)>,
    pub instructions: Vec<Instruction>,
    pub implicit_return: bool,
}

#[derive(Debug)]
pub(in crate::kotlin) struct Statement<'a> {
    pub instructions: Range<usize>,
    kind: Kind<'a>,
}

#[derive(Debug)]
enum Kind<'a> {
    Print {
        argument: Option<(Expr<'a>, PrintOperand)>,
        order: PrintOrder,
    },
    Declare(Rc<Binding<'a>>, Expr<'a>),
    Increment(Rc<Binding<'a>>, i16),
    Evaluate(Box<Call<'a>>),
    EvaluateNullable(Box<nullable::Expression<'a>>),
    Return(Expr<'a>, Value),
    AssignField(Box<super::lambdas::Field<'a>>, Expr<'a>),
}

#[derive(Debug)]
pub(super) struct Binding<'a> {
    pub(super) name: Cow<'a, str>,
    pub(super) value: Value,
    slot: u16,
    range: Range<u32>,
    pub(super) mutable: bool,
}

pub(super) struct ConditionalInitializer<'a> {
    pub(super) instructions: Range<usize>,
    /// The store that starts the LVT range, including a dead initial store
    /// before a closed conditional whose two arms both overwrite it.
    pub(super) store: usize,
    pub(super) condition: Expr<'a>,
    pub(super) yes: Expr<'a>,
    pub(super) no: Expr<'a>,
}

enum Initial<'a, 'scope> {
    Stack(usize, Expr<'a>),
    Declaration(Statement<'a>),
    Scope(&'scope [Statement<'a>]),
}

#[derive(Default)]
struct DebugLocals<'a> {
    entries: Vec<LocalVariable<'a>>,
    max: u16,
}

#[derive(Clone, Copy, Debug)]
enum PrintOperand {
    Primitive(Primitive),
    Object,
    String,
}

#[derive(Clone, Copy, Debug)]
enum PrintOrder {
    ReceiverFirst,
    ArgumentFirst,
    ArgumentFirstRequired,
}

impl PrintOrder {
    fn argument_first(argument: &Expr<'_>) -> Self {
        if argument.infallible() { Self::ArgumentFirst } else { Self::ArgumentFirstRequired }
    }
}

#[derive(Debug)]
pub(super) struct ValueBlock<'a> {
    pub(super) statements: Vec<Statement<'a>>,
    pub(super) value: Expr<'a>,
}

impl ValueBlock<'_> {
    pub(super) fn write(
        &self, out: &mut String, expected: Expected<'_>, parameters: &[ValueParameter], declaration: &str,
    ) -> Result<(), KotlinError> {
        out.push_str("kotlin.run { ");
        for statement in &self.statements {
            statement.write(out, parameters, declaration)?;
            out.push_str("; ");
        }
        self.value.write_at(out, expected, parameters, declaration, 0)?;
        out.push_str(" }");
        Ok(())
    }
}

impl<'a> Statement<'a> {
    pub(super) fn bind_suspending_call(
        name: &'a str, slot: u16, range: Range<u32>, instructions: Range<usize>, call: Call<'a>,
    ) -> (Self, Expr<'a>) {
        let result = call.result();
        let value = Value { ty: result.ty.clone(), jvm: result.jvm.clone() };
        let local = Rc::new(Binding { name: Cow::Borrowed(name), slot, range, value, mutable: false });
        let binding = Self {
            instructions,
            kind: Kind::Declare(
                Rc::clone(&local), Expr { kind: ExprKind::Invocation(Box::new(call)), depth: 1 },
            ),
        };
        (binding, Expr { kind: ExprKind::Local(local), depth: 1 })
    }

    pub(super) fn evaluate(call: Call<'a>, instructions: Range<usize>) -> Self {
        Self { instructions, kind: Kind::Evaluate(Box::new(call)) }
    }

    pub(super) fn returning(value: TailValue<'a>, ty: &Type, jvm: &JvmType) -> Self {
        Self {
            instructions: value.instructions,
            kind: Kind::Return(value.expr, Value { ty: ty.clone(), jvm: jvm.clone() }),
        }
    }
}

impl Statement<'_> {
    pub fn write(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
    ) -> Result<(), KotlinError> {
        self.write_with_print_overload(out, parameters, declaration, false)
    }

    pub(super) fn write_exact_print(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
    ) -> Result<(), KotlinError> {
        self.write_with_print_overload(out, parameters, declaration, true)
    }

    fn write_with_print_overload(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
        exact_print_overload: bool,
    ) -> Result<(), KotlinError> {
        // Java PrintStream chooses a different overload for String, CharArray,
        // and other arguments that Kotlin's inline println sends as Object.
        // Keep the proven overload when embedding a recovered closure.
        // Other statement emission keeps its existing source formatting.
        let (argument, order) = match &self.kind {
            Kind::Print { argument, order } => (argument, *order),
            Kind::Declare(local, value) => {
                out.push_str(if local.mutable { "var " } else { "val " });
                identifier(out, &local.name, declaration)?;
                // Without an expected type Kotlin gives small numeric
                // literals type Int, even when JVM iload read a Byte/Short.
                match local.value.jvm {
                    JvmType::Primitive(Primitive::Byte) => out.push_str(": kotlin.Byte"),
                    JvmType::Primitive(Primitive::Short) => out.push_str(": kotlin.Short"),
                    _ => {}
                }
                out.push_str(" = ");
                return value.write(out, &local.value.ty, &local.value.jvm, parameters, declaration);
            }
            Kind::Increment(local, amount) => {
                use std::fmt::Write;
                identifier(out, &local.name, declaration)?;
                match amount {
                    1 => out.push_str("++"),
                    -1 => out.push_str("--"),
                    _ => write!(out, " += {amount}").unwrap(),
                }
                return Ok(());
            }
            Kind::Evaluate(call) => return call.write(out, parameters, declaration),
            Kind::EvaluateNullable(expression) => {
                let result = expression.result();
                return expression.write(
                    out, Expected::Type(&result.ty, &result.jvm), parameters, declaration, 0,
                );
            }
            Kind::Return(value, result) => {
                out.push_str("return ");
                return value.write(out, &result.ty, &result.jvm, parameters, declaration);
            }
            Kind::AssignField(field, value) => return field.assignment(out, value, parameters, declaration),
        };
        let argument_first = matches!(order, PrintOrder::ArgumentFirstRequired)
            || exact_print_overload && matches!(order, PrintOrder::ArgumentFirst);
        if argument_first && matches!(argument, Some((_, PrintOperand::String))) {
            return Err(KotlinError::unsupported(declaration, "argument-first String println"));
        }
        out.push_str(if argument_first { "kotlin.io.println(" } else { "System.out.println(" });
        if let Some((expr, expected)) = argument {
            let (expected, cast) = match expected {
                PrintOperand::Primitive(primitive) => (Expected::Primitive(*primitive), ""),
                PrintOperand::Object if exact_print_overload && !argument_first => {
                    (Expected::Reference, " as kotlin.Any?")
                }
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
            if exact_print_overload && !cast.is_empty() {
                out.push('(');
                expr.write_at(out, expected, parameters, declaration, 0)?;
                out.push(')');
            } else {
                expr.write_at(out, expected, parameters, declaration, 0)?;
            }
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
        let nullable = matches!(
            self.kind,
            Kind::EvaluateNullable(_)
                | Kind::Declare(_, Expr { kind: ExprKind::Nullable(_), .. })
                | Kind::Return(Expr { kind: ExprKind::Nullable(_), .. }, _)
        );
        let mut instructions = instructions[self.instructions.clone()]
            .iter()
            .filter(|instruction| !matches!(instruction.opcode, 0x00 | 0x5f)
                && (!nullable || !nullable::elided_trace(instruction)))
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
    lower_debug_range(bytecode, instructions, start..instructions.len() - 1, code, locals, declaration)
}

pub(super) fn lower_debug_range<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: &[Instruction],
    range: Range<usize>,
    code: &Code<'data>,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let debug = if instructions[range.clone()].iter().any(|instruction| local_store(instruction).is_some()) {
        DebugLocals { entries: code.local_variables(&bytecode.class.pool)?, max: code.max_locals }
    } else {
        DebugLocals::default()
    };
    let (statements, value) = lower_block(bytecode, instructions, range, locals, declaration, &[], &debug, None)?;
    closed(statements, value, declaration)
}

pub(super) fn lower_nullable<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: &[Instruction],
    start: usize,
    join: usize,
    code: &Code<'data>,
    locals: &Locals<'_>,
    expression: Expr<'a>,
    returning: (&Type, &JvmType),
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let last = instructions.len() - 1;
    let (ty, jvm) = returning;
    let invalid = || KotlinError::unsupported(declaration, "unproven Kotlin nullable continuation");
    if instructions[last].opcode != super::return_opcode(jvm) {
        return Err(invalid());
    }
    if join == last {
        return if *jvm == JvmType::Void {
            let ExprKind::Nullable(expression) = expression.kind else { return Err(invalid()); };
            Ok(vec![Statement { instructions: start..join, kind: Kind::EvaluateNullable(expression) }])
        } else {
            Ok(vec![Statement {
                instructions: start..last + 1,
                kind: Kind::Return(expression, Value { ty: ty.clone(), jvm: jvm.clone() }),
            }])
        };
    }
    let debug = DebugLocals {
        entries: code.local_variables(&bytecode.class.pool)?,
        max: code.max_locals,
    };
    let (mut statements, value) = lower_block(
        bytecode, instructions, start..last, locals, declaration, &[], &debug,
        Some(Initial::Stack(join, expression)),
    )?;
    if !matches!(statements.first(), Some(Statement { kind: Kind::Declare(_, _), instructions }) if instructions.end == join + 1) {
        return Err(invalid());
    }
    if *jvm == JvmType::Void {
        return closed(statements, value, declaration);
    }
    let value = value.filter(|tail| tail.expr.stack_load() == Some(load_opcode(jvm))).ok_or_else(invalid)?;
    statements.push(Statement {
        instructions: value.instructions.start..last + 1,
        kind: Kind::Return(value.expr, Value { ty: ty.clone(), jvm: jvm.clone() }),
    });
    Ok(statements)
}

pub(super) fn lower_conditional_initializer<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: &[Instruction],
    code: &Code<'data>,
    locals: &Locals<'_>,
    init: ConditionalInitializer<'a>,
    declaration: &str,
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "unsupported conditional local initializer");
    let ConditionalInitializer { instructions: span, store, condition, yes, no } = init;
    let site = &instructions[store];
    let (opcode, slot) = local_store(site).filter(|&(_, slot)| slot >= locals.next_slot())
        .ok_or_else(invalid)?;
    let after = site.offset + site.len;
    let debug = DebugLocals { entries: code.local_variables(&bytecode.class.pool)?, max: code.max_locals };
    let mut entries = debug.entries.iter().filter(|local| local.index == slot && u32::from(local.start_pc) == after);
    let local = entries.next().filter(|_| entries.next().is_none()).ok_or_else(invalid)?;
    let jvm = JvmType::parse(local.descriptor)?;
    let yes_type = debug_value_type(&yes, &jvm, locals).ok_or_else(invalid)?;
    if debug_value_type(&no, &jvm, locals).as_ref() != Some(&yes_type) {
        return Err(invalid());
    }
    let value = Value { ty: yes_type, jvm };
    let binding = debug_binding(bytecode.owner, local, instructions, &debug, &[], locals, value, opcode, declaration)?;
    let expression = logic::Conditional::new(condition, yes, no, declaration)?;
    let start = span.start;
    let seed = Statement { instructions: span, kind: Kind::Declare(binding, expression) };
    let last = instructions.len() - 1;
    let (statements, value) = lower_block(
        bytecode, instructions, start..last, locals, declaration, &[], &debug,
        Some(Initial::Declaration(seed)),
    )?;
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

pub(super) fn lower_inherited<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    inherited: &[Statement<'a>],
) -> Result<Vec<Statement<'a>>, KotlinError> {
    let (statements, value) = lower_block(
        bytecode, instructions, range, locals, declaration, &[], &DebugLocals::default(),
        Some(Initial::Scope(inherited)),
    )?;
    closed(statements, value, declaration)
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
    lower_block(bytecode, instructions, range, locals, declaration, scoped, &DebugLocals::default(), None)
}

pub(super) struct Prefix<'a> {
    pub(super) statements: Vec<Statement<'a>>,
    pub(super) stack: Vec<StackValue<'a>>,
    pub(super) first: usize,
}

pub(super) fn lower_prefix<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: &[Instruction],
    range: Range<usize>,
    code: &Code<'data>,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<Prefix<'a>, KotlinError> {
    let debug = DebugLocals { entries: code.local_variables(&bytecode.class.pool)?, max: code.max_locals };
    lower_operands(bytecode, instructions, range, locals, declaration, &[], &debug, None)
}

impl<'a> Statement<'a> {
    fn binding(&self) -> Option<&Rc<Binding<'a>>> {
        match &self.kind {
            Kind::Declare(local, _) => Some(local),
            _ => None,
        }
    }
}

pub(super) fn read_local<'a, 'scope>(
    statements: impl Iterator<Item = &'scope Statement<'a>>,
    instruction: &Instruction,
) -> Result<Option<Expr<'a>>, ()>
where 'a: 'scope {
    let Some((load, slot)) = local_load(instruction) else { return Ok(None); };
    let Some(local) = live_local(statements, instruction.offset, slot) else { return Ok(None); };
    if load != load_opcode(&local.value.jvm) {
        return Err(());
    }
    Ok(Some(Expr { kind: ExprKind::Local(Rc::clone(local)), depth: 1 }))
}

fn live_local<'a, 'scope>(
    statements: impl Iterator<Item = &'scope Statement<'a>>,
    offset: u32,
    slot: u16,
) -> Option<&'scope Rc<Binding<'a>>>
where 'a: 'scope {
    statements.filter_map(Statement::binding).find(|local| local.slot == slot && local.range.contains(&offset))
}

fn lower_block<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: &[ScopedLocal<'a>],
    debug: &DebugLocals<'a>,
    initial: Option<Initial<'a, '_>>,
) -> Result<(Vec<Statement<'a>>, Option<TailValue<'a>>), KotlinError> {
    let Prefix { statements, mut stack, first } = lower_operands(
        bytecode, instructions, range.clone(), locals, declaration, scoped, debug, initial,
    )?;
    let value = if stack.is_empty() {
        None
    } else if let [StackValue::Value(_)] = stack.as_slice() {
        Some(TailValue { expr: pop_value(&mut stack, declaration)?, instructions: first..range.end })
    } else {
        return Err(KotlinError::unsupported(declaration, "unsupported Kotlin statement bytecode"));
    };
    Ok((statements, value))
}

fn lower_operands<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    range: Range<usize>,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: &[ScopedLocal<'a>],
    debug: &DebugLocals<'a>,
    initial: Option<Initial<'a, '_>>,
) -> Result<Prefix<'a>, KotlinError> {
    let mut statements = Vec::new();
    let mut stack = Vec::new();
    let mut print_order = PrintOrder::ReceiverFirst;
    let mut index = range.start;
    let mut first = range.start;
    let mut inherited = &[][..];
    match initial {
        Some(Initial::Stack(join, value)) => {
            index = join;
            stack.push(StackValue::Value(value));
        }
        Some(Initial::Declaration(statement)) => {
            index = statement.instructions.end;
            first = index;
            statements.push(statement);
        }
        Some(Initial::Scope(scope)) => inherited = scope,
        None => {}
    }
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin statement bytecode");
    let first_free = scoped.iter().map(|local| local.first_free())
        .fold(locals.next_slot(), u16::max);
    while index < range.end {
        let instruction = &instructions[index];
        let scope = || statements.iter().rev().chain(inherited.iter().rev());
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
                let jvm = JvmType::parse(local.descriptor)?;
                let ty = debug_value_type(&value, &jvm, locals)
                    .ok_or_else(|| KotlinError::unsupported(declaration, "unproven Kotlin debug local"))?;
                let binding = debug_binding(
                    bytecode.owner, local, instructions, debug, &statements, locals, Value { ty, jvm }, store, declaration,
                )?;
                statements.push(Statement { instructions: first..index + 1, kind: Kind::Declare(binding, value) });
                first = index + 1;
                index += 1;
                continue;
            }
            if let Some((written, _)) = instruction.local_access()
                && scope().filter_map(Statement::binding).any(|local| {
                    let start = u32::from(local.slot);
                    local.range.contains(&instruction.offset)
                        && start < written.end && written.start < start + u32::from(local.value.jvm.slots())
                })
            {
                return Err(invalid());
            }
            if locals.closure_body
                && let [StackValue::Value(value)] = stack.as_slice()
                && let Some((ty, jvm)) = value.source_type(locals)
                && load_opcode(jvm) + 0x21 == store
                && let Some((written, _)) = instruction.local_access()
                && written.end <= u32::from(debug.max)
            {
                let end = instructions[index + 1..range.end].iter().find(|next| {
                    next.local_access().is_some_and(|(slots, read)| {
                        (!read || next.opcode == 0x84) && written.start < slots.end && slots.start < written.end
                    })
                }).map_or_else(|| instructions[range.end - 1].offset + instructions[range.end - 1].len, |next| next.offset);
                if !debug.entries.iter().any(|local| {
                    let start = u32::from(local.start_pc);
                    let width = if matches!(local.descriptor, "J" | "D") { 2 } else { 1 };
                    after < start + u32::from(local.length) && start < end
                        && written.start < u32::from(local.index) + width && u32::from(local.index) < written.end
                }) {
                    let local = Rc::new(Binding {
                        name: Cow::Owned(format!("lambdaLocal{slot}_{}", instruction.offset)),
                        slot, range: after..end, mutable: false, value: Value { ty: ty.clone(), jvm: jvm.clone() },
                    });
                    let value = pop_value(&mut stack, declaration)?;
                    statements.push(Statement { instructions: first..index + 1, kind: Kind::Declare(local, value) });
                    first = index + 1;
                    index += 1;
                    continue;
                }
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
                print_order = PrintOrder::argument_first(argument);
                stack.insert(0, StackValue::PrintStream);
                index += 3;
                continue;
            }
            return Err(invalid());
        }
        if let Operand::Increment { index: slot, amount } = instruction.operand {
            let local = live_local(scope(), instruction.offset, slot).filter(|local| local.mutable).ok_or_else(invalid)?;
            // A deferred stack expression could read the old value, or
            // throw before the increment. Emit only at a statement boundary.
            if !stack.is_empty() {
                return Err(invalid());
            }
            statements.push(Statement {
                instructions: first..index + 1,
                kind: Kind::Increment(Rc::clone(local), amount),
            });
            first = index + 1;
            index += 1;
            continue;
        }
        if let Some(expr) = read_local(scope(), instruction).map_err(|_| invalid())? {
            stack.push(StackValue::Value(expr));
            index += 1;
            continue;
        }
        if instruction.opcode == 0xbd {
            let Some(StackValue::Value(Expr { kind: ExprKind::Literal(Literal::Int(length)), .. })) = stack.last()
                else { return Err(invalid()); };
            let (pack, consumed, scratch) = invocations::packed(
                bytecode, &instructions[index..range.end], *length,
                |instruction, stack| {
                    if let Some(value) = read_local(scope(), instruction).map_err(|_| invalid())? {
                        stack.push(StackValue::Value(value));
                        Ok(())
                    } else {
                        bytecode.expression_with_locals(instruction, locals, stack, declaration, scoped)
                    }
                },
                declaration,
            )?;
            if let Some(slot) = scratch {
                let begin = instruction.offset;
                let last = &instructions[index + consumed - 1];
                let end = last.offset + last.len;
                let overlaps = |local_slot: u16, width: u16, from: u32, to: u32| {
                    local_slot <= slot && u32::from(slot) < u32::from(local_slot) + u32::from(width)
                        && begin < to && from < end
                };
                if slot < first_free || (debug.max != 0 && slot >= debug.max)
                    || scope().filter_map(Statement::binding).any(|local|
                        overlaps(local.slot, local.value.jvm.slots(), local.range.start, local.range.end))
                    || debug.entries.iter().any(|local| {
                        let from = u32::from(local.start_pc);
                        let width = if matches!(local.descriptor, "J" | "D") { 2 } else { 1 };
                        overlaps(local.index, width, from, from + u32::from(local.length))
                    })
                {
                    return Err(invalid());
                }
            }
            stack.truncate(stack.len() - 1);
            stack.push(StackValue::Vararg(pack));
            index += consumed;
            continue;
        }
        if let Some(spread) = invocations::spread(bytecode, &instructions[index..range.end], locals)? {
            stack.push(StackValue::Vararg(spread));
            index += 5;
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
                print_order = PrintOrder::argument_first(argument);
                stack.swap(0, 1);
            } else {
                return Err(invalid());
            }
        } else if let Some(("java/io/PrintStream", "println", descriptor)) =
            bytecode.reference(instruction, 0xb6)?
        {
            let expected = println_operand(descriptor).ok_or_else(invalid)?;
            if matches!(print_order, PrintOrder::ArgumentFirstRequired)
                && (matches!(expected, None | Some(PrintOperand::String))
                    || locals.templates.properties.iter().any(|property| property.name == "kotlin")
                    || locals.extension.as_ref().is_some_and(|context| {
                        context.parameters.iter().any(|param| param.name == "kotlin")
                    }))
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
                kind: Kind::Print { argument, order: print_order },
            });
            print_order = PrintOrder::ReceiverFirst;
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
        } else if let Some((field, value)) = super::lambdas::store(bytecode, instruction, locals, &mut stack, declaration)? {
            statements.push(Statement { instructions: first..index + 1, kind: Kind::AssignField(Box::new(field), value) });
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
    Ok(Prefix { statements, stack, first })
}

fn debug_binding<'a>(
    owner: &str,
    local: &LocalVariable<'a>,
    instructions: &[Instruction],
    debug: &DebugLocals<'a>,
    declared: &[Statement<'a>],
    locals: &Locals<'_>,
    value: Value,
    store: u8,
    declaration: &str,
) -> Result<Rc<Binding<'a>>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "unproven Kotlin debug local");
    let jvm = &value.jvm;
    let start = u32::from(local.start_pc);
    let range = start..start + u32::from(local.length);
    let root = owner.split(['/', '$']).next().unwrap();
    let short = owner.rsplit('/').next().unwrap();
    if *jvm == JvmType::Void || !exact_type(&value.ty, jvm, false)
        || load_opcode(jvm) + 0x21 != store
        || local.index.checked_add(jvm.slots()).is_none_or(|end| end > debug.max)
        || range.is_empty() || range.end > instructions.last().map_or(0, |last| last.offset + last.len)
        || (range.end <= instructions.last().map_or(0, |last| last.offset)
            && instructions.binary_search_by_key(&range.end, |instruction| instruction.offset).is_err())
        || matches!(local.name, "System" | "kotlin") || local.name == root || local.name == short
        || locals.closure_body && super::lambdas::reserved(local.name)
        || declared.iter().filter_map(Statement::binding).any(|other| other.name == local.name)
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
    let tail = &instructions[instructions.binary_search_by_key(&start, |instruction| instruction.offset).map_err(|_| invalid())?..];
    let mut name = Cow::Borrowed(local.name);
    if locals.captures.is_some() {
        name = Cow::Owned(format!("lambdaLocal{}_{}", local.index, start));
    }
    if let Some(context) = &locals.extension
        && let Some(parameter) = context.parameters.iter().position(|param| param.name == local.name)
        && tail.iter().any(|instruction| {
            local_load(instruction).is_some_and(|(load, slot)| locals.parameter(slot, load) == Some(parameter))
        })
    {
        // The JVM can still name the original parameter from its own slot,
        // unlike source code with two live bindings sharing one identifier.
        let reserved = |candidate: &str| {
            candidate == root || candidate == short
                || debug.entries.iter().any(|entry| entry.name == candidate)
                || context.parameters.iter().any(|param| param.name == candidate)
                || declared.iter().filter_map(Statement::binding).any(|other| other.name == candidate)
        };
        name = (1..=u32::MAX).map(|suffix| format!("{}_{suffix}", local.name))
            .find(|candidate| !reserved(candidate))
            .map(Cow::Owned)
            .ok_or_else(invalid)?;
    }
    let mutable = *jvm == JvmType::Primitive(Primitive::Int)
        && tail.iter().take_while(|instruction| range.contains(&instruction.offset)).any(|instruction| {
            matches!(instruction.operand, Operand::Increment { index, .. } if index == local.index)
        });
    Ok(Rc::new(Binding { name, value, slot: local.index, range, mutable }))
}

fn debug_value_type(value: &Expr<'_>, jvm: &JvmType, locals: &Locals<'_>) -> Option<Type> {
    if let Some((ty, actual)) = value.source_type(locals) {
        return (actual == jvm).then(|| ty.clone());
    }
    use JvmType::Primitive as Jvm;
    use Literal::*;
    let ExprKind::Literal(literal) = &value.kind else { return None };
    let id = match (literal, jvm) {
        (String(_), JvmType::Object(name)) if name == "java/lang/String" => "kotlin/String",
        (Int(0 | 1), Jvm(Primitive::Boolean)) => "kotlin/Boolean",
        (Int(number), Jvm(Primitive::Byte)) if i8::try_from(*number).is_ok() => "kotlin/Byte",
        (Int(number), Jvm(Primitive::Short)) if i16::try_from(*number).is_ok() => "kotlin/Short",
        (Int(number), Jvm(Primitive::Char)) if u16::try_from(*number).is_ok() => "kotlin/Char",
        (Int(_), Jvm(Primitive::Int)) => "kotlin/Int",
        (Long(_), Jvm(Primitive::Long)) => "kotlin/Long",
        (Float(_), Jvm(Primitive::Float)) => "kotlin/Float",
        (Double(_), Jvm(Primitive::Double)) => "kotlin/Double",
        _ => return None,
    };
    Some(kotlin_type(id))
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
