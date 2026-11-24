// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Recover named Kotlin/JVM suspend functions without treating a suspension
//! return as a source-level exit. Both the immediate and resumed paths must
//! deliver the same value with the same exception-handler priority.

use crate::{
    context::{ClassGroup, NestedKind},
    kotlin::{Declaration, PackageDeclaration, model::CONTINUATION, read_metadata},
};

use super::{
    Body, Bytecode, Code, Constant, Expr, ExprKind, FINAL, Function, Instruction, JvmType,
    KotlinError, Locals, Member, Operand, Primitive, STATIC, StackValue, Type, bytecode,
    extensions::exact_type, invocations::Call, local_load, local_store, logic, pop_value,
    statements::{self, Statement, StatementBlock, TailValue},
    suspend::{COROUTINE_MARKER, THROW_ON_FAILURE, aload, class_operand},
    try_regions::SuspendingLoop,
};

const INT: JvmType = JvmType::Primitive(Primitive::Int);
const OBJECT: &str = "Ljava/lang/Object;";
const CONTINUATION_IMPL: &str = "kotlin/coroutines/jvm/internal/ContinuationImpl";
const CONSTRUCTOR: &str = "(Lkotlin/coroutines/Continuation;)V";
const RESUME: &str = "(Ljava/lang/Object;)Ljava/lang/Object;";
const NO_ARGS: &str = "(Lkotlin/coroutines/Continuation;)Ljava/lang/Object;";
const BOX_INT: MemberRef<'_> = ("kotlin/coroutines/jvm/internal/Boxing", "boxInt", "(I)Ljava/lang/Integer;");
type MemberRef<'a> = (&'a str, &'a str, &'a str);

pub(in crate::kotlin) fn source_return(ty: &Type) -> Option<&'static JvmType> {
    if ty.nullable || !ty.arguments.is_empty() {
        return None;
    }
    if ty.simple_class("kotlin/Int") {
        Some(&INT)
    } else if ty.simple_class("kotlin/Unit") {
        Some(&JvmType::Void)
    } else {
        None
    }
}

impl<'a, 'data> Bytecode<'a, 'data> {
    pub(in crate::kotlin) fn named_suspend(
        &self,
        member: &'a Member<'data>,
        function: &Function,
        members: &PackageDeclaration,
        group: Option<&ClassGroup<'data>>,
        trace: bool,
    ) -> Result<Body<'a>, KotlinError> {
        let declaration = &function.name;
        let unsupported = || invalid(declaration);
        let signature = function.signature.as_ref().ok_or_else(unsupported)?;
        let parameters = signature.suspend_parameters().ok_or_else(unsupported)?;
        let returns = source_return(&function.returns).ok_or_else(unsupported)?;
        if member.access_flags & STATIC == 0 || signature.name != *declaration
            || !function.parameters.iter().zip(parameters).all(|(source, jvm)| exact_type(&source.ty, jvm, false))
        {
            return Err(unsupported());
        }
        let mut locals = Locals::with_parameters(parameters, false, &function.parameters, None, declaration)?;
        locals.templates.member = Some(member);
        locals.templates.properties = &members.properties;
        let completion = locals.next_slot();
        let code = self.function_code(member, declaration)?;
        let instructions = bytecode::decode(code.bytes)?;
        if code.exceptions.is_empty()
            && !instructions.iter().any(|op| matches!(op.operand, Operand::Branch(_) | Operand::Switch { .. }))
        {
            let checked = self.parameter_checks(&instructions, &locals, &function.parameters)?;
            let first = instructions.len() - checked.len();
            // A tail call forwards the incoming continuation itself without
            // manufacturing a new state or checking a suspension marker.
            let (end, tail) = if let [prefix @ .., load, call, ret] = checked
                && aload(load, completion) && ret.opcode == 0xb0
                && let Some(target) = self.reference(call, 0xb8)?
                && let Some(tail) = self.suspend_target(target, members)?
                && tail.result().jvm == *returns
            {
                (first + prefix.len(), Some(tail))
            } else {
                let [prefix @ .., wrapper, ret] = checked else { return Err(unsupported()); };
                if ret.opcode != 0xb0 || (*returns == INT && self.reference(wrapper, 0xb8)? != Some(BOX_INT))
                    || (*returns == JvmType::Void && !self.unit(wrapper)?)
                {
                    return Err(unsupported());
                }
                (first + prefix.len(), None)
            };
            if instructions[first..end].iter().any(|op| {
                op.local_access().is_some_and(|(slots, _)| slots.contains(&u32::from(completion)))
            }) {
                return Err(unsupported());
            }
            let statements::Prefix { mut statements, mut stack, first: value_start } = statements::lower_prefix(
                self, &instructions, first..end, &code, &locals, declaration,
            )?;
            let value = if let Some(tail) = tail {
                if !stack.is_empty() {
                    return Err(unsupported());
                }
                Some(Expr { kind: ExprKind::Invocation(Box::new(tail)), depth: 1 })
            } else if *returns == JvmType::Void && stack.is_empty() {
                None
            } else if stack.len() == 1 {
                let value = pop_value(&mut stack, declaration)?;
                if value.stack_load() != Some(0x15) || *returns != INT {
                    return Err(unsupported());
                }
                Some(value)
            } else {
                return Err(unsupported());
            };
            let implicit_return = value.is_none();
            if let Some(expr) = value {
                if statements.is_empty() {
                    return self.return_expression(expr, &instructions[first..], &code, trace, None);
                }
                let value = TailValue { expr, instructions: value_start..instructions.len() };
                statements.push(Statement::returning(value, &function.returns, returns));
            } else if statements.is_empty() {
                return Ok(Body::Empty);
            }
            let lines = if trace { code.line_numbers(&self.class.pool)? } else { Vec::new() };
            return Ok(Body::Statements(StatementBlock { statements, instructions, lines, implicit_return }));
        }

        // Spill-free source arguments are not inferred across a resumption.
        if !parameters.is_empty() || *returns != INT {
            return Err(unsupported());
        }
        let graph = Graph::parse(self, &instructions, completion, declaration)?;
        let (region, spill) = graph.finally_loop(&code, &locals, members)?;
        self.named_continuation(graph.owner, spill, member, group, declaration)?;
        let lines = if trace { code.line_numbers(&self.class.pool)? } else { Vec::new() };
        Ok(Body::Try(region.into_body(instructions, lines)))
    }

    fn suspend_target(
        &self, (owner, name, descriptor): MemberRef<'_>, members: &PackageDeclaration,
    ) -> Result<Option<Call<'a>>, KotlinError> {
        if owner != self.owner || descriptor != NO_ARGS {
            return Ok(None);
        }
        let mut candidates = members.functions.iter().filter(|candidate| {
            candidate.name == name && candidate.receiver.is_none() && candidate.parameters.is_empty()
        });
        let Some(target) = candidates.next() else { return Ok(None); };
        if candidates.next().is_some() || !target.is_suspend() || !target.type_parameters.is_empty()
            || !target.context_receivers.is_empty() || !target.context_parameters.is_empty()
        {
            return Ok(None);
        }
        let Some(signature) = &target.signature else { return Ok(None); };
        let Some(returns) = source_return(&target.returns) else { return Ok(None); };
        if signature.name != name || signature.suspend_parameters() != Some(&[])
            || !self.find_method(signature)?.is_some_and(|method| method.access_flags & STATIC != 0)
        {
            return Ok(None);
        }
        Ok(Some(Call::named_suspend(name, &target.returns, returns)))
    }

    fn named_continuation(
        &self,
        owner: &str,
        spill: &str,
        method: &Member<'data>,
        group: Option<&ClassGroup<'data>>,
        declaration: &str,
    ) -> Result<(), KotlinError> {
        let unsupported = || invalid(declaration);
        let pool = &self.class.pool;
        let method_name = pool.utf8(method.name_index)?;
        let descriptor = pool.utf8(method.descriptor_index)?;
        let group = group.ok_or_else(unsupported)?;
        let nesting = group.nested_class(owner).ok_or_else(unsupported)?;
        if nesting.outer != self.owner || !group.is_attached(owner)
            || !matches!(nesting.kind, NestedKind::Anonymous)
            || !matches!(&nesting.method, Some((name, desc)) if name == method_name && desc == descriptor)
        {
            return Err(unsupported());
        }
        let class = group.get(owner).ok_or_else(unsupported)?;
        let pool = &class.pool;
        if class.access_flags != FINAL | 0x0020 || class.super_class == 0
            || pool.class_name(class.super_class)? != CONTINUATION_IMPL || !class.interfaces.is_empty()
            || class.fields.len() != 3 || class.methods.len() != 2
            || !matches!(read_metadata(class)?.map(|metadata| metadata.declaration), Some(Declaration::Synthetic(None)))
        {
            return Err(unsupported());
        }
        let mut flags = 0;
        for field in &class.fields {
            flags |= match (pool.utf8(field.name_index)?, pool.utf8(field.descriptor_index)?, field.access_flags) {
                ("label", "I", 0) => 1,
                ("result", OBJECT, 0x1000) => 2,
                (name, OBJECT, 0) if name == spill && name != "result" => 4,
                _ => return Err(unsupported()),
            };
        }
        if flags != 7 {
            return Err(unsupported());
        }
        let body = Bytecode { class, owner };
        let ctor = body.suspend_method("<init>", CONSTRUCTOR, 0, declaration)?;
        let ctor = body.instructions(ctor, declaration)?;
        let resume = body.suspend_method("invokeSuspend", RESUME, 0x0001 | FINAL, declaration)?;
        let resume = body.instructions(resume, declaration)?;
        if !matches!(ctor.as_slice(), [this, completion, init, ret]
            if aload(this, 0) && aload(completion, 1) && ret.opcode == 0xb1
                && body.reference(init, 0xb7)? == Some((CONTINUATION_IMPL, "<init>", CONSTRUCTOR)))
            || !matches!(resume.as_slice(), [this, value, result, set, load, label, bit, or, write, arg, cast, call, ret]
                if aload(this, 0) && aload(value, 1) && aload(set, 0) && aload(load, 0)
                    && body.reference(result, 0xb5)? == Some((owner, "result", OBJECT))
                    && body.reference(label, 0xb4)? == Some((owner, "label", "I"))
                    && int(&body, bit)? == Some(i32::MIN) && or.opcode == 0x80
                    && body.reference(write, 0xb5)? == Some((owner, "label", "I"))
                    && aload(arg, 0) && class_operand(&body, cast, 0xc0)? == Some(CONTINUATION)
                    && body.reference(call, 0xb8)? == Some((self.owner, method_name, descriptor)) && ret.opcode == 0xb0)
        {
            return Err(unsupported());
        }
        Ok(())
    }
}

struct Graph<'ops, 'a, 'data> {
    bytecode: &'ops Bytecode<'a, 'data>,
    instructions: &'ops [Instruction],
    declaration: &'ops str,
    owner: &'a str,
    continuation: u16,
    result: u16,
    marker: u16,
    cases: &'ops [(i32, u32)],
    initial: usize,
    default: usize,
}

struct Point<'a> {
    call: usize,
    target: MemberRef<'a>,
    resume: usize,
    join: usize,
    spill: Option<&'a str>,
}

impl<'ops, 'a, 'data> Graph<'ops, 'a, 'data> {
    fn parse(
        bytecode: &'ops Bytecode<'a, 'data>, instructions: &'ops [Instruction], completion: u16,
        declaration: &'ops str,
    ) -> Result<Self, KotlinError> {
        let unsupported = || invalid(declaration);
        let [incoming, test, not_instance, reload, cast, slot, check, read, high, and, not_resume,
            remove, dup, label, mask, subtract, write, skip, new, duplicate, argument, init, save,
            existing, result, save_result, marker, save_marker, state, read_state, dispatch, body @ ..] = instructions
        else { return Err(unsupported()); };
        let owner = class_operand(bytecode, test, 0xc1)?.ok_or_else(unsupported)?;
        let continuation = astore(slot).ok_or_else(unsupported)?;
        let result_slot = astore(save_result).ok_or_else(unsupported)?;
        let marker_slot = astore(save_marker).ok_or_else(unsupported)?;
        let initial = body.first().ok_or_else(unsupported)?;
        let initial_index = instructions.len() - body.len();
        let Operand::Switch { default, cases } = &dispatch.operand else { return Err(unsupported()); };
        let default = at(instructions, *default).ok_or_else(unsupported)?;
        let label_ref = Some((owner, "label", "I"));
        if default <= initial_index {
            return Err(unsupported());
        }
        if continuation == completion || result_slot == completion || marker_slot == completion
            || continuation == result_slot || continuation == marker_slot || result_slot == marker_slot
            || !aload(incoming, completion) || !branch(not_instance, 0x99, new.offset)
            || !aload(reload, completion) || class_operand(bytecode, cast, 0xc0)? != Some(owner)
            || !aload(check, continuation) || bytecode.reference(read, 0xb4)? != label_ref
            || int(bytecode, high)? != Some(i32::MIN) || and.opcode != 0x7e
            || !branch(not_resume, 0x99, new.offset) || !aload(remove, continuation) || dup.opcode != 0x59
            || bytecode.reference(label, 0xb4)? != label_ref || int(bytecode, mask)? != Some(i32::MIN)
            || subtract.opcode != 0x64 || bytecode.reference(write, 0xb5)? != label_ref || !jump(skip, existing.offset)
            || class_operand(bytecode, new, 0xbb)? != Some(owner) || duplicate.opcode != 0x59
            || !aload(argument, completion) || bytecode.reference(init, 0xb7)? != Some((owner, "<init>", CONSTRUCTOR))
            || astore(save) != Some(continuation) || !aload(existing, continuation)
            || bytecode.reference(result, 0xb4)? != Some((owner, "result", OBJECT))
            || bytecode.reference(marker, 0xb8)? != Some(COROUTINE_MARKER) || !aload(state, continuation)
            || bytecode.reference(read_state, 0xb4)? != label_ref || cases.first() != Some(&(0, initial.offset))
            || cases.iter().enumerate().any(|(index, &(label, _))| i32::try_from(index) != Ok(label))
            || cases.iter().any(|&(_, target)| target < initial.offset || target >= instructions[default].offset)
            || !bytecode.bad_resume(&instructions[default..])?
        {
            return Err(unsupported());
        }
        Ok(Self {
            bytecode, instructions, declaration, owner, continuation, result: result_slot, marker: marker_slot,
            cases, initial: initial_index, default,
        })
    }

    /// Match a suspension edge, not a source call alone. The returned marker
    /// exits only this invocation; an immediate result skips the resume arm.
    fn point(&self, start: usize, thrown: Option<u16>) -> Result<Point<'a>, KotlinError> {
        let unsupported = || invalid(self.declaration);
        let Some([argument, rest @ ..]) = self.instructions.get(start..self.default) else { return Err(unsupported()); };
        let (spill, tail) = if let Some(thrown) = thrown {
            let [state, caught, save, tail @ ..] = rest else { return Err(unsupported()); };
            let Some((owner, field, OBJECT)) = self.bytecode.reference(save, 0xb5)? else { return Err(unsupported()); };
            if !aload(state, self.continuation) || !aload(caught, thrown) || owner != self.owner || field == "result" {
                return Err(unsupported());
            }
            (Some(field), tail)
        } else {
            (None, rest)
        };
        let [state, number, save_label, call, dup, marker, compare, suspended, ret, resume, ..] = tail else {
            return Err(unsupported());
        };
        let case = int(self.bytecode, number)?.and_then(|n| usize::try_from(n).ok()).filter(|&n| n != 0);
        let Some(&(_, offset)) = case.and_then(|n| self.cases.get(n)) else { return Err(unsupported()); };
        let Some(target) = self.bytecode.reference(call, 0xb8)? else { return Err(unsupported()); };
        let Operand::Branch(join) = compare.operand else { return Err(unsupported()); };
        if offset != resume.offset || join <= offset || !aload(argument, self.continuation)
            || !aload(state, self.continuation) || self.bytecode.reference(save_label, 0xb5)? != Some((self.owner, "label", "I"))
            || dup.opcode != 0x59 || !aload(marker, self.marker) || compare.opcode != 0xa6
            || !aload(suspended, self.marker) || ret.opcode != 0xb0
        {
            return Err(unsupported());
        }
        let join = at(self.instructions, join).filter(|&join| join < self.default).ok_or_else(unsupported)?;
        let call = self.default - tail.len() + 3;
        Ok(Point { call, target, resume: call + 6, join, spill })
    }

    /// A resume failure is thrown at the suspension point before the resumed
    /// value is used. In an exceptional finally it must precede rethrowing the
    /// saved exception, so a cleanup failure takes precedence.
    fn resume(&self, point: &Point<'a>, thrown: Option<u16>) -> Result<(), KotlinError> {
        let unsupported = || invalid(self.declaration);
        let arm = &self.instructions[point.resume..point.join];
        let arm = if let Some(thrown) = thrown {
            let [state, restore, cast, save, arm @ ..] = arm else { return Err(unsupported()); };
            let spill = point.spill.ok_or_else(unsupported)?;
            if !aload(state, self.continuation) || self.bytecode.reference(restore, 0xb4)? != Some((self.owner, spill, OBJECT))
                || class_operand(self.bytecode, cast, 0xc0)? != Some("java/lang/Throwable") || astore(save) != Some(thrown)
            {
                return Err(unsupported());
            }
            arm
        } else {
            arm
        };
        let arm = trim_nops(arm);
        if !matches!(arm, [load, failure, value]
            if self.failure(load, failure)? && aload(value, self.result))
        {
            return Err(unsupported());
        }
        Ok(())
    }

    fn failure(&self, load: &Instruction, failure: &Instruction) -> Result<bool, KotlinError> {
        Ok(aload(load, self.result) && self.bytecode.reference(failure, 0xb8)? == Some(THROW_ON_FAILURE))
    }

    /// A source while/try/finally with a conditional break has three cleanup
    /// continuations: break, iteration, and rethrow. Only combine the copies
    /// once the entire table and the continuation of each copy are proved.
    fn finally_loop(
        &self, code: &Code<'data>, locals: &Locals<'_>, members: &PackageDeclaration,
    ) -> Result<(SuspendingLoop<'a>, &'a str), KotlinError> {
        let unsupported = || invalid(self.declaration);
        let instructions = self.instructions;
        let [entry, resumed, extra @ ..] = code.exceptions.as_slice() else { return Err(unsupported()); };
        let [load, check, code_body @ ..] = &instructions[self.initial..self.default] else { return Err(unsupported()); };
        if self.cases.len() != 5 || !self.failure(load, check)? {
            return Err(unsupported());
        }
        let start = self.initial + 2;
        let try_start = at(instructions, u32::from(entry.start_pc)).ok_or_else(unsupported)?;
        let call_start = self.default - trim_nops(code_body).len();
        let main = self.point(call_start, None)?;
        self.resume(&main, None)?;
        let [cast, unbox, store, read, test, ..] = &instructions[main.join..self.default] else { return Err(unsupported()); };
        let Some((0x36, slot)) = local_store(store) else { return Err(unsupported()); };
        if class_operand(self.bytecode, cast, 0xc0)? != Some("java/lang/Number")
            || self.bytecode.reference(unbox, 0xb6)? != Some(("java/lang/Number", "intValue", "()I"))
            || local_load(read) != Some((0x15, slot)) || !(0x99..=0x9e).contains(&test.opcode)
            || [locals.next_slot(), self.continuation, self.result, self.marker].contains(&slot)
        {
            return Err(unsupported());
        }
        let first_start = main.join + 5;
        let second_start = branch_index(instructions, test).ok_or_else(unsupported)?;
        let first = self.point(first_start, None)?;
        self.resume(&first, None)?;
        let second = self.point(second_start, None)?;
        self.resume(&second, None)?;
        let handler = at(instructions, u32::from(entry.handler_pc)).filter(|&handler| handler < self.default)
            .ok_or_else(unsupported)?;
        let caught = astore(&instructions[handler]).ok_or_else(unsupported)?;
        let exceptional = self.point(handler + 1, Some(caught))?;
        self.resume(&exceptional, Some(caught))?;
        if first.join + 2 != second_start || second.join + 2 != handler
            || [locals.next_slot(), self.continuation, self.result, self.marker].contains(&caught)
            || first.target != second.target || first.target != exceptional.target
            || !matches!(&instructions[exceptional.join..self.default], [pop, load, throw, ..]
                if pop.opcode == 0x57 && aload(load, caught) && throw.opcode == 0xbf)
        {
            return Err(unsupported());
        }
        let exit = exceptional.join + 3;
        let (break_copy, negate) = if discarded_jump(instructions, first.join, exit)
            && discarded_jump(instructions, second.join, start)
        {
            (first.call, false)
        } else if discarded_jump(instructions, first.join, start) && discarded_jump(instructions, second.join, exit) {
            (second.call, true)
        } else {
            return Err(unsupported());
        };
        // The protected fragments cover the actual invocation and resumed
        // throwOnFailure/unboxing, but neither the marker return nor cleanup.
        if !(start..=call_start).contains(&try_start) || entry.catch_type != 0 || resumed.catch_type != 0
            || u32::from(entry.end_pc) != instructions[main.call + 1].offset
            || u32::from(resumed.start_pc) != instructions[main.resume].offset
            || u32::from(resumed.end_pc) != instructions[first_start].offset || resumed.handler_pc != entry.handler_pc
            || !match extra {
                [] => true,
                [spill] => spill.catch_type == 0 && spill.start_pc == entry.handler_pc
                    && spill.handler_pc == entry.handler_pc && u32::from(spill.end_pc) == instructions[handler + 1].offset,
                _ => false,
            }
        {
            return Err(unsupported());
        }
        let [result @ .., boxing, ret] = &instructions[exit..self.default] else { return Err(unsupported()); };
        if self.bytecode.reference(boxing, 0xb8)? != Some(BOX_INT) || ret.opcode != 0xb0
            || result.iter().any(|op| op.local_access().is_some())
        {
            return Err(unsupported());
        }
        let mut stack = Vec::new();
        for op in result {
            self.bytecode.expression(op, locals, &mut stack, self.declaration)?;
        }
        if stack.len() != 1 {
            return Err(unsupported());
        }
        let expr = pop_value(&mut stack, self.declaration)?;
        if expr.stack_load() != Some(0x15) {
            return Err(unsupported());
        }
        let main_call = self.bytecode.suspend_target(main.target, members)?.filter(|call| call.result().jvm == INT)
            .ok_or_else(unsupported)?;
        let finally_call = self.bytecode.suspend_target(first.target, members)?.ok_or_else(unsupported)?;
        let local_range = read.offset..instructions[first_start].offset;
        let debug = code.local_variables(&self.bytecode.class.pool)?;
        let name = debug.iter().find(|local| local.index == slot && local.descriptor == "I"
            && u32::from(local.start_pc) == local_range.start
            && u32::from(local.start_pc) + u32::from(local.length) == local_range.end)
            .map_or("suspendValue", |local| local.name);
        let (binding, local) = Statement::bind_suspending_call(name, slot, local_range, main.call..main.call + 1, main_call);
        let condition = logic::condition(test.opcode, &mut vec![StackValue::Value(local)], &[], self.declaration)?;
        let condition = if negate { logic::negate(condition, self.declaration)? } else { condition };
        let iteration_copy = if break_copy == first.call { second.call } else { first.call };
        Ok((SuspendingLoop {
            start,
            protected: try_start,
            binding,
            condition,
            branch: main.join + 3..first_start,
            cleanup: Statement::evaluate(finally_call, break_copy..break_copy + 1),
            copies: [iteration_copy, exceptional.call],
            result: TailValue { expr, instructions: exit..self.default },
        }, exceptional.spill.ok_or_else(unsupported)?))
    }
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven named suspend function protocol")
}

fn astore(instruction: &Instruction) -> Option<u16> {
    local_store(instruction).and_then(|(opcode, slot)| (opcode == 0x3a).then_some(slot))
}

fn int(bytecode: &Bytecode<'_, '_>, instruction: &Instruction) -> Result<Option<i32>, KotlinError> {
    Ok(match (instruction.opcode, &instruction.operand) {
        (op @ 0x02..=0x08, _) => Some(i32::from(op) - 3),
        (0x10 | 0x11, Operand::Immediate(value)) => Some(*value),
        (0x12 | 0x13, Operand::Constant(index)) => match bytecode.class.pool.get(*index)? {
            Constant::Integer(value) => Some(*value),
            _ => None,
        },
        _ => None,
    })
}

fn at(instructions: &[Instruction], offset: u32) -> Option<usize> {
    instructions.binary_search_by_key(&offset, |op| op.offset).ok()
}

fn branch_index(instructions: &[Instruction], branch: &Instruction) -> Option<usize> {
    let Operand::Branch(offset) = branch.operand else { return None; };
    at(instructions, offset)
}

fn branch(instruction: &Instruction, opcode: u8, target: u32) -> bool {
    instruction.opcode == opcode && instruction.operand == Operand::Branch(target)
}

fn jump(instruction: &Instruction, target: u32) -> bool {
    matches!(instruction.opcode, 0xa7 | 0xc8) && instruction.operand == Operand::Branch(target)
}

fn discarded_jump(instructions: &[Instruction], start: usize, end: usize) -> bool {
    matches!(instructions.get(start..start + 2), Some([pop, edge])
        if pop.opcode == 0x57 && instructions.get(end).is_some_and(|end| jump(edge, end.offset)))
}

fn trim_nops(instructions: &[Instruction]) -> &[Instruction] {
    let first = instructions.iter().take_while(|op| op.opcode == 0).count();
    &instructions[first..]
}
