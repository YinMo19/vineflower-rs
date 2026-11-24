// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

mod progression;
mod sum;

use std::ops::Range;

use crate::{classfile::Constant, kotlin::{TypeArgument, Variance}};

use super::{
    Bytecode, Code, Expected, Expr, ExprKind, Instruction, KotlinError, Literal, Locals, Operand,
    Primitive, ValueParameter, identifier, load_opcode, local_load, local_store, statements::{self, Statement},
};

pub(super) use sum::recognize as recognize_sum;

#[derive(Clone, Copy, Debug)]
pub(super) enum Element { Primitive(Primitive), String, Object }

impl Element {
    fn descriptor(self) -> &'static str {
        match self {
            Self::Primitive(Primitive::Int) => "I", Self::Primitive(Primitive::Char) => "C",
            Self::String => "Ljava/lang/String;", Self::Object => "Ljava/lang/Object;",
            _ => unreachable!("loop lowering supports only Int and Char primitives"),
        }
    }

    pub(super) fn load(self) -> u8 {
        match self {
            Self::Primitive(p) => load_opcode(&super::JvmType::Primitive(p)),
            Self::String | Self::Object => 0x19,
        }
    }

    pub(super) fn primitive(self) -> Option<Primitive> {
        if let Self::Primitive(p) = self { Some(p) } else { None }
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Binding<'a> {
    pub slot: u16,
    pub element: Element,
    name: Option<&'a str>,
    suffix: usize,
    pub first_free: u16,
}

impl Binding<'_> {
    pub fn write(self, out: &mut String, declaration: &str) -> Result<(), KotlinError> {
        if let Some(name) = self.name {
            identifier(out, name, declaration)
        } else {
            use std::fmt::Write;
            write!(out, "index{}", self.slot).expect("writing to String");
            for _ in 0..self.suffix { out.push('_'); }
            Ok(())
        }
    }
}

pub(in crate::kotlin) struct LoopBody<'a> {
    form: Form<'a>,
    instructions: Vec<Instruction>,
    start: usize,
    pub lines: Vec<(u16, u16)>,
}

enum Form<'a> {
    For {
        bindings: Binding<'a>,
        source: Source<'a>,
        statements: Vec<Statement<'a>>,
        body: Range<usize>,
    },
    Sum(sum::Reduction<'a>),
}

struct Template<'a> {
    source: Source<'a>,
    slot: u16,
    element: Element,
    scope_start: usize,
    scope_end: usize,
    first_free: u16,
    body: Range<usize>,
}

enum Source<'a> {
    Range { first: Expr<'a>, last: Expr<'a>, step: Option<Expr<'a>>, direction: Direction },
    Iterable(Expr<'a>),
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Direction { Ascend, Descend, Until }

pub(super) fn back_edge_tail(instructions: &[Instruction]) -> bool {
    matches!(instructions, [.., jump, ret] if ret.opcode == 0xb1
        && matches!(jump.opcode, 0xa7 | 0xc8)
        && matches!(jump.operand, Operand::Branch(target) if target < jump.offset))
}

pub(super) fn lower<'a, 'data>(bytecode: &Bytecode<'a, 'data>, instructions: Vec<Instruction>, start: usize,
    code: &Code<'data>, locals: &Locals<'_>, parameters: &[ValueParameter], declaration: &str, trace: bool,
) -> Result<LoopBody<'a>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "loop or backward control transfer");
    let shape = Shape { bytecode, instructions: &instructions[start..], locals, parameters };
    let template = if let Some(template) = shape.iterable()? { template }
        else if let Some(template) = shape.array()? { template }
        else if let Some(template) = shape.simple()? { template }
        else { progression::recognize(&shape)?.ok_or_else(invalid)? };
    let first = shape.instructions[template.scope_start].offset;
    let end = shape.instructions[template.scope_end].offset;
    let name = code.local_variables(&bytecode.class.pool)?.into_iter().find(|local| {
        local.index == template.slot && local.descriptor == template.element.descriptor()
            && u32::from(local.start_pc) == first && u32::from(local.length) == end - first
            && !parameters.iter().any(|parameter| parameter.name == local.name)
            && (!locals.closure_body || !super::lambdas::reserved(local.name))
    }).map(|local| local.name);
    let mut suffix = 0;
    if name.is_none() {
        let mut candidate = format!("index{}", template.slot);
        while parameters.iter().any(|parameter| parameter.name == candidate) {
            candidate.push('_');
            suffix += 1;
        }
    }
    let bindings = Binding { slot: template.slot, element: template.element, name, suffix, first_free: template.first_free };
    let statements = statements::lower_scoped(
        bytecode, shape.instructions, template.body.clone(), locals, declaration,
        &[super::ScopedLocal::Loop(bindings)],
    )?;
    let lines = if trace { code.line_numbers(&bytecode.class.pool)? } else { Vec::new() };
    Ok(LoopBody {
        form: Form::For { bindings, source: template.source, statements, body: template.body },
        instructions, start, lines,
    })
}

struct Shape<'a, 'class, 'data> {
    bytecode: &'a Bytecode<'class, 'data>,
    instructions: &'a [Instruction],
    locals: &'a Locals<'a>,
    parameters: &'a [ValueParameter],
}

impl<'class> Shape<'_, 'class, '_> {
    fn final_indices(&self) -> (usize, usize) { (self.instructions.len() - 2, self.instructions.len() - 1) }

    fn atom(&self, instruction: &Instruction, load: u8) -> Result<Option<Expr<'class>>, KotlinError> {
        let expr = if let Some((opcode, slot)) = local_load(instruction) {
            let Some(index) = self.locals.parameter(slot, opcode) else { return Ok(None); };
            Expr { kind: ExprKind::Parameter { index, load: opcode }, depth: 1 }
        } else {
            let value = match (instruction.opcode, &instruction.operand) {
                (op @ 0x02..=0x08, Operand::None) => i32::from(op) - 3,
                (0x10 | 0x11, Operand::Immediate(value)) => *value,
                (0x12 | 0x13, Operand::Constant(index)) => {
                    let Constant::Integer(value) = *self.bytecode.class.pool.get(*index)? else { return Ok(None); };
                    value
                }
                _ => return Ok(None),
            };
            Expr::literal(Literal::Int(value))
        };
        Ok((expr.stack_load() == Some(load)).then_some(expr))
    }

    fn simple(&self) -> Result<Option<Template<'class>>, KotlinError> {
        let [first, store, lhs, rhs, guard, ..] = self.instructions else { return Ok(None); };
        let Some((0x36, slot)) = local_store(store) else { return Ok(None); };
        if slot < self.locals.next_slot() { return Ok(None); }
        let (back, exit) = self.final_indices();
        if back <= 5 || !branch_to(guard, guard.opcode, &self.instructions[exit]) { return Ok(None); }
        let Some(first) = self.atom(first, 0x15)? else { return Ok(None); };
        let (direction, bound) = if local_load(lhs) == Some((0x15, slot)) {
            (Direction::Ascend, rhs)
        } else if local_load(rhs) == Some((0x15, slot)) {
            (Direction::Descend, lhs)
        } else { return Ok(None); };
        let Some(mut last) = self.atom(bound, 0x15)? else { return Ok(None); };
        let delta = if direction == Direction::Ascend { 1 } else { -1 };
        let (update, primitive) = if is_increment(&self.instructions[back - 1], slot, delta) {
            (back - 1, Primitive::Int)
        } else if back >= 10 && matches!(&self.instructions[back - 5..back], [get, one, add, narrow, store]
            if slot_read(get, slot) && one.opcode == (if delta > 0 { 0x04 } else { 0x02 })
                && add.opcode == 0x60 && narrow.opcode == 0x92 && local_store(store) == Some((0x36, slot)))
        {
            (back - 5, Primitive::Char)
        } else { return Ok(None); };
        let mut direction = direction;
        let body_end = if guard.opcode == 0xa2 && backward(&self.instructions[back], lhs) {
            // Compile-time exclusive endpoint. Subtracting/adding one is
            // legal only when the endpoint remains representable; otherwise
            // preserve the original exclusive Int test with `until`.
            match (direction, integer(&last)) {
                (Direction::Ascend, Some(end)) if primitive == Primitive::Char && (1..=65535).contains(&end) => {
                    last = Expr::literal(Literal::Int(end - 1));
                }
                (Direction::Ascend, Some(end)) if primitive == Primitive::Int && end > i32::MIN => {
                    last = Expr::literal(Literal::Int(end - 1));
                }
                (Direction::Ascend, _) if primitive == Primitive::Int => direction = Direction::Until,
                (Direction::Descend, Some(end))
                    if (primitive == Primitive::Int && end < i32::MAX)
                        || (primitive == Primitive::Char && (0..65535).contains(&end)) =>
                {
                    last = Expr::literal(Literal::Int(end + 1));
                }
                _ => return Ok(None),
            }
            update
        } else if guard.opcode == 0xa3 && backward(&self.instructions[back], &self.instructions[5]) && update >= 8 {
            let [get, limit, stop] = &self.instructions[update - 3..update] else { unreachable!() };
            if !slot_read(get, slot) || !same(limit, bound) || !branch_to(stop, 0x9f, &self.instructions[exit]) {
                return Ok(None);
            }
            update - 3
        } else { return Ok(None); };
        Ok(Some(Template { source: Source::Range { first, last, step: None, direction }, slot,
            element: Element::Primitive(primitive), scope_start: 2, scope_end: exit,
            first_free: slot.saturating_add(1), body: 5..body_end }))
    }

    fn array(&self) -> Result<Option<Template<'class>>, KotlinError> {
        let [zero, save_index, length_source, length, save_length, get_index, get_length, guard,
            array, element_index, element, save_element, ..] = self.instructions else { return Ok(None); };
        let Some((0x36, index)) = local_store(save_index) else { return Ok(None); };
        let Some((0x36, limit)) = local_store(save_length) else { return Ok(None); };
        let Some((0x3a, slot)) = local_store(save_element) else { return Ok(None); };
        let Some((0x19, source_slot)) = local_load(length_source) else { return Ok(None); };
        let Some(parameter) = self.locals.parameter(source_slot, 0x19) else { return Ok(None); };
        let (back, exit) = self.final_indices();
        let body = 12;
        if back <= body || zero.opcode != 0x03 || length.opcode != 0xbe || element.opcode != 0x32
            || index == limit || index == slot || limit == slot
            || index.min(limit).min(slot) < self.locals.next_slot()
            || !slot_read(get_index, index) || !slot_read(get_length, limit) || !slot_read(element_index, index)
            || local_load(array) != Some((0x19, source_slot))
            || !branch_to(guard, 0xa2, &self.instructions[exit])
            || !is_increment(&self.instructions[back - 1], index, 1)
            || !backward(&self.instructions[back], get_index)
            || super::invocations::string_array_element(&self.parameters[parameter].ty, self.locals.slots[parameter].1).is_none()
        {
            return Ok(None);
        }
        let Some(source) = self.atom(array, 0x19)? else { return Ok(None); };
        Ok(Some(Template { source: Source::Iterable(source), slot, element: Element::String,
            scope_start: body, scope_end: back - 1, first_free: index.max(limit).max(slot).saturating_add(1),
            body: body..back - 1 }))
    }

    fn iterable(&self) -> Result<Option<Template<'class>>, KotlinError> {
        let [load, iterator, saved, get, has_next, guard, get_next, next, rest @ ..] = self.instructions else { return Ok(None); };
        let Some((0x19, parameter_slot)) = local_load(load) else { return Ok(None); };
        let Some(parameter) = self.locals.parameter(parameter_slot, 0x19) else { return Ok(None); };
        let source_type = &self.parameters[parameter].ty;
        let owner = match source_type.class_id() {
            Some("kotlin/collections/Iterable" | "kotlin/collections/MutableIterable") => "java/lang/Iterable",
            Some("kotlin/collections/Collection" | "kotlin/collections/MutableCollection") => "java/util/Collection",
            Some("kotlin/collections/List" | "kotlin/collections/MutableList") => "java/util/List",
            Some("kotlin/collections/Set" | "kotlin/collections/MutableSet") => "java/util/Set",
            Some("kotlin/sequences/Sequence") => "kotlin/sequences/Sequence",
            _ => return Ok(None),
        };
        if source_type.nullable || source_type.flexible.is_some() || source_type.raw
            || !self.invoke_interface(iterator, owner, "iterator", "()Ljava/util/Iterator;")?
        { return Ok(None); }
        let Some((0x3a, iterator_slot)) = local_store(saved) else { return Ok(None); };
        let (back, exit) = self.final_indices();
        if iterator_slot < self.locals.next_slot() || local_load(get) != Some((0x19, iterator_slot))
            || local_load(get_next) != Some((0x19, iterator_slot)) || !backward(&self.instructions[back], get)
            || !branch_to(guard, 0x99, &self.instructions[exit])
            || !self.invoke_interface(has_next, "java/util/Iterator", "hasNext", "()Z")?
            || !self.invoke_interface(next, "java/util/Iterator", "next", "()Ljava/lang/Object;")?
        { return Ok(None); }
        let Some(raw_store) = rest.first() else { return Ok(None); };
        let (element, store, head) = match source_type.arguments.as_slice() {
            [TypeArgument::Type(Variance::Invariant | Variance::Out, ty)]
                if !ty.nullable && ty.flexible.is_none() && ty.class_id() == Some("kotlin/Int") =>
            {
                let [cast, unbox, store, ..] = rest else { return Ok(None); };
                if !self.class_operation(cast, 0xc0, "java/lang/Number")?
                    || self.bytecode.reference(unbox, 0xb6)? != Some(("java/lang/Number", "intValue", "()I"))
                { return Ok(None); }
                (Element::Primitive(Primitive::Int), store, 11)
            }
            [TypeArgument::Type(Variance::Invariant | Variance::Out, ty)]
                if ty.flexible.is_none() && ty.class_id() == Some("kotlin/String") =>
            {
                let [cast, store, ..] = rest else { return Ok(None); };
                if !self.class_operation(cast, 0xc0, "java/lang/String")? { return Ok(None); }
                (Element::String, store, 10)
            }
            [TypeArgument::Star] => (Element::Object, raw_store, 9),
            [TypeArgument::Type(Variance::Invariant | Variance::Out, ty)]
                if ty.class_id() == Some("kotlin/Any") =>
            {
                (Element::Object, raw_store, 9)
            }
            _ => return Ok(None),
        };
        let Some((store_opcode, slot)) = local_store(store) else { return Ok(None); };
        if store_opcode != element.load() + 0x21 || slot < self.locals.next_slot() || slot == iterator_slot || head > back { return Ok(None); }
        let Some(source) = self.atom(load, 0x19)? else { return Ok(None); };
        Ok(Some(Template { source: Source::Iterable(source), slot, element, scope_start: head, scope_end: back,
            first_free: slot.max(iterator_slot).saturating_add(1), body: head..back }))
    }

    fn invoke_interface(&self, instruction: &Instruction, owner: &str, name: &str, descriptor: &str) -> Result<bool, KotlinError> {
        let Operand::InvokeInterface { index, count: 1 } = instruction.operand else { return Ok(false); };
        let pool = &self.bytecode.class.pool;
        Ok(instruction.opcode == 0xb9 && matches!(pool.get(index)?, Constant::InterfaceMethodref { .. })
            && pool.member_ref(index)? == (owner, name, descriptor))
    }

    fn class_operation(&self, instruction: &Instruction, opcode: u8, name: &str) -> Result<bool, KotlinError> {
        let Operand::Constant(index) = instruction.operand else { return Ok(false); };
        Ok(instruction.opcode == opcode && self.bytecode.class.pool.class_name(index)? == name)
    }
}

fn integer(expr: &Expr<'_>) -> Option<i32> {
    if let ExprKind::Literal(Literal::Int(value)) = expr.kind { Some(value) } else { None }
}

fn slot_read(instruction: &Instruction, slot: u16) -> bool { local_load(instruction) == Some((0x15, slot)) }
fn is_increment(instruction: &Instruction, slot: u16, delta: i16) -> bool {
    instruction.opcode == 0x84 && instruction.operand == Operand::Increment { index: slot, amount: delta }
}
fn same(left: &Instruction, right: &Instruction) -> bool { left.opcode == right.opcode && left.operand == right.operand }
fn branch_to(instruction: &Instruction, opcode: u8, target: &Instruction) -> bool {
    instruction.opcode == opcode && instruction.operand == Operand::Branch(target.offset)
}
fn backward(instruction: &Instruction, target: &Instruction) -> bool {
    matches!(instruction.opcode, 0xa7 | 0xc8) && branch_to(instruction, instruction.opcode, target)
}

impl<'a> LoopBody<'a> {
    pub(super) fn sum(
        reduction: sum::Reduction<'a>, instructions: Vec<Instruction>, start: usize, lines: Vec<(u16, u16)>,
    ) -> Self {
        Self { form: Form::Sum(reduction), instructions, start, lines }
    }
}

impl LoopBody<'_> {
    pub fn write(&self, out: &mut String, parameters: &[ValueParameter], declaration: &str,
        indent: &str, unit: &str, mut map: impl FnMut(&Instruction, usize),
    ) -> Result<(), KotlinError> {
        let instructions = &self.instructions[self.start..];
        let (bindings, source, statements, body) = match &self.form {
            Form::For { bindings, source, statements, body } => (bindings, source, statements, body),
            Form::Sum(reduction) => return reduction.write(out, parameters, declaration, indent, unit, instructions, map),
        };
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("for (");
        bindings.write(out, declaration)?;
        out.push_str(" in ");
        match source {
            Source::Range { first, last, step, direction } => {
                let expected = Expected::Primitive(bindings.element.primitive().expect("range has primitive elements"));
                first.write_at(out, expected, parameters, declaration, 0)?;
                out.push_str(match direction { Direction::Ascend => "..", Direction::Descend => " downTo ", Direction::Until => " until " });
                last.write_at(out, expected, parameters, declaration, 0)?;
                if let Some(step) = step {
                    out.push_str(" step ");
                    step.write_at(out, Expected::Primitive(Primitive::Int), parameters, declaration, 0)?;
                }
            }
            Source::Iterable(expr) => expr.write_at(out, Expected::Reference, parameters, declaration, 0)?,
        }
        out.push_str(") {\n");
        let (ret, instructions) = instructions.split_last().expect("for-loop has return");
        for instruction in instructions[..body.start].iter().chain(&instructions[body.end..]) {
            if instruction.opcode != 0x00 { map(instruction, 1); }
        }
        let mut line = 2;
        for statement in statements {
            out.push_str(indent);
            out.push_str(unit);
            out.push_str(unit);
            statement.write(out, parameters, declaration)?;
            out.push('\n');
            super::switches::map_statement(instructions, statement, line, &mut map);
            line += 1;
        }
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("}\n");
        out.push_str(indent);
        out.push('}');
        map(ret, line + 1);
        Ok(())
    }
}
