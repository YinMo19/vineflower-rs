// Based on Vineflower SecondaryFunctionsHelper and PPandMMHelper (Apache-2.0).
use crate::{
    bytecode::{Instruction, Operand},
    classfile::{Constant, ConstantPool},
    descriptor::{Primitive, Type},
    source_text::Document,
};

use super::{
    Effect, LiftError, Machine,
    expr::{
        ADDITIVE, BIT_AND, BIT_OR, BIT_XOR, BOOLEAN, Category, Expr, INT, MULTIPLICATIVE,
        Order, PRIMARY, SHIFT, Source, UNARY,
    },
    operations::array_store_opcode,
};

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(super) struct Binary {
    pub(super) left: Category,
    pub(super) right: Category,
    pub(super) operator: &'static str,
    pub(super) precedence: u8,
    pub(super) can_throw: bool,
}

impl Binary {
    pub(super) fn of(opcode: u8) -> Option<Self> {
        let (left, right, operator, precedence) = match opcode {
            0x60..=0x73 => {
                let relative = opcode - 0x60;
                let category = Category::for_local(relative % 4);
                let (operator, precedence) = [
                    ("+", ADDITIVE), ("-", ADDITIVE), ("*", MULTIPLICATIVE),
                    ("/", MULTIPLICATIVE), ("%", MULTIPLICATIVE),
                ][usize::from(relative / 4)];
                (category, category, operator, precedence)
            }
            0x78..=0x83 => {
                let relative = opcode - 0x78;
                let left = Category::for_local(relative % 2);
                let right = if relative < 6 { Category::Int } else { left };
                let (operator, precedence) = [
                    ("<<", SHIFT), (">>", SHIFT), (">>>", SHIFT),
                    ("&", BIT_AND), ("|", BIT_OR), ("^", BIT_XOR),
                ][usize::from(relative / 2)];
                (left, right, operator, precedence)
            }
            _ => return None,
        };
        let can_throw = matches!(left, Category::Int | Category::Long) && matches!(operator, "/" | "%");
        Some(Self { left, right, operator, precedence, can_throw })
    }

    pub(super) fn increment(self) -> Option<&'static str> {
        match self.operator {
            "+" => Some("++"),
            "-" => Some("--"),
            _ => None,
        }
    }

    pub(super) fn assignment_conversion(self, left: &Type, right: &Type, narrow: Option<u8>) -> bool {
        let Type::Primitive(left) = left else { return false };
        let Type::Primitive(right) = right else { return false };
        if *left == Primitive::Boolean || *right == Primitive::Boolean {
            return *left == Primitive::Boolean && *right == Primitive::Boolean
                && matches!(self.operator, "&" | "|" | "^") && narrow.is_none();
        }
        let promote = |primitive| match primitive {
            Primitive::Long => 1,
            Primitive::Float => 2,
            Primitive::Double => 3,
            _ => 0,
        };
        let left_rank = promote(*left);
        let right_rank = promote(*right);
        if matches!(self.operator, "<<" | ">>" | ">>>") {
            // The JVM consumes an int shift distance. Explicit long-to-int
            // bytecode conversions are already represented by the RHS.
            if right_rank != 0 || self.left != Category::for_local(left_rank) {
                return false;
            }
        } else if self.left != Category::for_local(left_rank.max(right_rank)) {
            return false;
        }
        let expected = match (*left, self.left) {
            (Primitive::Byte, Category::Int) => Some(0x91),
            (Primitive::Char, Category::Int) => Some(0x92),
            (Primitive::Short, Category::Int) => Some(0x93),
            (Primitive::Int, Category::Int)
            | (Primitive::Long, Category::Long)
            | (Primitive::Float, Category::Float)
            | (Primitive::Double, Category::Double) => None,
            _ => return false,
        };
        narrow == expected
    }
}

#[derive(Clone, Copy)]
pub(super) struct LocalWrite {
    pub(super) index: u16,
    pub(super) category: Category,
}

impl LocalWrite {
    fn of(op: &Instruction) -> Option<Self> {
        let (index, kind) = match (op.opcode, &op.operand) {
            (opcode @ 0x36..=0x3a, Operand::Local(index)) => (*index, opcode - 0x36),
            (opcode @ 0x3b..=0x4e, _) => {
                let compact = opcode - 0x3b;
                (u16::from(compact % 4), compact / 4)
            }
            _ => return None,
        };
        Some(Self { index, category: Category::for_local(kind) })
    }

    fn dup_opcode(self) -> u8 {
        if matches!(self.category, Category::Long | Category::Double) { 0x5c } else { 0x59 }
    }

    fn matches(self, value: &Expr) -> bool {
        matches!(value.source, Source::Local(index) if index == self.index)
            && Category::of(&value.ty) == Some(self.category)
    }

    fn loads_for_return(self, load: &Instruction, ret: &Instruction) -> bool {
        let load_kind = match load.opcode {
            0x15..=0x19 => load.opcode - 0x15,
            0x1a..=0x2d => (load.opcode - 0x1a) / 4,
            _ => return false,
        };
        Category::for_local(load_kind) == self.category
            && load.local_access().is_some_and(|(slots, read)| {
                read && slots.start == u32::from(self.index)
            })
            && matches!(ret.opcode, 0xac..=0xb0)
            && Category::for_local(ret.opcode - 0xac) == self.category
    }
}

/// Identity introduced by an actual JVM duplication, never by matching text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct StackAlias {
    pub(super) instruction: u32,
    pub(super) ordinal: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AddressPart {
    This,
    Duplicate(StackAlias),
    Index(i32),
}

impl AddressPart {
    pub(super) fn receiver(value: &Expr) -> Option<Self> {
        if matches!(value.source, Source::This) {
            Some(Self::This)
        } else {
            value.alias.map(Self::Duplicate)
        }
    }

    pub(super) fn index(value: &Expr) -> Option<Self> {
        if let Source::Integer(index) = value.source {
            Some(Self::Index(index))
        } else {
            value.alias.map(Self::Duplicate)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Access {
    Static(u16),
    Field(u16, AddressPart),
    Array { store: u8, array: AddressPart, index: AddressPart },
}

impl Access {
    fn address_values(self) -> usize {
        match self {
            Self::Static(_) => 0,
            Self::Field(..) => 1,
            Self::Array { .. } => 2,
        }
    }

    fn matches_store(self, op: &Instruction, prefix: &[Expr]) -> bool {
        match (self, op.opcode, &op.operand, prefix) {
            (Self::Static(read), 0xb3, Operand::Constant(write), _) => read == *write,
            (Self::Field(read, receiver), 0xb5, Operand::Constant(write), [.., actual]) =>
                read == *write && AddressPart::receiver(actual) == Some(receiver),
            (Self::Array { store, array, index }, opcode, _, [.., actual_array, actual_index]) =>
                store == opcode && AddressPart::receiver(actual_array) == Some(array)
                    && AddressPart::index(actual_index) == Some(index),
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
enum Target {
    Local(LocalWrite),
    Access(Access),
    ArrayAssignment,
}

impl Target {
    fn address_values(self) -> usize {
        match self {
            Self::Local(_) => 0,
            Self::Access(access) => access.address_values(),
            Self::ArrayAssignment => 2,
        }
    }

    fn dup_opcode(self, ty: &Type) -> u8 {
        store_dup_opcode(ty, self.address_values() as u8)
    }
}

pub(super) fn store_dup_opcode(ty: &Type, address_slots: u8) -> u8 {
    0x59 + (if ty.slots() == 2 { 3 } else { 0 }) + address_slots
}

pub(crate) struct AssignmentStep {
    pub(crate) consumed: usize,
    pub(crate) effect: Effect,
    /// A harmless blank declaration is not the source of any bytecode.
    pub(crate) declaration: Option<Document>,
}

#[derive(Clone, Copy)]
pub(super) enum Form {
    Assign,
    Compound(Binary),
    Increment { text: &'static str, postfix: bool },
}

impl Form {
    pub(super) fn render(self, mut target: Document, right: Option<Document>) -> (Document, u8) {
        match self {
            Self::Assign => {
                target.push_str(" = ");
                target.append(right.expect("plain assignment has a RHS"));
                (target, 0)
            }
            Self::Compound(binary) => {
                target.push(' ');
                target.push_str(binary.operator);
                target.push_str("= ");
                target.append(right.expect("compound assignment has a RHS"));
                (target, 0)
            }
            Self::Increment { text, postfix: true } => {
                target.push_str(text);
                (target, PRIMARY)
            }
            Self::Increment { text, postfix: false } => {
                target.prepend_str(text);
                (target, UNARY)
            }
        }
    }
}

struct Candidate<'a> {
    store: &'a Instruction,
    target: Target,
    form: Form,
    order: Option<Order>,
    operands: usize,
    leaves_value: bool,
    declaration: bool,
}

impl Machine<'_, '_> {
    pub(crate) fn forget_assignment_aliases(&mut self) {
        for value in &mut self.stack {
            value.alias = None;
            if matches!(value.source, Source::Access(_)) {
                value.source = Source::Plain;
            }
        }
    }

    /// Recover a read/modify/write or a proven store alias before generic dup
    /// lowering spills it. The caller supplies a single straight-line region.
    pub(crate) fn step_assignment(
        &mut self,
        instructions: &[Instruction],
        permits: impl Fn(usize, &Instruction) -> bool,
    ) -> Result<Option<AssignmentStep>, LiftError> {
        let Some(first) = instructions.first() else { return Ok(None) };
        if first.opcode == 0x5c
            && let Some(step) = self.array_compound_without_spill(instructions, &permits)?
        {
            return Ok(Some(step));
        }
        let candidate = if matches!(first.opcode, 0x59..=0x5e) {
            self.duplicated_assignment(instructions)
        } else if let Some(binary) = Binary::of(first.opcode) {
            self.compound_assignment(instructions, binary)
        } else {
            None
        };
        let Some((consumed, candidate)) = candidate else { return Ok(None) };
        if !permitted_prefix(instructions, consumed, &permits) {
            return Ok(None);
        }
        if consumed == 2
            && !candidate.leaves_value
            && let Target::Local(target) = candidate.target
            && let [left, _] = self.stack.as_slice()
            && left.ty == self.descriptor.return_type
            && let Some([load, ret]) = instructions.get(consumed..consumed + 2)
            && target.loads_for_return(load, ret)
            && candidate.store.offset.checked_add(candidate.store.len) == Some(load.offset)
            && load.offset.checked_add(load.len) == Some(ret.offset)
            && permits(consumed, load)
            && permits(consumed + 1, ret)
        {
            // The final store is only read by this return. Lift the same
            // binary expression without committing it to the local slot.
            let effect = self.step(first)?;
            debug_assert!(matches!(effect, Effect::None));
            self.stack
                .last_mut()
                .expect("binary expression leaves one value")
                .text
                .omit_bytes(candidate.store.offset..ret.offset);
            return Ok(Some(AssignmentStep {
                consumed: consumed + 1,
                effect,
                declaration: None,
            }));
        }
        if let Candidate { target: Target::Local(target), form: Form::Assign, leaves_value: true, declaration: false, store, .. } = candidate
            && let Some(value) = self.stack.last_mut()
            && target.matches(value)
            && matches!(self.opcode, 0x15..=0x2d)
            && value.order.is_some_and(|order| order.first == self.offset && order.last == self.offset)
        {
            // An immediate load/dup/store to the same active binding
            // leaves the input value and does not change any local state.
            value.text.omit_bytes(first.offset..store.offset + store.len);
            self.offset = store.offset;
            self.opcode = store.opcode;
            return Ok(Some(AssignmentStep { consumed, effect: Effect::None, declaration: None }));
        }
        let Candidate { store, target, form, order, operands, leaves_value, declaration } = candidate;
        let mut right = self.pop_raw()?;
        let left = if operands >= 2 { Some(self.pop_raw()?) } else { None };
        let implicit_update = if !leaves_value
            && matches!((form, target), (Form::Compound(_), Target::Local(_)))
        {
            left.as_ref().and_then(Expr::deferred_operand_origin)
        } else {
            None
        };
        if operands == 3 {
            self.pop_raw()?;
        }
        let array_target = if matches!(target, Target::ArrayAssignment) {
            let index = self.pop_raw()?;
            let array = self.pop_raw()?;
            Some(self.array_write_target(array, index))
        } else {
            for _ in 0..target.address_values() {
                self.pop_raw()?;
            }
            None
        };
        let ty = left.as_ref().unwrap_or(&right).ty.clone();
        self.offset = store.offset;
        self.opcode = store.opcode;
        self.instruction_has_source = true;
        if !leaves_value {
            self.before_statement(order)?;
        }
        let (access, declaration) = match target {
            Target::Local(target) => self.commit_assignment_local(store, target, &ty, declaration),
            Target::ArrayAssignment => (array_target.expect("verified array address"), None),
            // Keep the exact target spelling, layout, and symbol reference.
            // The saved address must not be reevaluated as a second access.
            Target::Access(_) => (left.map_or_else(|| std::mem::take(&mut right.text), |left| left.text), None),
        };
        if matches!(form, Form::Compound(_)) && ty == BOOLEAN && right.ty == INT {
            right = self.boolean_value(right);
        }
        let (mut text, precedence) = form.render(access, Some(right.text));
        if let Some(load) = implicit_update {
            // The source compound operator already performs the old-value
            // load and arithmetic; the explicit RHS and store own the map.
            text.omit_bytes(load.bytes());
            text.omit_bytes(first.offset..first.offset + first.len);
        }
        if leaves_value {
            self.push(Expr {
                order,
                precedence,
                observable: true,
                statement: true,
                ..Expr::atom(ty, text)
            })?;
            Ok(Some(AssignmentStep { consumed, effect: Effect::None, declaration }))
        } else {
            text.push(';');
            Ok(Some(AssignmentStep { consumed, effect: Effect::Statement(text), declaration }))
        }
    }

    /// `dup2; xaload; rhs; op; [narrow]; [dup_x2]; xastore` retains
    /// only the exact address, never an independently used stack reference.
    /// Java's compound lvalue executes the null/bounds check before `rhs`.
    fn array_compound_without_spill(
        &mut self,
        ops: &[Instruction],
        permits: &impl Fn(usize, &Instruction) -> bool,
    ) -> Result<Option<AssignmentStep>, LiftError> {
        let [_, load, rhs, operation, ..] = ops else { return Ok(None) };
        let [.., array, index] = self.stack.as_slice() else { return Ok(None) };
        let Type::Array(component) = &array.ty else { return Ok(None) };
        if !matches!(**component, Type::Primitive(primitive) if primitive != Primitive::Boolean)
            || array.is_open_array()
            || Category::of(&index.ty) != Some(Category::Int)
            || matches!(index.source, Source::Comparison(_))
        {
            return Ok(None);
        }
        let ty = component.as_ref().clone();
        let expected_store = array_store_opcode(&ty);
        let (Some(binary), Some(right_type), Some((store, consumed, narrow))) = (
            Binary::of(operation.opcode), numeric_literal_type(&self.class.pool, rhs), find_store(ops, 4, true),
        ) else { return Ok(None) };
        let duplicate = matches!(ops[consumed - 2].opcode, 0x59..=0x5e);
        let width = u32::from(ty.slots());
        let scratch = 2.max(width + u32::from(right_type.slots())).max(if duplicate { 2 * width } else { 0 });
        if load.opcode != expected_store - 0x21 || store.opcode != expected_store
            || Category::of(&ty) != Some(binary.left) || Category::of(&right_type) != Some(binary.right)
            || !binary.assignment_conversion(&ty, &right_type, narrow)
            || duplicate && ops[consumed - 2].opcode != store_dup_opcode(&ty, 2)
            || self.stack_slots + scratch > self.max_stack
            || !permitted_prefix(ops, consumed, permits)
        {
            return Ok(None);
        }
        let checked = self.join_order(self.order_of([array, index], false)?, Order::at(load.offset))?;
        let order = self.join_order(Some(checked), Order::at(store.offset))?;
        let effect = self.step(rhs)?;
        debug_assert!(matches!(effect, Effect::None));
        let right = self.pop_raw()?;
        let index = self.pop_raw()?;
        let array = self.pop_raw()?;
        self.offset = store.offset;
        self.opcode = store.opcode;
        self.instruction_has_source = true;
        if !duplicate {
            self.before_statement(Some(order))?;
        }
        let form = match binary.increment().filter(|_| is_one(&right)) {
            Some(text) => Form::Increment { text, postfix: !duplicate },
            None => Form::Compound(binary),
        };
        let (mut text, precedence) = form.render(self.array_write_target(array, index), Some(right.text));
        text.omit_bytes(load.offset..load.offset + load.len);
        let arithmetic_end = &ops[3 + usize::from(narrow.is_some())];
        text.omit_bytes(operation.offset..arithmetic_end.offset + arithmetic_end.len);
        let effect = if duplicate {
            self.push(Expr { order: Some(order), precedence, observable: true, statement: true, ..Expr::atom(ty, text) })?;
            Effect::None
        } else {
            text.push(';');
            Effect::Statement(text)
        };
        Ok(Some(AssignmentStep { consumed, effect, declaration: None }))
    }

    fn duplicated_assignment<'a>(&self, ops: &'a [Instruction]) -> Option<(usize, Candidate<'a>)> {
        let [prefix @ .., value] = self.stack.as_slice() else { return None };
        if value.is_uninitialized(self.initialized_this) || matches!(value.source, Source::Comparison(_)) {
            return None;
        }
        let second = ops.get(1)?;
        if (0x4f..=0x56).contains(&second.opcode) {
            let [.., array, index] = prefix else { return None };
            let Type::Array(component) = &array.ty else { return None };
            let target = Target::ArrayAssignment;
            // A JVM duplicate keeps the pre-store value. If the source
            // assignment narrows it or changes its Java type, the surviving
            // value cannot be substituted by the assignment expression.
            if !matches!(**component, Type::Primitive(_))
                || **component != value.ty
                || second.opcode != array_store_opcode(component)
                || Category::of(&index.ty) != Some(Category::Int)
                || matches!(index.source, Source::Comparison(_))
                || ops[0].opcode != target.dup_opcode(&value.ty)
                || self.stack_slots + u32::from(value.ty.slots()) > self.max_stack
            {
                return None;
            }
            let order = self.order_of([array, index, value], false).ok()?;
            let order = self.join_order(order, Order::at(second.offset)).ok()?;
            return Some((2, Candidate {
                store: second, target, form: Form::Assign, order: Some(order),
                operands: 1, leaves_value: true, declaration: false,
            }));
        }
        if let Some(target) = LocalWrite::of(second) {
            if ops[0].opcode != target.dup_opcode() || Category::of(&value.ty) != Some(target.category)
                || self.stack_slots + u32::from(value.ty.slots()) > self.max_stack
            {
                return None;
            }
            let declaration = self.assignment_local_destination(second, target, value)?;
            if declaration && !self.initialized_this {
                return None;
            }
            let order = self.join_order(value.order, Order::at(second.offset)).ok()?;
            return Some((2, Candidate {
                store: second, target: Target::Local(target), form: Form::Assign, order: Some(order),
                operands: 1, leaves_value: true, declaration,
            }));
        }

        let operation = ops.get(2)?;
        let binary = Binary::of(operation.opcode)?;
        let increment = binary.increment()?;
        let one = one_instruction(&self.class.pool, second, binary.right)?;
        let (store, consumed, narrow) = find_store(ops, 3, false)?;
        let target = self.update_destination(store, prefix, value)?;
        if ops[0].opcode != target.dup_opcode(&value.ty)
            || self.stack_slots + 2 * u32::from(value.ty.slots()) > self.max_stack
            || !binary.assignment_conversion(&value.ty, &one, narrow)
        {
            return None;
        }
        let order = self.join_order(value.order, Order::at(store.offset)).ok()?;
        Some((consumed, Candidate {
            store, target, form: Form::Increment { text: increment, postfix: true },
            order: Some(order), operands: 1, leaves_value: true, declaration: false,
        }))
    }

    fn compound_assignment<'a>(&self, ops: &'a [Instruction], binary: Binary) -> Option<(usize, Candidate<'a>)> {
        let [prefix @ .., left, right] = self.stack.as_slice() else { return None };
        if Category::of(&left.ty) != Some(binary.left) || Category::of(&right.ty) != Some(binary.right)
            || matches!(right.source, Source::Comparison(_))
        {
            return None;
        }
        let (store, consumed, narrow) = find_store(ops, 1, true)?;
        let target = self.update_destination(store, prefix, left)?;
        let boolean = left.ty == BOOLEAN && right.ty == INT && matches!(right.source, Source::Integer(0 | 1));
        if !binary.assignment_conversion(&left.ty, if boolean { &BOOLEAN } else { &right.ty }, narrow) {
            return None;
        }
        let duplicate = matches!(ops[consumed - 2].opcode, 0x59..=0x5e);
        if duplicate {
            let slots_at_dup = self.stack_slots - u32::from(left.ty.slots() + right.ty.slots())
                + 2 * u32::from(left.ty.slots());
            if ops[consumed - 2].opcode != target.dup_opcode(&left.ty) || slots_at_dup > self.max_stack {
                return None;
            }
        }
        let inc = if is_one(right) { binary.increment() } else { None };
        // javac emits two adjacent loads (rather than dup) for some byte-
        // sized postfix sites. Reading other stack values is not equivalent.
        let old = if let Target::Local(target) = target && inc.is_some() && !duplicate {
            prefix.last().filter(|old| {
                target.matches(old) && old.ty == left.ty && old.order.zip(left.order)
                    .is_some_and(|(old, left)| old.last.checked_add(1) == Some(left.first))
            })
        } else {
            None
        };
        let preceding = self.order_of(old.into_iter().chain([left, right]), false).ok()?;
        let order = self.join_order(preceding, Order::at(store.offset)).ok()?;
        let form = if let Some(text) = inc {
            Form::Increment { text, postfix: old.is_some() || !duplicate }
        } else {
            Form::Compound(binary)
        };
        Some((consumed, Candidate {
            store, target, form, order: Some(order), operands: 2 + usize::from(old.is_some()),
            leaves_value: duplicate || old.is_some(), declaration: false,
        }))
    }

    fn update_destination(&self, op: &Instruction, prefix: &[Expr], value: &Expr) -> Option<Target> {
        if let Some(local) = LocalWrite::of(op)
            && local.matches(value) && !self.assignment_local_destination(op, local, value)?
        {
            return Some(Target::Local(local));
        }
        if let Source::Access(access) = value.source
            && access.matches_store(op, prefix)
            && !self.own_final_target(op)
        {
            return Some(Target::Access(access));
        }
        None
    }

    fn own_final_target(&self, op: &Instruction) -> bool {
        let (0xb3 | 0xb5, Operand::Constant(member)) = (op.opcode, &op.operand) else {
            return false;
        };
        let pool = &self.class.pool;
        let Ok((owner, field_name, field_ty)) = pool.member_ref(*member) else {
            return true;
        };
        owner == self.owner && self.class.fields.iter().any(|field| {
            field.access_flags & 0x0010 != 0
                && pool.utf8(field.name_index).is_ok_and(|name| name == field_name)
                && pool.utf8(field.descriptor_index).is_ok_and(|ty| ty == field_ty)
        })
    }
}

pub(super) fn one_instruction(
    pool: &ConstantPool<'_>,
    op: &Instruction,
    category: Category,
) -> Option<Type> {
    use Constant::*;
    let ty = match (op.opcode, &op.operand) {
        (0x04 | 0x10 | 0x11, _) if op.opcode == 0x04 || op.operand == Operand::Immediate(1) => INT,
        (0x0a, _) => Type::Primitive(Primitive::Long),
        (0x0c, _) => Type::Primitive(Primitive::Float),
        (0x0f, _) => Type::Primitive(Primitive::Double),
        (0x12..=0x14, Operand::Constant(index)) => match pool.get(*index).ok()? {
            Integer(1) if op.opcode != 0x14 => INT,
            Long(1) if op.opcode == 0x14 => Type::Primitive(Primitive::Long),
            Float(value) if op.opcode != 0x14 && *value == 1.0 => Type::Primitive(Primitive::Float),
            Double(value) if op.opcode == 0x14 && *value == 1.0 => Type::Primitive(Primitive::Double),
            _ => return None,
        },
        _ => return None,
    };
    (Category::of(&ty) == Some(category)).then_some(ty)
}

fn numeric_literal_type(pool: &ConstantPool<'_>, op: &Instruction) -> Option<Type> {
    let primitive = match (op.opcode, &op.operand) {
        (0x02..=0x08, _) | (0x10..=0x11, Operand::Immediate(_)) => Primitive::Int,
        (0x09..=0x0a, _) => Primitive::Long,
        (0x0b..=0x0d, _) => Primitive::Float,
        (0x0e..=0x0f, _) => Primitive::Double,
        (0x12..=0x13, Operand::Constant(index)) => match pool.get(*index).ok()? {
            Constant::Integer(_) => Primitive::Int,
            Constant::Float(_) => Primitive::Float,
            _ => return None,
        },
        (0x14, Operand::Constant(index)) => match pool.get(*index).ok()? {
            Constant::Long(_) => Primitive::Long,
            Constant::Double(_) => Primitive::Double,
            _ => return None,
        },
        _ => return None,
    };
    Some(Type::Primitive(primitive))
}

fn permitted_prefix(
    instructions: &[Instruction],
    consumed: usize,
    permits: &impl Fn(usize, &Instruction) -> bool,
) -> bool {
    instructions[..consumed].iter().enumerate().all(|(index, op)| {
        permits(index, op) && (index == 0 || {
            let prev = &instructions[index - 1];
            prev.offset.checked_add(prev.len) == Some(op.offset)
        })
    })
}

fn find_store(
    ops: &[Instruction],
    mut cursor: usize,
    allow_dup: bool,
) -> Option<(&Instruction, usize, Option<u8>)> {
    let narrow = (0x91..=0x93).contains(&ops.get(cursor)?.opcode).then(|| {
        let op = ops[cursor].opcode;
        cursor += 1;
        op
    });
    if allow_dup && matches!(ops.get(cursor)?.opcode, 0x59..=0x5e) {
        cursor += 1;
    }
    Some((ops.get(cursor)?, cursor + 1, narrow))
}

fn is_one(value: &Expr) -> bool {
    matches!(value.source, Source::Integer(1) | Source::NumericOne)
}
