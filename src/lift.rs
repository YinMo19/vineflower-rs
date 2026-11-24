// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! Lowers JVM values into Java expressions, materializing stack values when
//! the JVM's evaluation schedule cannot otherwise be represented in Java.

mod anonymous;
mod concat;
mod dynamic;
mod expr;
mod generics;
mod literal;
mod locals;
mod members;
mod nested;
mod numeric;
mod operations;

pub(crate) use anonymous::{AnonymousSite, AnonymousSites};
pub(crate) use literal::{constant_literal, constant_literal_with_options, string_literal};
pub(crate) use dynamic::source_method_name;

#[cfg(test)]
mod tests;

use std::{cell::RefCell, collections::BTreeSet, rc::Rc};

use crate::{
    ClassGroup,
    bytecode::{Instruction, Operand},
    classfile::{
        BootstrapMethod, ClassError, ClassFile, Code, Constant, Member, StackMapError,
        TypeTarget, VerificationType, initial_stack_map_locals,
    },
    descriptor::{DescriptorError, MethodDescriptor, Primitive, Type},
    legacy::NormalizedCode,
    naming::MemberRenames,
    options::Options,
};

use self::{
    expr::{Category, Expr, Order, Source},
    locals::Locals,
};

#[derive(Debug, thiserror::Error)]
pub(crate) enum LiftError {
    #[error(transparent)]
    Class(#[from] ClassError),
    #[error(transparent)]
    Descriptor(#[from] DescriptorError),
    #[error(transparent)]
    StackMap(#[from] StackMapError),
    #[error("cannot render bytecode type annotation: {0}")]
    TypeAnnotation(#[source] Box<dyn std::error::Error + Send + Sync>),
    #[error("unsupported opcode {opcode:#04x} at bytecode offset {offset}: {reason}")]
    Unsupported {
        offset: u32,
        opcode: u8,
        reason: &'static str,
    },
    #[error("invalid operand stack at bytecode offset {offset}: {reason}")]
    InvalidStack { offset: u32, reason: &'static str },
    #[error("invalid local slot {index} at bytecode offset {offset}: {reason}")]
    InvalidLocal {
        offset: u32,
        index: u16,
        reason: &'static str,
    },
    #[error("invalid instruction operand at bytecode offset {offset}: {reason}")]
    InvalidOperand { offset: u32, reason: &'static str },
    #[error("constant pool entry {0} has no Java literal representation")]
    UnrepresentableConstant(u16),
}

pub(crate) enum Effect {
    None,
    Statement(String),
    FieldAssignment {
        target: String,
        value: String,
    },
    Branch {
        target: u32,
        when_true: String,
        when_false: String,
    },
    Jump(u32),
    Return(Option<String>),
    Throw(String),
    Switch {
        selector: String,
    },
}

pub(crate) type DynamicHelpers = Rc<RefCell<BTreeSet<(u16, u16)>>>;
type CodeTypeRenderer<'c> = dyn Fn(&Type, TypeTarget) -> Result<Option<String>, LiftError> + 'c;


#[derive(Clone)]
pub(crate) struct Machine<'a, 'c> {
    class: &'c ClassFile<'a>,
    group: Option<&'c ClassGroup<'a>>,
    renames: Option<&'c MemberRenames>,
    normalized: Option<&'c NormalizedCode>,
    method: &'c Member<'a>,
    code: &'c Code<'a>,
    descriptor: &'c MethodDescriptor,
    options: &'c Options,
    class_name: &'c dyn Fn(&str) -> String,
    owner: &'c str,
    super_class: Option<&'c str>,
    method_name: &'c str,
    locals: Locals<'c>,
    max_stack: u32,
    stack_slots: u32,
    stack: Vec<Expr>,
    prelude: Vec<String>,
    bootstrap: Option<std::rc::Rc<[BootstrapMethod]>>,
    dynamic_helpers: Option<DynamicHelpers>,
    anonymous_sites: Option<AnonymousSites>,
    code_type_renderer: Option<&'c CodeTypeRenderer<'c>>,
    lambda_depth: u8,
    initialized_this: bool,
    opcode: u8,
    offset: u32,
}

impl<'a, 'c> Machine<'a, 'c> {
    pub(crate) fn new(
        class: &'c ClassFile<'a>,
        method: &'c Member<'a>,
        code: &'c Code<'a>,
        descriptor: &'c MethodDescriptor,
        options: &'c Options,
        class_name: &'c dyn Fn(&str) -> String,
    ) -> Result<Self, LiftError> {
        let owner = class.pool.class_name(class.this_class)?;
        let super_class = (class.super_class != 0)
            .then(|| class.pool.class_name(class.super_class))
            .transpose()?;
        let method_name = class.pool.utf8(method.name_index)?;
        let locals = Locals::new(class, method, code, descriptor, options, owner)?;
        Ok(Self {
            class,
            group: None,
            renames: None,
            normalized: None,
            method,
            code,
            descriptor,
            options,
            class_name,
            owner,
            super_class,
            method_name,
            locals,
            max_stack: code.max_stack.into(),
            stack_slots: 0,
            stack: Vec::new(),
            prelude: Vec::new(),
            bootstrap: None,
            dynamic_helpers: None,
            anonymous_sites: None,
            code_type_renderer: None,
            lambda_depth: 0,
            initialized_this: method_name != "<init>" || super_class.is_none(),
            opcode: 0,
            offset: 0,
        })
    }

    pub(crate) fn with_group(mut self, group: &'c ClassGroup<'a>) -> Self {
        self.group = Some(group);
        self
    }

    pub(crate) fn set_code_type_renderer(&mut self, renderer: &'c CodeTypeRenderer<'c>) {
        self.code_type_renderer = Some(renderer);
    }

    pub(crate) fn set_member_renames(&mut self, renames: &'c MemberRenames) {
        self.renames = Some(renames);
    }

    fn source_field_name<'n>(&'n self, owner: &str, name: &'n str, descriptor: &str) -> &'n str {
        self.renames.map_or(name, |plan| plan.field_name(owner, name, descriptor))
    }

    pub(crate) fn with_normalized_offsets(mut self, normalized: &'c NormalizedCode) -> Self {
        self.normalized = Some(normalized);
        self
    }

    fn debug_offset(&self, offset: u32) -> u32 {
        self.normalized.and_then(|code| code.source_offset(offset)).unwrap_or(offset)
    }

    pub(crate) fn set_dynamic_helpers(&mut self, helpers: DynamicHelpers) {
        self.dynamic_helpers = Some(helpers);
    }

    pub(crate) fn render_catch_type(&self, catch_type: u16) -> Result<String, LiftError> {
        Ok((self.class_name)(self.class.pool.class_name(catch_type)?))
    }

    pub(crate) fn exception_class(&self, index: u16) -> Result<&str, LiftError> {
        Ok(self.class.pool.class_name(index)?)
    }

    pub(crate) fn exception_member(&self, index: u16) -> Result<(&str, &str, &str), LiftError> {
        Ok(self.class.pool.member_ref(index)?)
    }

    pub(crate) fn is_auto_closeable(&self, owner: &str) -> bool {
        crate::hierarchy::is_assignable(self.group, self.options, owner, "java/lang/AutoCloseable")
    }

    pub(crate) fn caught_exception_stack_type(&self, handler_offset: u32) -> Result<Option<u16>, LiftError> {
        let initial = initial_stack_map_locals(self.class, self.method, self.descriptor)?;
        let mut caught = None;
        self.code.visit_stack_map_frames(&self.class.pool, &initial, None, |frame| {
            if u32::from(frame.offset) == handler_offset
                && let [VerificationType::Object(index)] = frame.stack
            {
                caught = Some(*index);
            }
        })?;
        Ok(caught)
    }

    pub(crate) fn parameter_names(&self) -> &[String] {
        self.locals.parameters()
    }

    pub(crate) fn stack_is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub(crate) fn this_is_initialized(&self) -> bool {
        self.initialized_this
    }

    pub(crate) fn keeps_locals_of(&self, baseline: &Self) -> bool {
        self.initialized_this == baseline.initialized_this && self.locals.keeps(&baseline.locals)
    }

    pub(crate) fn same_locals(&self, other: &Self) -> bool {
        self.initialized_this == other.initialized_this && self.locals.same_as(&other.locals)
    }

    pub(crate) fn discard_branch_locals(&mut self, baseline: &Self) -> bool {
        self.stack_is_empty()
            && baseline.stack_is_empty()
            && self.initialized_this == baseline.initialized_this
            && self.locals.discard_branch_only(&baseline.locals)
    }

    pub(crate) fn take_prelude(&mut self) -> Vec<String> {
        std::mem::take(&mut self.prelude)
    }

    pub(crate) fn take_monitor_lock(&mut self, op: &Instruction) -> Result<String, LiftError> {
        self.offset = op.offset;
        self.opcode = op.opcode;
        self.lower_pending_comparison()?;
        let lock = self.pop_category(Category::Ref)?;
        if !self.stack_is_empty() {
            return Err(self.unsupported("pending operand across synchronized entry"));
        }
        self.before_statement(lock.order)?;
        Ok(if matches!(lock.source, Source::Null) {
            format!("(Object){}", lock.text)
        } else {
            lock.text
        })
    }

    pub(crate) fn step(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        self.offset = op.offset;
        self.opcode = op.opcode;
        if !matches!(op.opcode, 0x00 | 0x99..=0x9e) {
            self.lower_pending_comparison()?;
        }
        match op.opcode {
            0x00 => {}
            0x01 => self.push(Expr {
                source: Source::Null,
                ..Expr::atom(object_type(), "null".into())
            })?,
            0x02..=0x08 => self.push(Expr::integer(i32::from(op.opcode) - 3))?,
            0x09..=0x0a => self.push(Expr::literal(
                Type::Primitive(Primitive::Long),
                format!("{}L", op.opcode - 0x09),
            ))?,
            0x0b..=0x0d => self.push(Expr::literal(
                Type::Primitive(Primitive::Float),
                format!("{}.0F", op.opcode - 0x0b),
            ))?,
            0x0e..=0x0f => self.push(Expr::literal(
                Type::Primitive(Primitive::Double),
                format!("{}.0", op.opcode - 0x0e),
            ))?,
            0x10..=0x11 => {
                let Operand::Immediate(value) = op.operand else {
                    return Err(self.invalid_operand("expected an integer immediate"));
                };
                self.push(Expr::integer(value))?;
            }
            0x12..=0x14 => self.load_constant(op)?,
            0x15..=0x19 => {
                self.load(self.local_index(op)?, Category::for_local(op.opcode - 0x15))?
            }
            0x1a..=0x2d => {
                let relative = op.opcode - 0x1a;
                self.load(u16::from(relative % 4), Category::for_local(relative / 4))?;
            }
            0x2e..=0x35 => self.array_load(op.opcode - 0x2e)?,
            0x36..=0x3a => {
                return self.store(
                    op,
                    self.local_index(op)?,
                    Category::for_local(op.opcode - 0x36),
                );
            }
            0x3b..=0x4e => {
                let relative = op.opcode - 0x3b;
                return self.store(
                    op,
                    u16::from(relative % 4),
                    Category::for_local(relative / 4),
                );
            }
            0x4f..=0x56 => return self.array_store(op.opcode - 0x4f),
            0x57 => self.discard(1)?,
            0x58 => self.discard(2)?,
            0x59..=0x5e => {
                let relative = op.opcode - 0x59;
                self.duplicate(1 + relative / 3, relative % 3)?;
            }
            0x5f => self.swap()?,
            0x60..=0x83 => self.arithmetic(op.opcode)?,
            0x84 => {
                let Operand::Increment { index, amount } = op.operand else {
                    return Err(self.invalid_operand("expected iinc slot and delta"));
                };
                return self.increment(index, amount);
            }
            0x85..=0x93 => self.convert(op.opcode - 0x85)?,
            0x94..=0x98 => self.compare(op.opcode - 0x94)?,
            0x99..=0xa6 | 0xc6..=0xc7 => return self.conditional(op),
            0xa7 | 0xc8 => return Ok(Effect::Jump(self.target(op)?)),
            0xaa..=0xab => {
                if !matches!(op.operand, Operand::Switch { .. }) {
                    return Err(self.invalid_operand("expected switch targets"));
                }
                let value = self.pop_category(Category::Int)?;
                return Ok(Effect::Switch {
                    selector: self.as_int(value).text,
                });
            }
            0xac..=0xb1 => return self.return_value(op.opcode),
            0xb2..=0xb5 => return self.field(op),
            0xb6..=0xb9 => return self.invoke(op),
            0xba => return self.invoke_dynamic(op),
            0xbb => {
                let ty = self.class_type(self.constant_index(op)?)?;
                if !matches!(ty, Type::Object(_)) {
                    return Err(self.invalid_operand("new requires a class type"));
                }
                self.push(Expr {
                    source: Source::New(self.offset),
                    ..Expr::atom(ty, String::new())
                })?;
            }
            0xbc | 0xbd | 0xc5 => self.new_array(op)?,
            0xbe => self.array_length()?,
            0xbf => {
                let value = self.pop_category(Category::Ref)?;
                self.before_statement(value.order)?;
                self.stack.clear();
                self.stack_slots = 0;
                return Ok(Effect::Throw(value.text));
            }
            0xc0..=0xc1 => self.type_test(op)?,
            0xa8 | 0xa9 | 0xc9 => return Err(self.unsupported("legacy jsr/ret subroutines")),
            0xc2 | 0xc3 => {
                return Err(self
                    .unsupported("monitor operations require synchronized-region reconstruction"));
            }
            _ => return Err(self.unsupported("unrecognized JVM instruction")),
        }
        Ok(Effect::None)
    }

    fn load_constant(&mut self, op: &Instruction) -> Result<(), LiftError> {
        let index = self.constant_index(op)?;
        let constant = self.class.pool.get(index)?;
        let named = || {
            (!self.options.keep_literals)
                .then(|| numeric::named(constant, None, self.class_name)).flatten()
        };
        let value = match constant {
            Constant::Integer(value) => {
                if let Some(named) = named() {
                    Expr {
                        source: Source::Integer(*value),
                        precedence: named.precedence,
                        ..Expr::literal(expr::INT, named.text)
                    }
                } else {
                    Expr::integer(*value)
                }
            }
            Constant::Long(value) => numeric::expression(Primitive::Long, named(), || format!("{value}L")),
            Constant::Float(value) if value.is_nan() && value.to_bits() != f32::NAN.to_bits() => {
                let class = (self.class_name)("java/lang/Float");
                Expr {
                    statement: true,
                    ..self.expression(
                        Type::Primitive(Primitive::Float),
                        format!("{class}.intBitsToFloat(0x{:08x})", value.to_bits()),
                        expr::PRIMARY,
                        [],
                        true,
                    )?
                }
            }
            Constant::Double(value) if value.is_nan() && value.to_bits() != f64::NAN.to_bits() => {
                let class = (self.class_name)("java/lang/Double");
                Expr {
                    statement: true,
                    ..self.expression(
                        Type::Primitive(Primitive::Double),
                        format!("{class}.longBitsToDouble(0x{:016x}L)", value.to_bits()),
                        expr::PRIMARY,
                        [],
                        true,
                    )?
                }
            }
            Constant::Float(value) => numeric::expression(Primitive::Float, named(), || literal::float_literal(*value)),
            Constant::Double(value) => numeric::expression(Primitive::Double, named(), || literal::double_literal(*value)),
            Constant::String(_) => Expr::literal(
                Type::Object("java/lang/String".into()),
                constant_literal(&self.class.pool, index, None, self.options.ascii_strings)?,
            ),
            Constant::Class(_) => {
                let ty = self.class_type(index)?;
                self.expression(
                    Type::Object("java/lang/Class".into()),
                    format!("{}.class", self.render_type(&ty)),
                    expr::PRIMARY,
                    [],
                    true,
                )?
            }
            Constant::Dynamic { .. } => self.dynamic_constant(index)?,
            Constant::MethodType(_) | Constant::MethodHandle { .. } => {
                return Err(
                    self.unsupported("method handle/type constants have no direct Java expression")
                );
            }
            _ => return Err(self.invalid_operand("ldc requires a loadable constant")),
        };
        if (value.ty.slots() == 2) != (op.opcode == 0x14) {
            return Err(self.invalid_operand("constant width does not match ldc variant"));
        }
        self.push(value)
    }

    fn return_value(&mut self, opcode: u8) -> Result<Effect, LiftError> {
        if !self.initialized_this {
            return Err(self.invalid_stack("constructor returns before initializing this"));
        }
        let expected = &self.descriptor.return_type;
        let value = if opcode == 0xb1 {
            if *expected != Type::Void {
                return Err(self.invalid_stack("void return in a nonvoid method"));
            }
            None
        } else {
            let value = self.pop_category(Category::for_local(opcode - 0xac))?;
            Some(self.coerce(value, expected, false)?)
        };
        self.before_statement(value.as_ref().and_then(|value| value.order))?;
        self.stack.clear();
        self.stack_slots = 0;
        Ok(Effect::Return(value.map(|value| value.text)))
    }

    fn push(&mut self, value: Expr) -> Result<(), LiftError> {
        let width = u32::from(value.ty.slots());
        if width == 0 {
            return Err(self.invalid_stack("attempted to push void"));
        }
        if width + self.stack_slots > self.max_stack {
            return Err(self.invalid_stack("operand stack exceeds max_stack"));
        }
        self.stack.push(value);
        self.stack_slots += width;
        Ok(())
    }

    fn pop_raw(&mut self) -> Result<Expr, LiftError> {
        let value = self
            .stack
            .pop()
            .ok_or_else(|| self.invalid_stack("stack underflow"))?;
        self.stack_slots -= u32::from(value.ty.slots());
        Ok(value)
    }

    fn pop_category(&mut self, category: Category) -> Result<Expr, LiftError> {
        let value = self.pop_raw()?;
        if Category::of(&value.ty) != Some(category) {
            return Err(self.invalid_stack("operand category does not match the opcode"));
        }
        if value.is_uninitialized(self.initialized_this) {
            return Err(self.invalid_stack("uninitialized receiver used before invokespecial"));
        }
        Ok(value)
    }

    /// Number of complete stack values in a group of exactly `width` slots.
    fn group(&self, end: usize, mut width: u8) -> Result<usize, LiftError> {
        let mut start = end;
        while width != 0 {
            start = start
                .checked_sub(1)
                .ok_or_else(|| self.invalid_stack("stack underflow"))?;
            width = width
                .checked_sub(self.stack[start].ty.slots() as u8)
                .ok_or_else(|| self.invalid_stack("stack operation splits a category-2 value"))?;
        }
        Ok(start)
    }

    fn duplicate(&mut self, width: u8, beneath: u8) -> Result<(), LiftError> {
        let end = self.stack.len();
        let start = self.group(end, width)?;
        let insert = self.group(start, beneath)?;
        if self.stack_slots + u32::from(width) > self.max_stack {
            return Err(self.invalid_stack("dup exceeds max_stack"));
        }
        if self.stack[start..]
            .iter()
            .any(|value| value.order.is_some())
        {
            self.freeze_stack(None)?;
        }
        self.stack.extend_from_within(start..end);
        self.stack[insert..].rotate_right(end - start);
        self.stack_slots += u32::from(width);
        Ok(())
    }

    fn swap(&mut self) -> Result<(), LiftError> {
        let top = self.group(self.stack.len(), 1)?;
        let lower = self.group(top, 1)?;
        if self.stack[top].order.is_some() && self.stack[lower].order.is_some() {
            self.freeze_stack(None)?;
        }
        self.stack.swap(top, lower);
        Ok(())
    }

    fn discard(&mut self, width: u8) -> Result<(), LiftError> {
        let start = self.group(self.stack.len(), width)?;
        let top = self.pop_raw()?;
        let second = if self.stack.len() > start {
            Some(self.pop_raw()?)
        } else {
            None
        };
        let mut values = [second, Some(top)];
        if values
            .iter()
            .flatten()
            .any(|value| matches!(value.source, Source::New(_)))
        {
            return Err(self.unsupported("discard of an allocation before its constructor"));
        }
        if values.iter().flatten().any(|value| value.observable) {
            let order = self.order_of(values.iter().flatten(), false)?;
            self.before_statement(order)?;
            for value in values.iter_mut().flatten().filter(|value| value.observable) {
                if value.statement {
                    self.prelude.push(format!("{};", value.text));
                } else {
                    self.spill(value);
                }
            }
        }
        Ok(())
    }

    fn spill(&mut self, value: &mut Expr) {
        let name = self.locals.temporary(self.debug_offset(self.offset));
        let ty = self.render_type(&value.ty);
        self.prelude.push(format!("{ty} {name} = {};", value.text));
        value.text = name;
        value.precedence = expr::PRIMARY;
        value.source = Source::Plain;
        value.order = None;
        value.observable = false;
        value.statement = false;
        value.constant = false;
    }

    fn freeze_stack(&mut self, following: Option<Order>) -> Result<Option<Order>, LiftError> {
        if self
            .stack
            .iter()
            .any(|value| value.is_uninitialized(self.initialized_this))
            || !self.initialized_this
        {
            return Err(self.unsupported("stack spills across an unfinished constructor call"));
        }
        let prior = self.order_of(&self.stack, false)?;
        if let Some(following) = following {
            self.join_order(prior, following)?;
        }
        if prior.is_some() {
            let mut stack = std::mem::take(&mut self.stack);
            for value in stack.iter_mut().filter(|value| value.order.is_some()) {
                self.spill(value);
            }
            self.stack = stack;
        }
        Ok(prior)
    }

    fn before_statement(&mut self, order: Option<Order>) -> Result<(), LiftError> {
        self.freeze_stack(order).map(|_| ())
    }

    fn freeze_values(&mut self, values: &mut [Expr]) -> Result<(), LiftError> {
        let order = self.order_of(&*values, false)?;
        if order.is_some() {
            self.freeze_stack(order)?;
            for value in values.iter_mut().filter(|value| value.order.is_some()) {
                self.spill(value);
            }
        }
        Ok(())
    }

    fn class_type(&self, index: u16) -> Result<Type, LiftError> {
        let name = self.class.pool.class_name(index)?;
        if name.starts_with('[') {
            Ok(Type::parse(name)?)
        } else {
            Ok(Type::Object(name.into()))
        }
    }

    fn render_type(&self, ty: &Type) -> String {
        ty.render(self.class_name)
    }

    fn render_code_type(&self, ty: &Type, target: TypeTarget) -> Result<Option<String>, LiftError> {
        self.code_type_renderer.map_or(Ok(None), |render| render(ty, target))
    }

    fn known_assignable(&self, from: &Type, to: &Type) -> bool {
        if from == to {
            return true;
        }
        if let (Type::Object(from), Type::Object(to)) = (from, to)
            && crate::hierarchy::is_assignable(self.group, self.options, from, to)
        {
            return true;
        }
        match (from, to) {
            (Type::Object(_) | Type::Array(_), Type::Object(to)) if to == "java/lang/Object" => {
                true
            }
            (Type::Object(from), Type::Object(to)) if from == self.owner => {
                self.super_class == Some(to)
                    || self.class.interfaces.iter().any(|index| {
                        self.class
                            .pool
                            .class_name(*index)
                            .is_ok_and(|name| name == to)
                    })
            }
            (Type::Array(_), Type::Object(to)) => {
                matches!(to.as_str(), "java/lang/Cloneable" | "java/io/Serializable")
            }
            (Type::Array(from), Type::Array(to)) => self.known_assignable(from, to),
            _ => false,
        }
    }

    fn invalid_stack(&self, reason: &'static str) -> LiftError {
        LiftError::InvalidStack {
            offset: self.offset,
            reason,
        }
    }

    fn invalid_local(&self, index: u16, reason: &'static str) -> LiftError {
        LiftError::InvalidLocal {
            offset: self.offset,
            index,
            reason,
        }
    }

    fn invalid_operand(&self, reason: &'static str) -> LiftError {
        LiftError::InvalidOperand {
            offset: self.offset,
            reason,
        }
    }

    fn unsupported(&self, reason: &'static str) -> LiftError {
        LiftError::Unsupported {
            offset: self.offset,
            opcode: self.opcode,
            reason,
        }
    }

    fn local_index(&self, op: &Instruction) -> Result<u16, LiftError> {
        match op.operand {
            Operand::Local(index) => Ok(index),
            _ => Err(self.invalid_operand("expected a local slot")),
        }
    }

    fn constant_index(&self, op: &Instruction) -> Result<u16, LiftError> {
        match op.operand {
            Operand::Constant(index) => Ok(index),
            _ => Err(self.invalid_operand("expected a constant pool index")),
        }
    }

    fn target(&self, op: &Instruction) -> Result<u32, LiftError> {
        match op.operand {
            Operand::Branch(target) => Ok(target),
            _ => Err(self.invalid_operand("expected a branch target")),
        }
    }
}

fn object_type() -> Type {
    Type::Object("java/lang/Object".into())
}
