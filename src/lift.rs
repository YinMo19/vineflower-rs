// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! Lowers JVM values into Java expressions, materializing stack values when
//! the JVM's evaluation schedule cannot otherwise be represented in Java.

mod anonymous;
mod array_initializer;
mod assignment_expr;
mod concat;
mod condy;
mod booleans;
mod boxing;
mod constructor;
mod dynamic;
mod enum_constants;
pub(crate) mod enum_switch;
mod expr;
mod generics;
mod java_templates;
mod literal;
mod locals;
mod members;
mod nested;
mod numeric;
mod operations;
mod overloads;
pub(crate) mod pattern_dispatch;
pub(crate) mod qualified_new;
mod switch_expression;

pub(crate) use anonymous::{AnonymousBindings, AnonymousSite, AnonymousSites};
pub(crate) use booleans::{BooleanCondition, BooleanFact, BooleanSelection};
pub(crate) use dynamic::source_method_name;
pub(crate) use literal::{constant_literal, constant_literal_with_options, string_literal};
pub(crate) use locals::IfPatternLocal;

#[cfg(test)]
mod tests;

use std::{cell::RefCell, collections::{BTreeMap, BTreeSet}, rc::Rc};

use crate::{
    ClassGroup,
    bytecode::{Instruction, Operand},
    classfile::{
        BootstrapMethod, ClassError, ClassFile, Code, Constant, ConstantPool, Member,
        LocalTypeRange, StackMapError, TypeTarget, VerificationType, initial_stack_map_locals,
    },
    descriptor::{DescriptorError, MethodDescriptor, Primitive, Type},
    emit::type_annotations::RenderType,
    legacy::NormalizedCode,
    naming::MemberRenames,
    options::Options,
    source_text::Document,
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
    Statement(Document),
    FieldAssignment {
        target: Document,
        value: Document,
    },
    Branch {
        target: u32,
        when_true: Document,
        when_false: Document,
    },
    Jump(u32),
    Return(Option<Document>),
    Throw(Document),
    Switch {
        selector: Document,
    },
}

pub(crate) type DynamicHelpers = Rc<RefCell<BTreeSet<(u16, u16)>>>;
type CodeTypeRenderer<'c> =
    dyn Fn(RenderType<'_>, CodeTypeSite) -> Result<Option<Document>, LiftError> + 'c;

pub(crate) enum CodeTypeSite {
    Exact(TypeTarget),
    Local(LocalTypeRange),
}

impl CodeTypeSite {
    pub(crate) fn matches(&self, target: &TypeTarget) -> bool {
        match (self, target) {
            (Self::Exact(expected), actual) => expected == actual,
            (Self::Local(range), TypeTarget::LocalVariable(ranges) | TypeTarget::ResourceVariable(ranges)) =>
                ranges.contains(range),
            _ => false,
        }
    }
}

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
    prelude: Vec<Document>,
    bootstrap: Option<std::rc::Rc<[BootstrapMethod]>>,
    dynamic_helpers: Option<DynamicHelpers>,
    anonymous_sites: Option<AnonymousSites>,
    anonymous_bindings: Option<AnonymousBindings>,
    anonymous_source: Option<&'c [Instruction]>,
    code_type_renderer: Option<&'c CodeTypeRenderer<'c>>,
    lambda_depth: u8,
    array_probe_depth: u8,
    initialized_this: bool,
    early_final_fields: BTreeMap<usize, bool>,
    instruction_has_source: bool,
    boolean_condition: BooleanCondition,
    boolean_return: Option<BooleanFact>,
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
            anonymous_bindings: None,
            anonymous_source: None,
            code_type_renderer: None,
            lambda_depth: 0,
            array_probe_depth: 0,
            initialized_this: method_name != "<init>" || super_class.is_none(),
            early_final_fields: BTreeMap::new(),
            instruction_has_source: false,
            boolean_condition: BooleanCondition::UNKNOWN,
            boolean_return: None,
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
        self.renames
            .map_or(name, |plan| plan.field_name(owner, name, descriptor))
    }

    pub(crate) fn with_normalized_offsets(mut self, normalized: &'c NormalizedCode) -> Self {
        self.normalized = Some(normalized);
        self
    }

    fn debug_offset(&self, offset: u32) -> u32 {
        self.normalized
            .and_then(|code| code.source_offset(offset))
            .unwrap_or(offset)
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

    pub(crate) fn caught_exception_stack_type(
        &self,
        handler_offset: u32,
    ) -> Result<Option<u16>, LiftError> {
        let initial = initial_stack_map_locals(self.class, self.method, self.descriptor)?;
        let mut caught = None;
        self.code
            .visit_stack_map_frames(&self.class.pool, &initial, None, |frame| {
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

    pub(crate) fn field_receiver_is_this(&self) -> bool {
        matches!(self.stack.as_slice(), [receiver, _] if matches!(receiver.source, Source::This))
    }

    pub(crate) fn this_is_initialized(&self) -> bool {
        self.initialized_this
    }

    pub(crate) fn keeps_locals_of(&self, baseline: &Self) -> bool {
        self.initialized_this == baseline.initialized_this && self.locals.keeps(&baseline.locals)
    }

    pub(crate) fn same_locals(&self, other: &Self) -> bool {
        self.initialized_this == other.initialized_this
            && self.early_final_fields == other.early_final_fields
            && self.locals.same_as(&other.locals)
    }

    pub(crate) fn discard_branch_locals(&mut self, baseline: &Self) -> bool {
        self.stack_is_empty()
            && baseline.stack_is_empty()
            && self.initialized_this == baseline.initialized_this
            && self.early_final_fields == baseline.early_final_fields
            && self.locals.discard_branch_only(&baseline.locals)
    }

    pub(crate) fn take_prelude(&mut self) -> Vec<Document> {
        std::mem::take(&mut self.prelude)
    }

    pub(crate) fn take_monitor_lock(&mut self, op: &Instruction) -> Result<Document, LiftError> {
        let lock = self.take_region_reference(op)?;
        Ok(if matches!(lock.source, Source::Null) {
            let mut text = lock.text;
            text.prepend_str(&format!("({})", (self.class_name)("java/lang/Object")));
            text
        } else {
            lock.text
        })
    }

    pub(crate) fn constant_pool(&self) -> &'c ConstantPool<'a> {
        &self.class.pool
    }

    pub(crate) fn switch_requires_case_scopes(&self) -> bool {
        // Regular locals already share a method-wide unique name allocator.
        // Local classes preserve their JVM source names and can shadow each
        // other across explicit case blocks.
        self.options.decompile_inner
            && self.group.is_some_and(|group| {
                group.children(self.owner).any(|(_, child)| {
                    matches!(child.kind, crate::context::NestedKind::Local(_))
                        && child.method.as_ref().is_some_and(|(name, descriptor)| {
                            name == self.method_name
                                && self.class.pool.utf8(self.method.descriptor_index)
                                    .is_ok_and(|current| descriptor == current)
                        })
                })
            })
    }

    pub(crate) fn ascii_strings(&self) -> bool {
        self.options.ascii_strings
    }

    pub(crate) fn take_string_switch_selector(
        &mut self,
        op: &Instruction,
    ) -> Result<Document, LiftError> {
        self.offset = op.offset;
        self.opcode = op.opcode;
        self.lower_pending_comparison()?;
        let selector = self.pop_category(Category::Ref)?;
        Ok(self
            .coerce(selector, &Type::Object("java/lang/String".into()), true)?
            .text)
    }

    fn take_region_reference(&mut self, op: &Instruction) -> Result<Expr, LiftError> {
        self.offset = op.offset;
        self.opcode = op.opcode;
        self.lower_pending_comparison()?;
        let value = self.pop_category(Category::Ref)?;
        if !self.stack_is_empty() {
            return Err(self.unsupported("pending operand across structured region entry"));
        }
        self.before_statement(value.order)?;
        Ok(value)
    }

    pub(crate) fn take_assertion_detail(
        &mut self,
        constructor: &Instruction,
        allocation: u32,
        descriptor: &str,
    ) -> Result<Option<Document>, LiftError> {
        self.offset = constructor.offset;
        self.opcode = constructor.opcode;
        self.lower_pending_comparison()?;
        let descriptor = MethodDescriptor::parse(descriptor)?;
        let detail = match descriptor.parameters.as_slice() {
            [] => None,
            [ty] => {
                let category = Category::of(ty).expect("a constructor parameter is not void");
                let value = self.pop_category(category)?;
                // An assert detail of reference type already selects the
                // Object constructor, including boxed values and null.
                Some(self.coerce(value, ty, category != Category::Ref)?.text)
            }
            _ => return Err(self.invalid_operand("assertion constructor arity")),
        };
        if !self.initialized_this
            || !self.prelude.is_empty()
            || !matches!(&self.stack[..], [receiver, thrown] if [receiver, thrown].into_iter().all(
                |value| matches!(value.source, Source::New(offset) if offset == allocation)
                    && matches!(&value.ty, Type::Object(name) if name == "java/lang/AssertionError")
            ))
        {
            return Err(
                self.invalid_stack("assertion constructor and throw need the same allocation")
            );
        }
        self.stack.clear();
        self.stack_slots = 0;
        Ok(detail)
    }

    pub(crate) fn instruction_has_source(&self) -> bool {
        self.instruction_has_source
    }

    pub(crate) fn step(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        self.offset = op.offset;
        self.opcode = op.opcode;
        // Stack management and the allocation half of `new` do not
        // correspond to standalone source tokens.
        self.instruction_has_source = !matches!(op.opcode, 0 | 0x57..=0x5f | 0xbb);
        if !matches!(op.opcode, 0x00 | 0x99..=0x9e) {
            self.lower_pending_comparison()?;
        }
        if matches!(op.opcode, 0x2e | 0x57 | 0xaa..=0xab | 0xb2 | 0xb6 | 0xb8)
            && let Some(action) = self.enum_switch_action(op.offset)
        {
            return match action {
                enum_switch::Action::Skip => {
                    // The int lookup is the source selector's dispatch;
                    // the helper array and ordinal call have no source.
                    self.instruction_has_source = op.opcode == 0x2e;
                    Ok(Effect::None)
                }
                enum_switch::Action::Switch(owner) => Ok(Effect::Switch {
                    selector: self.enum_switch_selector(owner)?,
                }),
                enum_switch::Action::Empty(owner) => self.empty_enum_switch(owner),
            };
        }
        match op.opcode {
            0x00 => {}
            0x01 => self.push(Expr {
                source: Source::Null,
                ..Expr::atom(object_type(), "null".into())
            })?,
            0x02..=0x08 => self.push(Expr::integer(i32::from(op.opcode) - 3))?,
            0x09..=0x0a => self.push(Expr::numeric_literal(
                Primitive::Long, format!("{}L", op.opcode - 0x09).into(), op.opcode == 0x0a,
            ))?,
            0x0b..=0x0d => self.push(Expr::numeric_literal(
                Primitive::Float, format!("{}.0F", op.opcode - 0x0b).into(), op.opcode == 0x0c,
            ))?,
            0x0e..=0x0f => self.push(Expr::numeric_literal(
                Primitive::Double, format!("{}.0", op.opcode - 0x0e).into(), op.opcode == 0x0f,
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
                    ..Expr::atom(ty, Document::new())
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
                .then(|| numeric::named(constant, None, self.class_name))
                .flatten()
        };
        let mut value = match constant {
            Constant::Integer(value) => {
                if let Some(named) = named() {
                    Expr {
                        source: Source::Integer(*value),
                        precedence: named.precedence,
                        ..Expr::literal(expr::INT, named.text.into())
                    }
                } else {
                    Expr::integer(*value)
                }
            }
            Constant::Long(value) => {
                numeric::expression(Primitive::Long, named(), || format!("{value}L"))
            }
            Constant::Float(value) if value.is_nan() && value.to_bits() != f32::NAN.to_bits() => {
                let class = (self.class_name)("java/lang/Float");
                Expr {
                    statement: true,
                    ..self.expression(
                        Type::Primitive(Primitive::Float),
                        format!("{class}.intBitsToFloat(0x{:08x})", value.to_bits()).into(),
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
                        format!("{class}.longBitsToDouble(0x{:016x}L)", value.to_bits()).into(),
                        expr::PRIMARY,
                        [],
                        true,
                    )?
                }
            }
            Constant::Float(value) => {
                numeric::expression(Primitive::Float, named(), || literal::float_literal(*value, true))
            }
            Constant::Double(value) => numeric::expression(Primitive::Double, named(), || {
                literal::double_literal(*value, true)
            }),
            Constant::String(_) => Expr::literal(
                Type::Object("java/lang/String".into()),
                constant_literal(&self.class.pool, index, None, self.options.ascii_strings)?.into(),
            ),
            Constant::Class(_) => {
                let ty = self.class_type(index)?;
                self.expression(
                    Type::Object("java/lang/Class".into()),
                    format!("{}.class", self.render_type(&ty)).into(),
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
        if match constant {
            Constant::Long(value) => *value == 1,
            Constant::Float(value) => *value == 1.0,
            Constant::Double(value) => *value == 1.0,
            _ => false,
        } {
            value.source = Source::NumericOne;
        }
        self.push(value)
    }

    fn return_value(&mut self, opcode: u8) -> Result<Effect, LiftError> {
        if !self.initialized_this {
            return Err(self.invalid_stack("constructor returns before initializing this"));
        }
        if self.early_final_fields.values().any(|definite| !definite) {
            return Err(self.invalid_stack("early final field is not assigned on every path"));
        }
        let expected = &self.descriptor.return_type;
        self.boolean_return = None;
        let value = if opcode == 0xb1 {
            if *expected != Type::Void {
                return Err(self.invalid_stack("void return in a nonvoid method"));
            }
            None
        } else {
            let value = self.pop_category(Category::for_local(opcode - 0xac))?;
            let constant = match value.source {
                Source::Integer(value) => Some(BooleanFact::constant(value & 1 != 0)),
                _ => None,
            };
            let value = self.coerce_assignment(value, expected)?;
            if *expected == expr::BOOLEAN && self.options.ternary_constant_simplification {
                self.boolean_return = constant.or_else(|| BooleanFact::operand(&value));
            }
            Some(value)
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
        if beneath == 0 {
            for (ordinal, value) in self.stack[start..end].iter_mut().enumerate() {
                value.alias.get_or_insert(assignment_expr::StackAlias {
                    instruction: self.offset,
                    ordinal: ordinal as u8,
                });
            }
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
                    value.text.push(';');
                    self.prelude.push(std::mem::take(&mut value.text));
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
        let mut assignment = std::mem::replace(&mut value.text, name.clone().into());
        assignment.surround(&format!("{ty} {name} = "), ";");
        self.prelude.push(assignment);
        value.precedence = expr::PRIMARY;
        value.source = Source::Plain;
        value.order = None;
        value.observable = false;
        value.statement = false;
        value.constant = false;
    }

    fn freeze_stack(&mut self, following: Option<Order>) -> Result<Option<Order>, LiftError> {
        if self.array_probe_depth != 0 {
            return Err(self.unsupported("array initializer element requires a spill"));
        }
        if self.stack.iter().any(|value| {
            // The raw constructor receiver is just an unordered marker for a
            // later putfield or invokespecial. Never materialize it, nor
            // move an open, potentially throwing allocation across a spill.
            value.is_uninitialized(self.initialized_this)
                && (!matches!(value.source, Source::This) || value.order.is_some())
        }) {
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

    fn type_document(&self, ty: &Type) -> Document {
        let rendered = self.render_type(ty);
        if !self.options.dump_text_tokens {
            return rendered.into();
        }
        let mut leaf = ty;
        let mut dimensions = 0;
        while let Type::Array(element) = leaf {
            leaf = element;
            dimensions += 1;
        }
        if let Type::Object(name) = leaf {
            let base_end = rendered.len() - dimensions * "[]".len();
            let mut document = Document::new();
            crate::emit::symbols::append_class(&mut document, &rendered[..base_end], name, true);
            document.push_str(&rendered[base_end..]);
            return document;
        }
        rendered.into()
    }

    fn render_code_type(
        &self,
        ty: &Type,
        target: TypeTarget,
    ) -> Result<Option<Document>, LiftError> {
        self.render_code_type_at(ty.into(), CodeTypeSite::Exact(target))
    }

    fn render_code_type_at(
        &self,
        ty: RenderType<'_>,
        site: CodeTypeSite,
    ) -> Result<Option<Document>, LiftError> {
        self.code_type_renderer.map_or(Ok(None), |render| render(ty, site))
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
