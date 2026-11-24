// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::ops::RangeInclusive;

use super::Local;
use crate::lift::{
    LiftError, Machine,
    expr::{BOOLEAN, Category, Expr, INT, Order, Source, TERNARY},
};
use crate::{bytecode::Instruction, descriptor::Type};

pub(crate) struct JoinCode {
    pub(crate) declarations: Vec<String>,
    pub(crate) arms: Vec<Vec<String>>,
}

impl JoinCode {
    fn new(arms: usize) -> Self {
        Self {
            declarations: Vec::new(),
            arms: vec![Vec::new(); arms],
        }
    }
}

pub(crate) struct LocalJoinCode {
    pub(crate) declarations: Vec<String>,
    pub(crate) arms: Vec<Vec<LocalCopy>>,
}

pub(crate) struct LocalCopy {
    pub(crate) statement: String,
    direct: Option<(String, String)>,
}

impl LocalCopy {
    /// If the source is an immediately preceding declaration, assign to the
    /// outer binding directly. Its RHS and bytecode mapping stay in place.
    pub(crate) fn fuse(&self, line: &mut String) -> bool {
        let Some((declaration, assignment)) = &self.direct else {
            return false;
        };
        if !line.starts_with(declaration) {
            return false;
        }
        line.replace_range(..declaration.len(), assignment);
        true
    }
}

pub(crate) struct HeldStack {
    original: Vec<(usize, Expr)>,
}

impl Machine<'_, '_> {
    pub(crate) fn control_order(
        &self,
        instruction: &Instruction,
    ) -> Result<Option<RangeInclusive<u32>>, LiftError> {
        let count = match instruction.opcode {
            0x99..=0x9e | 0xaa..=0xab | 0xc6..=0xc7 => 1,
            0x9f..=0xa6 => 2,
            _ => return Ok(None),
        };
        let values = &self.stack[self.stack.len().saturating_sub(count)..];
        let order = self.order_of(values, false)?;
        Ok(Some(
            order.map_or(instruction.offset, |order| order.first)..=instruction.offset,
        ))
    }

    /// Freeze expressions produced before a statement-form control transfer.
    /// If the transfer becomes an expression, the unchanged prefix can be
    /// restored provided the arms never referenced the temporary names.
    pub(crate) fn hold_control_stack(
        &mut self,
        control: &RangeInclusive<u32>,
    ) -> Result<Option<HeldStack>, LiftError> {
        if self.has_uninitialized_stack() || !self.stack.iter().any(|value| value.order.is_some()) {
            return Ok(None);
        }
        let original = self
            .stack
            .iter()
            .enumerate()
            .filter(|(_, value)| value.order.is_some())
            .map(|(index, value)| (index, value.clone()))
            .collect();
        self.freeze_control_stack(control)?;
        Ok(Some(HeldStack { original }))
    }

    pub(crate) fn freeze_control_stack(
        &mut self,
        control: &RangeInclusive<u32>,
    ) -> Result<(), LiftError> {
        self.freeze_stack(Some(Order::at(*control.start())))
            .map(|_| ())
    }

    pub(crate) fn has_uninitialized_stack(&self) -> bool {
        !self.initialized_this
            || self
                .stack
                .iter()
                .any(|value| value.is_uninitialized(self.initialized_this))
    }

    /// Join two expression-only arms without evaluating either arm eagerly.
    /// The unmodified stack prefix remains below the conditional result.
    pub(crate) fn merge_conditional_stack(
        &mut self,
        yes: &Self,
        no: &Self,
        condition: &str,
        inverse: &str,
        control: &RangeInclusive<u32>,
        held: Option<HeldStack>,
    ) -> Result<Option<bool>, LiftError> {
        let Some(prefix) = yes.stack.len().checked_sub(1) else {
            return Ok(None);
        };
        if prefix > self.stack.len()
            || no.stack.len() != yes.stack.len()
            || !yes.stack[..prefix]
                .iter()
                .zip(&self.stack)
                .all(|(a, b)| same_value(a, b))
            || !no.stack[..prefix]
                .iter()
                .zip(&self.stack)
                .all(|(a, b)| same_value(a, b))
            || (yes.stack.len() == self.stack.len()
                && self.same_control_stack(yes)
                && self.same_control_stack(no))
            || (held.is_none()
                && self.stack[prefix..].iter().any(|value| {
                    value.is_uninitialized(self.initialized_this) || value.order.is_some()
                }))
        {
            return Ok(None);
        }
        let yes = &yes.stack[prefix];
        let no = &no.stack[prefix];
        if [yes, no].into_iter().any(|value| {
            value.is_uninitialized(self.initialized_this)
                || matches!(value.source, Source::Comparison(_))
                || value
                    .order
                    .is_some_and(|order| order.first <= *control.end())
        }) {
            return Ok(None);
        }
        let Some(mut ty) = self.common_value_type(yes, no) else {
            return Ok(None);
        };
        let condition = predicate(condition);
        let (text, precedence) = match (&yes.source, &no.source) {
            (Source::Integer(1), Source::Integer(0)) => {
                ty = BOOLEAN;
                (condition.into_owned(), TERNARY)
            }
            (Source::Integer(0), Source::Integer(1)) => {
                ty = BOOLEAN;
                (inverse.to_owned(), TERNARY)
            }
            (_, Source::Integer(0)) if yes.ty == BOOLEAN => boolean_arm(&condition, yes, true),
            (_, Source::Integer(1)) if yes.ty == BOOLEAN => boolean_arm(inverse, yes, false),
            (Source::Integer(0), _) if no.ty == BOOLEAN => boolean_arm(inverse, no, true),
            (Source::Integer(1), _) if no.ty == BOOLEAN => boolean_arm(&condition, no, false),
            _ => {
                let yes = self.conditional_operand(yes, &ty, &no.ty)?;
                let no = self.conditional_operand(no, &ty, &yes.ty)?;
                (format!("{condition} ? {} : {}", yes.text, no.text), TERNARY)
            }
        };
        let mut original = held.filter(|held| {
            held.original.iter().all(|&(index, _)| {
                index < prefix && !text.contains(self.stack[index].text.as_str())
            })
        });
        for removed in self.stack.drain(prefix..) {
            self.stack_slots -= u32::from(removed.ty.slots());
        }
        if let Some(held) = &mut original {
            for (index, value) in held.original.drain(..) {
                self.stack[index] = value;
            }
        }
        self.push(Expr {
            precedence,
            order: Some(Order {
                first: *control.start(),
                last: [yes, no]
                    .into_iter()
                    .filter_map(|value| value.order.map(|order| order.last))
                    .max()
                    .unwrap_or(*control.end())
                    .max(*control.end()),
            }),
            // The condition itself may call or throw, even if the result is
            // discarded or neither branch expression has visible effects.
            observable: true,
            ..Expr::atom(ty, text)
        })?;
        Ok(Some(original.is_some()))
    }

    pub(in crate::lift) fn conditional_operand(
        &self,
        value: &Expr,
        ty: &Type,
        other: &Type,
    ) -> Result<Expr, LiftError> {
        if *ty == INT && value.ty != INT {
            let value = self.as_int(value.clone());
            if value.ty == INT {
                // A boolean-to-int expression itself uses a ternary. It is
                // legal in both Java ternary value positions without a cast.
                return Ok(value);
            }
            return self.cast(value, ty.clone(), false);
        }
        if Category::of(ty) == Some(Category::Ref)
            && &value.ty != other
            && &value.ty != ty
            && !matches!(value.source, Source::Null)
        {
            // Prevent Java from selecting a numeric conditional/unboxing for
            // two different wrapper classes; these are JVM reference values.
            return self.cast(value.clone(), ty.clone(), false);
        }
        self.coerce(value.clone(), ty, false)
    }

    pub(crate) fn same_control_stack(&self, other: &Self) -> bool {
        self.stack.len() == other.stack.len()
            && self
                .stack
                .iter()
                .zip(&other.stack)
                .all(|(a, b)| same_value(a, b))
    }

    pub(crate) fn merge_stack(
        &mut self,
        arms: &[&Self],
        offset: u32,
    ) -> Result<JoinCode, LiftError> {
        self.offset = offset;
        let mut code = JoinCode::new(arms.len());
        let Some(first) = arms.first() else {
            return Ok(code);
        };
        if arms.iter().any(|arm| arm.stack.len() != first.stack.len()) {
            return Err(self.invalid_stack("incompatible stack heights at control-flow join"));
        }
        if arms.iter().all(|arm| self.same_control_stack(arm)) {
            return Ok(code);
        }
        let mut slots = 0;
        let mut merged = Vec::with_capacity(first.stack.len());
        for index in 0..first.stack.len() {
            let exemplar = &first.stack[index];
            if let Some(baseline) = self.stack.get(index)
                && arms
                    .iter()
                    .all(|arm| same_value(baseline, &arm.stack[index]))
            {
                slots += u32::from(baseline.ty.slots());
                merged.push(baseline.clone());
                continue;
            }
            let mut ty = exemplar.ty.clone();
            let mut only_null = matches!(exemplar.source, Source::Null);
            for arm in arms {
                let value = &arm.stack[index];
                if value.is_uninitialized(arm.initialized_this)
                    || matches!(value.source, Source::Comparison(_))
                {
                    return Err(self.invalid_stack("unrepresentable operand at control-flow join"));
                }
                if matches!(value.source, Source::Null) && Category::of(&ty) == Some(Category::Ref)
                {
                    continue;
                }
                if only_null && Category::of(&value.ty) == Some(Category::Ref) {
                    only_null = false;
                    ty = value.ty.clone();
                } else {
                    ty = self.common_type(&ty, &value.ty).ok_or_else(|| {
                        self.invalid_stack("incompatible operand categories at control-flow join")
                    })?;
                }
            }
            let name = self.locals.temporary(self.debug_offset(offset));
            code.declarations
                .push(format!("{} {name};", self.render_type(&ty)));
            for (arm, assignments) in arms.iter().zip(&mut code.arms) {
                let value = arm.coerce(arm.stack[index].clone(), &ty, false)?;
                assignments.push(format!("{name} = {};", value.text));
            }
            slots += u32::from(ty.slots());
            merged.push(Expr::atom(ty, name));
        }
        // Edge assignments execute payloads in stack order. Reject a stack
        // whose still-deferred JVM evaluations cannot be written that way.
        for arm in arms {
            arm.order_of(&arm.stack, false)?;
        }
        self.stack = merged;
        self.stack_slots = slots;
        Ok(code)
    }

    /// Bind JVM operands that a loop backedge or switch fallthrough can
    /// replace before shared source code is entered again.
    pub(crate) fn bind_edge_stack(
        &mut self,
        offset: u32,
        before: Option<u32>,
    ) -> Result<Vec<String>, LiftError> {
        if self.stack.is_empty() {
            return Ok(Vec::new());
        }
        if self.has_uninitialized_stack()
            || self
                .stack
                .iter()
                .any(|value| matches!(value.source, Source::Comparison(_)))
        {
            return Err(self.invalid_stack("unrepresentable control-flow entry stack"));
        }
        let order = self.order_of(&self.stack, false)?;
        if let Some(before) = before {
            self.join_order(order, Order::at(before))?;
        }
        let offset = self.debug_offset(offset);
        let mut stack = std::mem::take(&mut self.stack);
        let mut declarations = Vec::with_capacity(stack.len());
        for value in &mut stack {
            let ty = self.render_type(&value.ty);
            let name = self.locals.temporary(offset);
            declarations.push(format!("{ty} {name} = {};", value.text));
            *value = Expr::atom(value.ty.clone(), name);
        }
        self.stack = stack;
        Ok(declarations)
    }

    pub(crate) fn update_edge_stack(
        &self,
        entry: &Self,
        offset: u32,
    ) -> Result<Vec<String>, LiftError> {
        if self.stack.len() != entry.stack.len() {
            return Err(self.invalid_stack("incompatible incoming stack height"));
        }
        self.order_of(&self.stack, false)?;
        let offset = self.debug_offset(offset);
        let mut updates = Vec::new();
        for (from, to) in self.stack.iter().zip(&entry.stack) {
            if same_value(from, to) {
                continue;
            }
            if from.is_uninitialized(self.initialized_this)
                || matches!(from.source, Source::Comparison(_))
                || !(self.known_assignable(&from.ty, &to.ty)
                    || (Category::of(&from.ty) == Some(Category::Int)
                        && from.fits_int_local(&to.ty))
                    || (Category::of(&to.ty) == Some(Category::Ref)
                        && matches!(from.source, Source::Null)))
            {
                return Err(self.invalid_stack("incompatible incoming operand"));
            }
            let value = self.coerce(from.clone(), &to.ty, false)?;
            updates.push((to, value));
        }
        let mut statements = Vec::with_capacity(updates.len() * 2);
        if updates.len() == 1 {
            let (to, value) = updates.pop().unwrap();
            statements.push(format!("{} = {};", to.text, value.text));
        } else {
            // Edge updates are parallel copies. A permutation must not
            // overwrite an old operand before another RHS has read it.
            let mut copies = Vec::with_capacity(updates.len());
            for (to, value) in updates {
                let temporary = self.locals.temporary(offset);
                statements.push(format!(
                    "{} {temporary} = {};",
                    self.render_type(&to.ty),
                    value.text
                ));
                copies.push(format!("{} = {temporary};", to.text));
            }
            statements.extend(copies);
        }
        Ok(statements)
    }

    pub(crate) fn merge_locals(
        &mut self,
        arms: &[&Self],
        offset: u32,
        mut live: impl FnMut(u16) -> bool,
    ) -> Result<LocalJoinCode, LiftError> {
        self.offset = offset;
        let mut code = LocalJoinCode {
            declarations: Vec::new(),
            arms: (0..arms.len()).map(|_| Vec::new()).collect(),
        };
        if arms
            .iter()
            .any(|arm| arm.initialized_this != self.initialized_this)
        {
            return Err(
                self.invalid_stack("receiver initialization differs across control-flow join")
            );
        }
        for slot in 0..self.locals.slots.len() {
            let index = slot as u16;
            let before = self.locals.slots[slot].as_ref();
            if arms
                .iter()
                .all(|arm| arm.locals.slots[slot].as_ref() == before)
                || !live(index)
            {
                continue;
            }
            let mut bindings = arms.iter().map(|arm| arm.locals.slots[slot].as_ref());
            let unbound =
                || self.invalid_local(index, "local is not assigned on every incoming path");
            let first = bindings.next().flatten().ok_or_else(unbound)?;
            let mut ty = first.ty.clone();
            for binding in bindings {
                let binding = binding.ok_or_else(unbound)?;
                ty = self.common_type(&ty, &binding.ty).ok_or_else(|| {
                    self.invalid_local(index, "incompatible local categories at control-flow join")
                })?;
            }
            // Reuse a visible binding only within the same source lifetime.
            let debug = self.locals.debug_at(index, self.debug_offset(offset));
            let debug_range = debug.map(|entry| (entry.start_pc, entry.length));
            let local = if let Some(before) = before.filter(|before| {
                !before.receiver && before.ty == ty && before.debug_range == debug_range
            }) {
                before.clone()
            } else {
                let name = self.locals.local_name(index, &ty, debug);
                code.declarations
                    .push(format!("{} {name};", self.render_type(&ty)));
                Local {
                    name,
                    ty,
                    debug_range,
                    receiver: false,
                }
            };
            for (arm, assignments) in arms.iter().zip(&mut code.arms) {
                let value = arm.locals.slots[slot]
                    .as_ref()
                    .expect("checked incoming binding");
                if value.name != local.name {
                    let expr = arm.coerce(
                        Expr::atom(value.ty.clone(), value.name.clone()),
                        &local.ty,
                        false,
                    )?;
                    assignments.push(LocalCopy {
                        statement: format!("{} = {};", local.name, expr.text),
                        direct: (value.ty == local.ty).then(|| {
                            (
                                format!("{} {} = ", self.render_type(&value.ty), value.name),
                                format!("{} = ", local.name),
                            )
                        }),
                    });
                }
            }
            if slot > 0
                && self.locals.slots[slot - 1]
                    .as_ref()
                    .is_some_and(|previous| previous.ty.slots() == 2)
            {
                self.locals.slots[slot - 1] = None;
            }
            if local.ty.slots() == 2 {
                self.locals.slots[slot + 1] = None;
            }
            self.locals.slots[slot] = Some(local);
        }
        Ok(code)
    }

    /// The shared code uses the original source bindings. Copy into them
    /// before another incoming edge rather than let arm-local names escape.
    pub(crate) fn update_edge_locals(
        &self,
        entry: &Self,
        mut live: impl FnMut(u16) -> bool,
    ) -> Result<Vec<String>, LiftError> {
        let mut assignments = Vec::new();
        for (slot, (from, to)) in self
            .locals
            .slots
            .iter()
            .zip(&entry.locals.slots)
            .enumerate()
        {
            if from == to || !live(slot as u16) {
                continue;
            }
            let invalid = || self.invalid_local(slot as u16, "incompatible incoming local binding");
            let (from, to) = (
                from.as_ref().ok_or_else(invalid)?,
                to.as_ref().ok_or_else(invalid)?,
            );
            if to.receiver
                || !(self.known_assignable(&from.ty, &to.ty)
                    || (to.ty == INT && Category::of(&from.ty) == Some(Category::Int)))
            {
                return Err(invalid());
            }
            let value = self.coerce(
                Expr::atom(from.ty.clone(), from.name.clone()),
                &to.ty,
                false,
            )?;
            assignments.push(format!("{} = {};", to.name, value.text));
        }
        Ok(assignments)
    }

    fn common_value_type(&self, yes: &Expr, no: &Expr) -> Option<Type> {
        if Category::of(&yes.ty) == Some(Category::Ref)
            && Category::of(&no.ty) == Some(Category::Ref)
        {
            if matches!(yes.source, Source::Null) {
                return Some(no.ty.clone());
            }
            if matches!(no.source, Source::Null) {
                return Some(yes.ty.clone());
            }
        }
        if Category::of(&yes.ty) == Some(Category::Int)
            && Category::of(&no.ty) == Some(Category::Int)
        {
            if yes.ty != INT && no.fits_int_local(&yes.ty) {
                return Some(yes.ty.clone());
            }
            if no.ty != INT && yes.fits_int_local(&no.ty) {
                return Some(no.ty.clone());
            }
        }
        self.common_type(&yes.ty, &no.ty)
    }

    pub(in crate::lift) fn common_type(&self, left: &Type, right: &Type) -> Option<Type> {
        if left == right {
            return Some(left.clone());
        }
        match (Category::of(left)?, Category::of(right)?) {
            (Category::Int, Category::Int) => Some(INT),
            (Category::Ref, Category::Ref) => Some(if self.known_assignable(left, right) {
                right.clone()
            } else if self.known_assignable(right, left) {
                left.clone()
            } else if let (Type::Array(left), Type::Array(right)) = (left, right)
                && Category::of(left) == Some(Category::Ref)
                && Category::of(right) == Some(Category::Ref)
            {
                Type::Array(Box::new(self.common_type(left, right)?))
            } else {
                Type::Object("java/lang/Object".into())
            }),
            _ => None,
        }
    }
}

fn predicate(text: &str) -> std::borrow::Cow<'_, str> {
    if text.contains('?') {
        format!("({text})").into()
    } else {
        text.into()
    }
}

fn boolean_arm(condition: &str, value: &Expr, and: bool) -> (String, u8) {
    let (operator, precedence) = if and { ("&&", 3) } else { ("||", 2) };
    let text = if and && condition.contains(" || ") {
        format!("({condition}) {operator} {}", value.at(precedence))
    } else {
        format!(
            "{} {operator} {}",
            predicate(condition),
            value.at(precedence)
        )
    };
    (text, precedence)
}

fn same_value(a: &Expr, b: &Expr) -> bool {
    a.ty == b.ty
        && a.text == b.text
        && a.precedence == b.precedence
        && a.order.map(|order| (order.first, order.last))
            == b.order.map(|order| (order.first, order.last))
        && a.observable == b.observable
        && a.statement == b.statement
        && a.constant == b.constant
        && match (&a.source, &b.source) {
            (Source::Local(a), Source::Local(b)) => a == b,
            (Source::New(a), Source::New(b)) => a == b,
            (Source::Integer(a), Source::Integer(b)) => a == b,
            (Source::Plain, Source::Plain)
            | (Source::CapturedLocal, Source::CapturedLocal)
            | (Source::Null, Source::Null)
            | (Source::This, Source::This)
            | (Source::OuterThis, Source::OuterThis) => true,
            // Equal rendered text does not prove that a deferred builder
            // chain or string conversion carries the same operand metadata.
            _ => false,
        }
}
