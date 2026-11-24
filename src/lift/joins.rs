// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{borrow::Cow, ops::RangeInclusive, rc::Rc};

use super::{Local, is_variable_type};
use crate::lift::{
    BooleanCondition, BooleanFact, BooleanSelection, Effect, LiftError, Machine,
    expr::{BOOLEAN, Category, Expr, INT, Order, Source, TERNARY, UNARY},
};
use crate::{
    bytecode::{Instruction, Operand},
    classfile::LocalVariable,
    descriptor::{GenericType, MethodSignature, Type, TypeArgument},
    source_text::{Document, Infix, tokens::Token},
};

pub(crate) struct JoinCode {
    pub(crate) declarations: Vec<Document>,
    pub(crate) arms: Vec<Vec<Document>>,
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
    pub(crate) declarations: Vec<Document>,
    pub(crate) arms: Vec<Vec<LocalCopy>>,
    pub(crate) hoists: Vec<LocalHoist>,
}

type HoistSites = Vec<(usize, Option<usize>)>;
type ProveHoist<'a> = dyn FnMut(usize, &str, &str, bool) -> Option<HoistSites> + 'a;

pub(crate) struct LocalHoist {
    /// The existing arm lines. `None` denotes a blank declaration whose
    /// original line can disappear when its declaration moves to the join.
    pub(crate) sites: HoistSites,
    target: String,
    token: Option<Rc<Token>>,
}

impl LocalHoist {
    pub(crate) fn rewrite(&self, line: &mut Document, prefix: usize) {
        rewrite_local_binding(line, prefix, &self.target, self.token.as_ref());
    }
}

pub(crate) struct LocalCopy {
    pub(crate) statement: Document,
    direct: Option<DirectLocalCopy>,
}

struct DirectLocalCopy {
    source: Document,
    target: String,
    token: Option<Rc<Token>>,
}

impl LocalCopy {
    /// If the source is an immediately preceding declaration, assign to the
    /// outer binding directly. Its RHS and bytecode mapping stay in place.
    pub(crate) fn fuse(&self, line: &mut Document) -> bool {
        let Some(copy) = &self.direct else {
            return false;
        };
        if !line.starts_with(copy.source.as_flat()) {
            return false;
        }
        rewrite_local_binding(line, copy.source.len(), &copy.target, copy.token.as_ref());
        true
    }
}

fn rewrite_local_binding(line: &mut Document, prefix: usize, target: &str, token: Option<&Rc<Token>>) {
    line.replace_literal_prefix(prefix, target);
    if let Some(token) = token {
        line.token_at(0..target.len() - " = ".len(), Rc::clone(token));
    }
}

pub(crate) struct HeldStack {
    original: Vec<(usize, Expr)>,
}

pub(crate) struct ConditionalStackMerge {
    pub(crate) restored: bool,
    pub(crate) uses_yes: bool,
    pub(crate) uses_no: bool,
}

impl Machine<'_, '_> {
    pub(crate) fn loop_binding_type(&self, slot: u16) -> Option<&Type> {
        Some(&self.locals.slots.get(usize::from(slot))?.as_ref()?.ty)
    }

    pub(crate) fn loop_binding_starts_here(
        &self,
        slot: u16,
        store: &Instruction,
        earlier_store: bool,
    ) -> bool {
        let Some(local) = self
            .locals
            .slots
            .get(usize::from(slot))
            .and_then(Option::as_ref)
        else {
            return false;
        };
        if let Some((start, _)) = local.debug_range {
            let end = self.debug_offset(store.offset + store.len - 1) + 1;
            return u32::from(start) == end;
        }
        if earlier_store {
            return false;
        }
        let receiver = u16::from(self.method.access_flags & 0x0008 == 0);
        slot >= receiver
            + self
                .descriptor
                .parameters
                .iter()
                .map(Type::slots)
                .sum::<u16>()
    }

    pub(crate) fn bind_loop_element(
        &mut self,
        store: &Instruction,
        slot: u16,
        ty: Type,
    ) -> Option<Document> {
        let index = usize::from(slot);
        if index + usize::from(ty.slots()) > self.locals.slots.len()
            || self.locals.slots[index].is_some()
            || index > 0
                && self.locals.slots[index - 1]
                    .as_ref()
                    .is_some_and(|local| local.ty.slots() == 2)
            || ty.slots() == 2 && self.locals.slots[index + 1].is_some()
        {
            return None;
        }
        let end = self.debug_offset(store.offset + store.len - 1) + 1;
        let debug = self.locals.debug_at(slot, end);
        let debug_range = debug.map(|entry| (entry.start_pc, entry.length));
        if debug.is_some_and(|entry| Type::parse(entry.descriptor).ok().as_ref() != Some(&ty)) {
            // Do not remove a separate JVM store conversion or let the
            // foreach declaration introduce a different binding type.
            return None;
        }
        let generic = self.locals.declaration_signature(&ty, debug);
        if generic.as_ref().is_some_and(|signature| is_variable_type(&signature.ty)) {
            // An enhanced-for binding cannot cast a raw element to a type variable.
            return None;
        }
        let name = self.locals.local_name(slot, &ty, debug);
        let local = Local {
            name,
            ty,
            generic,
            debug_range,
            receiver: false,
            token_index: self.locals.new_local_token_index(slot),
        };
        let declaration = self.declared_local_document(slot, &local).ok()?;
        self.locals.slots[index] = Some(local);
        Some(declaration)
    }

    pub(crate) fn forget_loop_binding(&mut self, slot: u16) {
        self.locals.slots[usize::from(slot)] = None;
    }

    pub(crate) fn same_live_loop_bindings(&self, other: &Self, mut live: impl FnMut(u16) -> bool) -> bool {
        self.locals.slots.iter().zip(&other.locals.slots).enumerate()
            .all(|(slot, (left, right))| left == right || !live(slot as u16))
    }

    /// Combine a JVM increment and its adjacent read without moving either
    /// past another pending operand or changing a lexical/captured binding.
    pub(crate) fn step_loop_prefix_update(
        &mut self,
        increment: &Instruction,
        load: &Instruction,
    ) -> Result<bool, LiftError> {
        let Operand::Increment { index, amount: amount @ (-1 | 1) } = increment.operand else {
            return Ok(false);
        };
        let load_index = match (load.opcode, &load.operand) {
            (0x15, Operand::Local(index)) => *index,
            (op @ 0x1a..=0x1d, _) => u16::from(op - 0x1a),
            _ => return Ok(false),
        };
        if index != load_index || !self.stack.is_empty() || !self.prelude.is_empty()
            || self.loop_binding_type(index) != Some(&INT) || self.lexical_parameter(index).is_some()
        {
            return Ok(false);
        }
        let effect = self.step(load)?;
        debug_assert!(matches!(effect, Effect::None));
        let mut value = self.pop_category(Category::Int)?;
        value.text.prepend_str(if amount == 1 { "++" } else { "--" });
        value.precedence = UNARY;
        value.source = Source::Plain;
        value.observable = true;
        value.statement = true;
        value.order = Some(self.join_order(Some(Order::at(increment.offset)), Order::at(load.offset))?);
        self.push(value)?;
        Ok(true)
    }

    pub(crate) fn loop_receiver(&self, slot: u16) -> Option<Document> {
        let local = self.locals.slots.get(usize::from(slot))?.as_ref()?;
        if Category::of(&local.ty) != Some(Category::Ref) {
            return None;
        }
        Some(match self.lexical_parameter(slot) {
            Some(expr) => expr.text,
            None => self.local_binding_document(slot, local, false),
        })
    }

    pub(crate) fn render_loop_type(&self, ty: &Type) -> String {
        self.render_type(ty)
    }

    pub(crate) fn supports_enhanced_for(&self) -> bool {
        self.class.major_version >= 49
    }

    pub(crate) fn proves_iterable(&self, ty: &Type, owner: &str) -> bool {
        let Type::Object(receiver) = ty else {
            return false;
        };
        if platform_iterable(receiver) && platform_iterable(owner) {
            return true;
        }
        let iterable = Type::Object("java/lang/Iterable".into());
        (platform_iterable(receiver) || self.known_assignable(ty, &iterable))
            && (platform_iterable(owner)
                || self.known_assignable(&Type::Object(owner.into()), &iterable))
    }

    pub(crate) fn loop_receiver_has_element(&self, slot: u16, ty: &Type, owner: &str) -> bool {
        self.locals.slots.get(usize::from(slot)).and_then(Option::as_ref)
            .and_then(|local| local.generic.as_ref())
            .and_then(|signature| iterable_argument(&signature.ty, owner))
            .or_else(|| self.loop_parameter_element(slot, owner))
            .as_ref() == Some(ty)
    }

    fn loop_parameter_element(&self, slot: u16, owner: &str) -> Option<Type> {
        let local = self.locals.slots.get(usize::from(slot))?.as_ref()?;
        if !self.options.decompile_generics {
            return None;
        }
        if !local.debug_range.is_none_or(|range| range.0 == 0) {
            return None;
        }
        let mut cursor = u16::from(self.method.access_flags & 0x0008 == 0);
        let ordinal = self.descriptor.parameters.iter().position(|ty| {
            let matches = cursor == slot;
            cursor += ty.slots();
            matches
        })?;
        let signature = self.method.signature(&self.class.pool).ok()??;
        let method = MethodSignature::parse(signature).ok()?;
        iterable_argument(method.parameters.get(ordinal)?, owner)
    }

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
        self.stack.iter().any(|value| value.is_uninitialized(self.initialized_this))
    }

    /// Join two expression-only arms without evaluating either arm eagerly.
    /// The unmodified stack prefix remains below the conditional result.
    pub(crate) fn merge_conditional_stack(
        &mut self,
        yes: &Self,
        no: &Self,
        condition: (&Document, &Document, BooleanCondition),
        control: &RangeInclusive<u32>,
        held: Option<HeldStack>,
    ) -> Result<Option<ConditionalStackMerge>, LiftError> {
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
        let (condition, inverse, facts) = condition;
        let simplify = self.simplify_boolean_ternaries();
        let mut uses = [true, true];
        let (text, precedence) = if let (Some(yes_fact), Some(no_fact)) =
            (BooleanFact::operand(yes), BooleanFact::operand(no))
            && (ty == BOOLEAN || matches!((yes_fact.literal(), no_fact.literal()),
                (Some(left), Some(right)) if left != right || simplify))
        {
            ty = BOOLEAN;
            let selection = BooleanSelection::of(facts, yes_fact, no_fact, simplify);
            if simplify {
                uses = [selection.uses(true), selection.uses(false)];
            }
            let (result, mut text) = selection.render(
                (facts, [Cow::Borrowed(condition), Cow::Borrowed(inverse)]),
                (yes_fact, boolean_document(yes, yes_fact, selection.uses(true))),
                (no_fact, boolean_document(no, no_fact, selection.uses(false))),
            );
            if self.options.include_line_mappings
                && matches!(selection, BooleanSelection::Condition { .. })
                && text.materialize_short_circuit_predicates()
            {
                // The two stack arms are only the encoding of this boolean.
                // Neither constant has a source operand after the merge.
                for origin in [yes, no].into_iter().filter_map(Expr::deferred_operand_origin) {
                    text.omit_bytes(origin.bytes());
                }
            }
            (text, result.precedence())
        } else {
            let yes = self.conditional_operand(yes, &ty, &no.ty)?;
            let no = self.conditional_operand(no, &ty, &yes.ty)?;
            let parens = condition.infix() == Some(Infix::TERNARY);
            let text = Document::ternary_expression([condition, &yes.text, &no.text], parens);
            (text, TERNARY)
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
        Ok(Some(ConditionalStackMerge {
            restored: original.is_some(),
            uses_yes: uses[0],
            uses_no: uses[1],
        }))
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
                .push(format!("{} {name};", self.render_type(&ty)).into());
            for (arm, assignments) in arms.iter().zip(&mut code.arms) {
                let value = arm.coerce(arm.stack[index].clone(), &ty, false)?;
                assignments.push(assignment(&name, value.text));
            }
            slots += u32::from(ty.slots());
            merged.push(Expr::atom(ty, name.into()));
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
    ) -> Result<Vec<Document>, LiftError> {
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
            let binding = Expr::atom(value.ty.clone(), name.clone().into());
            let expr = std::mem::replace(value, binding);
            declarations.push(assignment(&format!("{ty} {name}"), expr.text));
        }
        self.stack = stack;
        Ok(declarations)
    }

    pub(crate) fn update_edge_stack(
        &self,
        entry: &Self,
        offset: u32,
    ) -> Result<Vec<Document>, LiftError> {
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
            statements.push(assignment(to.text.as_str(), value.text));
        } else {
            // Edge updates are parallel copies. A permutation must not
            // overwrite an old operand before another RHS has read it.
            let mut copies = Vec::with_capacity(updates.len());
            for (to, value) in updates {
                let temporary = self.locals.temporary(offset);
                statements.push(assignment(
                    &format!("{} {temporary}", self.render_type(&to.ty)),
                    value.text,
                ));
                copies.push(assignment(to.text.as_str(), temporary.into()));
            }
            statements.extend(copies);
        }
        Ok(statements)
    }

    pub(crate) fn merge_locals(
        &mut self,
        arms: &[&Self],
        offset: u32,
        live: impl FnMut(u16) -> bool,
    ) -> Result<LocalJoinCode, LiftError> {
        self.merge_local_bindings(arms, offset, live, None)
    }

    pub(crate) fn merge_locals_with_hoists(
        &mut self,
        arms: &[&Self],
        offset: u32,
        live: impl FnMut(u16) -> bool,
        mut prove_move: impl FnMut(usize, &str, &str, bool) -> Option<HoistSites>,
    ) -> Result<LocalJoinCode, LiftError> {
        self.merge_local_bindings(arms, offset, live, Some(&mut prove_move))
    }

    fn merge_local_bindings(
        &mut self,
        arms: &[&Self],
        offset: u32,
        mut live: impl FnMut(u16) -> bool,
        mut prove_move: Option<&mut ProveHoist<'_>>,
    ) -> Result<LocalJoinCode, LiftError> {
        self.offset = offset;
        let mut code = LocalJoinCode {
            declarations: Vec::new(),
            arms: (0..arms.len()).map(|_| Vec::new()).collect(),
            hoists: Vec::new(),
        };
        if arms
            .iter()
            .any(|arm| arm.initialized_this != self.initialized_this)
        {
            return Err(
                self.invalid_stack("receiver initialization differs across control-flow join")
            );
        }
        self.merge_early_final_fields(arms);
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
            let adopted = if let Some(prove) = &mut prove_move
                && before.is_none()
                && let Some(debug) = debug
                && let Some(owner) = self.debug_join_owner(arms, slot, debug, &ty)
            {
                let binding = arms[owner].locals.slots[slot].as_ref().expect("proved owner");
                let declaration = arms[owner].declared_local_document(index, binding)?;
                prove(owner, declaration.as_flat(), &binding.name, false).map(|sites| (binding, sites))
            } else {
                None
            };
            let mut move_sites = None;
            let local = if let Some(before) = before.filter(|before| {
                !before.receiver && before.ty == ty && before.debug_range == debug_range
            }) {
                before.clone()
            } else {
                let (name, token_index) = if let Some((binding, sites)) = adopted {
                    move_sites = Some(sites);
                    (binding.name.clone(), binding.token_index)
                } else {
                    (self.locals.local_name(index, &ty, debug), self.locals.new_local_token_index(index))
                };
                let local = Local {
                    name,
                    generic: self.locals.declaration_signature(&ty, debug),
                    ty,
                    debug_range,
                    receiver: false,
                    token_index,
                };
                let mut declaration = self.declared_local_document(index, &local)?;
                declaration.push(';');
                code.declarations.push(declaration);
                local
            };
            for (position, (arm, assignments)) in arms.iter().zip(&mut code.arms).enumerate() {
                let value = arm.locals.slots[slot]
                    .as_ref()
                    .expect("checked incoming binding");
                if value.name != local.name {
                    if let (Some(sites), Some(prove)) = (&mut move_sites, &mut prove_move)
                        && arm.stack_is_empty()
                    {
                        let declaration = arm.declared_local_document(index, value)?;
                        if let Some(moved) = prove(position, declaration.as_flat(), &value.name, true) {
                            sites.extend(moved);
                            continue;
                        }
                    }
                    let expr = arm.coerce_local_assignment(
                        Expr::atom(
                            value.ty.clone(),
                            arm.local_binding_document(index, value, false),
                        ),
                        &local.ty,
                        local.generic.as_deref(),
                        value.generic.as_deref(),
                    )?;
                    let token = self.local_binding_token(index, &local, false);
                    let mut target = Document::new();
                    if let Some(token) = &token {
                        target.token(&local.name, Rc::clone(token));
                    } else {
                        target.push_str(&local.name);
                    }
                    let direct = if value.ty == local.ty
                        && value.generic == local.generic
                        && (self.code_type_renderer.is_none()
                            || arm.declared_local_type(index, value)? == self.declared_local_type(index, &local)?)
                    {
                        let mut source = arm.declared_local_document(index, value)?;
                        source.push_str(" = ");
                        Some(DirectLocalCopy {
                            source,
                            target: format!("{} = ", local.name),
                            token,
                        })
                    } else {
                        None
                    };
                    assignments.push(LocalCopy { statement: local_assignment(target, expr.text), direct });
                }
            }
            if let Some(sites) = move_sites {
                code.hoists.push(LocalHoist {
                    sites,
                    target: format!("{} = ", local.name),
                    token: self.local_binding_token(index, &local, false),
                });
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

    fn debug_join_owner(
        &self,
        arms: &[&Self],
        slot: usize,
        debug: &LocalVariable<'_>,
        ty: &Type,
    ) -> Option<usize> {
        if arms.len() < 2 || !self.locals.use_debug_names || self.locals.names.borrow().namer.is_some()
            || Type::parse(debug.descriptor).ok()? != *ty
        {
            return None;
        }
        let generic = self.locals.declaration_signature(ty, Some(debug));
        let render = generic.as_ref().map_or_else(|| ty.into(), |signature| (&signature.ty).into());
        let annotation = self.annotated_local_type(debug.index, (debug.start_pc, debug.length), render).ok()?;
        // javac splits one source lifetime into LVT fragments at reaching
        // definitions and at the continuation. All fragments must describe
        // the same slot, spelling and exact Java type. The shared registry
        // proves that the reaching local already owns this spelling.
        let mut owner = None;
        for (position, arm) in arms.iter().enumerate() {
            let binding = arm.locals.slots[slot].as_ref()?;
            let range = binding.debug_range?;
            if binding.receiver || binding.ty != *ty
                || binding.generic != generic
                || arm.annotated_local_type(debug.index, range, render).ok()? != annotation
                || !Rc::ptr_eq(&self.locals.names, &arm.locals.names)
                || !self.locals.debug.iter().any(|entry| {
                    entry.index == debug.index && (entry.start_pc, entry.length) == range
                        && entry.name == debug.name && entry.descriptor == debug.descriptor
                })
                || binding.name == debug.name && owner.replace(position).is_some()
            {
                return None;
            }
        }
        owner
    }

    /// The shared code uses the original source bindings. Copy into them
    /// before another incoming edge rather than let arm-local names escape.
    pub(crate) fn update_edge_locals(
        &self,
        entry: &Self,
        mut live: impl FnMut(u16) -> bool,
    ) -> Result<Vec<Document>, LiftError> {
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
            let value = self.coerce_local_assignment(
                Expr::atom(
                    from.ty.clone(),
                    self.local_binding_document(slot as u16, from, false),
                ),
                &to.ty,
                to.generic.as_deref(),
                from.generic.as_deref(),
            )?;
            assignments.push(local_assignment(
                entry.local_binding_document(slot as u16, to, false),
                value.text,
            ));
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

// This part of the platform hierarchy is known without runtime classes and
// each listed type carries the Iterable parameter through without changes.
fn platform_iterable(name: &str) -> bool {
    matches!(
        name,
        "java/lang/Iterable"
            | "java/util/Collection"
            | "java/util/List"
            | "java/util/Set"
            | "java/util/SortedSet"
            | "java/util/NavigableSet"
            | "java/util/Queue"
            | "java/util/Deque"
            | "java/util/ArrayList"
            | "java/util/LinkedList"
            | "java/util/HashSet"
            | "java/util/TreeSet"
            | "java/util/ArrayDeque"
            | "java/util/Vector"
    )
}

fn iterable_argument(ty: &GenericType, owner: &str) -> Option<Type> {
    let GenericType::Class(class) = ty else {
        return None;
    };
    if class.internal_name != owner || !class.nested.is_empty() || !platform_iterable(owner) {
        return None;
    }
    let [argument] = class.arguments.as_slice() else { return None };
    match argument {
        TypeArgument::Exact(ty) | TypeArgument::Extends(ty) => generic_erasure(ty),
        _ => None,
    }
}

fn generic_erasure(ty: &GenericType) -> Option<Type> {
    match ty {
        GenericType::Class(class) if class.nested.is_empty() => {
            Some(Type::Object(class.internal_name.clone()))
        }
        GenericType::Array {
            dimensions,
            element,
        } => {
            let mut ty = generic_erasure(element)?;
            for _ in 0..*dimensions {
                ty = Type::Array(Box::new(ty));
            }
            Some(ty)
        }
        GenericType::Primitive(primitive) => Some(Type::Primitive(*primitive)),
        _ => None,
    }
}

fn assignment(target: &str, mut value: Document) -> Document {
    value.prepend_str(" = ");
    value.prepend_str(target);
    value.push(';');
    value
}

fn local_assignment(mut target: Document, value: Document) -> Document {
    target.push_str(" = ");
    target.append(value);
    target.push(';');
    target
}

fn boolean_document(value: &Expr, fact: BooleanFact, used: bool) -> Cow<'_, Document> {
    if used && value.ty != BOOLEAN && let Some(literal) = fact.literal() {
        return Cow::Owned(Document::from(if literal { "true" } else { "false" }));
    }
    Cow::Borrowed(&value.text)
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
            (Source::Boxing(a), Source::Boxing(b)) | (Source::Unboxing(a), Source::Unboxing(b)) => a == b,
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
