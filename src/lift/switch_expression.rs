// Based on Vineflower SwitchExpressionHelper (Apache-2.0).

use std::{mem, ops::RangeInclusive};

use crate::{
    bytecode::{Instruction, Operand},
    classfile::Constant,
    descriptor::{MethodDescriptor, Primitive, Type},
    source_text::Document,
};

use super::{
    LiftError, Machine,
    expr::{Category, Expr, INT, Order, Source, TERNARY},
};

pub(crate) struct SwitchValue {
    pub(crate) yields: Vec<Document>,
    ty: Type,
    order: Order,
}

impl<'a, 'c> Machine<'a, 'c> {
    pub(crate) fn supports_switch_expressions(&self) -> bool {
        // Match Vineflower's Java 16 class-file gate. Earlier Java releases
        // had preview (12/13) or final (14/15) switch expression syntax, but
        // are intentionally treated as statement-only by this recovery.
        self.class.major_version >= 60
    }

    /// Lift each arm above an empty operand stack. If an arm needs even one
    /// incoming operand, the trial fails by underflow. The untouched prefix
    /// then stays outside the expression, including invocation receivers and
    /// arguments which had already been evaluated before dispatch.
    pub(crate) fn switch_arm_entry(
        &mut self,
        control: &RangeInclusive<u32>,
    ) -> Result<Self, LiftError> {
        self.join_order(
            self.order_of(&self.stack, false)?,
            Order::at(*control.start()),
        )?;
        let stack = mem::take(&mut self.stack);
        let mut entry = self.clone();
        self.stack = stack;
        entry.max_stack -= entry.stack_slots;
        entry.stack_slots = 0;
        entry.dynamic_helpers = self.dynamic_helpers.as_ref().map(|_| Default::default());
        Ok(entry)
    }

    pub(crate) fn switch_anonymous_checkpoint(&self) -> usize {
        self.anonymous_sites
            .as_ref()
            .map_or(0, |sites| sites.borrow().len())
    }

    pub(crate) fn restore_switch_anonymous_sites(&self, len: usize) {
        if let Some(sites) = &self.anonymous_sites {
            sites.borrow_mut().truncate(len);
        }
    }

    pub(crate) fn commit_switch_dynamic_helpers(&self, entry: &Self) {
        if let (Some(outer), Some(staged)) = (&self.dynamic_helpers, &entry.dynamic_helpers) {
            outer.borrow_mut().append(&mut staged.borrow_mut());
        }
    }

    /// These rules supply the final constructor argument. Keep its formal
    /// Java type to preserve overload selection for null and narrow values.
    pub(crate) fn join_constructor_switch_values(
        &self,
        arms: &[&Self],
        constructor: &Instruction,
        control: &RangeInclusive<u32>,
        last: u32,
    ) -> Option<SwitchValue> {
        let Operand::Constant(index) = constructor.operand else {
            return None;
        };
        if !matches!(self.class.pool.get(index).ok()?, Constant::Methodref { .. }) {
            return None;
        }
        let (owner, name, descriptor_text) = self.class.pool.member_ref(index).ok()?;
        if constructor.opcode != 0xb7 || name != "<init>" {
            return None;
        }
        let descriptor = MethodDescriptor::parse(descriptor_text).ok()?;
        let (expected, prefix) = descriptor.parameters.split_last()?;
        let receiver_index = self.stack.len().checked_sub(prefix.len() + 1)?;
        let receiver = &self.stack[receiver_index];
        match receiver.source {
            Source::This
                if !self.initialized_this
                    && receiver_index == 0
                    && self.constructor_invocation_kind(owner, descriptor_text).is_ok() => {}
            Source::New(_) if matches!(&receiver.ty, Type::Object(name) if name == owner) => {}
            _ => return None,
        }
        if descriptor.return_type != Type::Void
            || self.stack[receiver_index + 1..]
                .iter()
                .zip(prefix)
                .any(|(value, ty)| {
                    value.is_uninitialized(self.initialized_this)
                        || Category::of(&value.ty) != Category::of(ty)
                })
        {
            return None;
        }
        let yields = arms.iter().map(|arm| {
            let value = arm.switch_yield()?;
            if value.order.is_some_and(|order| order.first <= *control.end() || order.last > last)
                || (Category::of(expected) == Some(Category::Ref)
                    && !matches!(value.source, Source::Null)
                    && !self.known_assignable(&value.ty, expected))
            {
                return None;
            }
            let yielded = self.coerce(value.clone(), expected, true).ok()?;
            (yielded.ty == *expected).then_some(yielded.text)
        }).collect::<Option<Vec<_>>>()?;
        if yields.is_empty() {
            return None;
        }
        Some(SwitchValue {
            yields,
            ty: expected.clone(),
            order: Order {
                first: *control.start(),
                last,
            },
        })
    }
    pub(crate) fn join_switch_values(
        &self,
        arms: &[&Self],
        control: &RangeInclusive<u32>,
        last: u32,
    ) -> Result<Option<SwitchValue>, LiftError> {
        let Some(first) = arms.first().and_then(|arm| arm.switch_yield()) else {
            return Ok(None);
        };
        let mut ty = first.ty.clone();
        let mut only_null = matches!(first.source, Source::Null);
        for arm in arms {
            let Some(value) = arm.switch_yield() else {
                return Ok(None);
            };
            if value
                .order
                .is_some_and(|order| order.first <= *control.end() || order.last > last)
            {
                return Ok(None);
            }
            if matches!(value.source, Source::Null) && Category::of(&ty) == Some(Category::Ref) {
                continue;
            }
            if only_null && Category::of(&value.ty) == Some(Category::Ref) {
                ty = value.ty.clone();
                only_null = false;
                continue;
            }
            let Some(join) = self.common_type(&ty, &value.ty) else {
                return Ok(None);
            };
            ty = join;
        }
        if ty == INT
            && let Some(narrow) = arms
                .iter()
                .filter_map(|arm| arm.switch_yield())
                .map(|value| &value.ty)
                .find(|&ty| {
                    *ty != INT
                        && arms
                            .iter()
                            .all(|arm| arm.switch_yield().unwrap().fits_int_local(ty))
                })
        {
            ty = narrow.clone();
        }
        let yields = arms
            .iter()
            .map(|arm| {
                let value = arm.switch_yield().expect("checked switch yield");
                // Use the same coercions as a conditional stack join. In
                // particular, mixed wrapper types must remain JVM references.
                let coerced = self.conditional_operand(value, &ty, &ty)?;
                let preserve_narrow = value.ty != ty
                    && matches!(ty, Type::Primitive(Primitive::Byte | Primitive::Short));
                Ok(if only_null || preserve_narrow {
                    self.cast(coerced, ty.clone(), false)?.text
                } else {
                    coerced.text
                })
            })
            .collect::<Result<_, LiftError>>()?;
        Ok(Some(SwitchValue {
            yields,
            ty,
            order: Order {
                first: *control.start(),
                last,
            },
        }))
    }

    fn switch_yield(&self) -> Option<&Expr> {
        let [value] = self.stack.as_slice() else {
            return None;
        };
        (!value.is_uninitialized(self.initialized_this)
            && !matches!(value.source, Source::Comparison(_)))
        .then_some(value)
    }

    pub(crate) fn push_switch_value(
        &mut self,
        value: SwitchValue,
        text: Document,
    ) -> Result<(), LiftError> {
        self.push(Expr {
            precedence: TERNARY,
            observable: true,
            order: Some(value.order),
            ..Expr::atom(value.ty, text)
        })
    }
}
