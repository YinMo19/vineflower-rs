// Based on Vineflower SimplifyExprentsHelper (Apache-2.0).
use std::{mem, vec::IntoIter};

use crate::{
    bytecode::{Instruction, Operand},
    classfile::Constant,
    context::NestedKind,
    descriptor::{Primitive, Type},
    source_text::{ArrayStyle, Document},
};

use super::{
    Effect, LiftError, Machine,
    expr::{Category, Expr, INT, Order, Source, UNARY},
};

#[cfg(test)]
mod tests;

struct ArrayPlan {
    start: usize,
    end: usize,
    length: usize,
    ty: Type,
}

impl Machine<'_, '_> {
    /// Try a compiler-style array creation within one straight-line block.
    /// Success leaves one typed array in the dimension's original stack slot
    /// and returns the number of instructions represented by that expression.
    pub(crate) fn try_array_initializer(
        &mut self,
        instructions: &[Instruction],
        permits: impl Fn(usize, &Instruction) -> bool,
    ) -> Option<usize> {
        let [allocation, duplicate, first_index, ..] = instructions else {
            return None;
        };
        if !matches!(allocation.opcode, 0xbc | 0xbd)
            || duplicate.opcode != 0x59
            || self.literal_index(first_index) != Some(0)
            || !self.prelude.is_empty()
        {
            return None;
        }
        let length = array_length(self.stack.last()?)?;
        let permits = |index: usize, op: &Instruction| {
            allows_contiguous(instructions, index, op) && permits(index, op)
        };
        let mut arrays = Vec::new();
        self.plan_array(instructions, 0, length, 0, &permits, &mut arrays)?;
        let mut arrays = arrays.into_iter();
        let root = arrays.next().expect("array preflight produced a root");
        let consumed = root.end;

        // Only the typed pass renders. Stage method retention until it has
        // also proved the element assignment conversions and operand order.
        let original_helpers = self.dynamic_helpers.take();
        self.dynamic_helpers = original_helpers.as_ref().map(|_| Default::default());
        let position = (self.offset, self.opcode);
        let initialized = self.initialized_this;
        let result = self.fold_array(instructions, root, &mut arrays);
        self.initialized_this = initialized;
        let staged = mem::replace(&mut self.dynamic_helpers, original_helpers);
        if result.is_err() {
            (self.offset, self.opcode) = position;
            return None;
        }
        if let (Some(outer), Some(staged)) = (&self.dynamic_helpers, staged) {
            outer.borrow_mut().append(&mut staged.borrow_mut());
        }
        debug_assert!(arrays.as_slice().is_empty() && self.prelude.is_empty());
        Some(consumed)
    }

    fn plan_array(
        &self,
        instructions: &[Instruction],
        start: usize,
        length: usize,
        depth: u8,
        permits: &impl Fn(usize, &Instruction) -> bool,
        arrays: &mut Vec<ArrayPlan>,
    ) -> Option<usize> {
        // Each store needs at least dup, a literal index, a value, and the
        // store itself. In particular, never allocate based on a class-file
        // dimension without a corresponding amount of bytecode.
        if length == 0 || length > (instructions.len() - start - 1) / 4 || depth == 32 {
            return None;
        }
        let allocation = &instructions[start];
        if !permits(start, allocation) {
            return None;
        }
        let (ty, _) = self.array_type(allocation).ok()?;
        let Type::Array(component) = &ty else {
            return None;
        };
        let mut rank = 1usize;
        let mut element = component.as_ref();
        while let Type::Array(inner) = element {
            element = inner;
            rank += 1;
        }
        if rank > 255 {
            return None;
        }
        let store = store_opcode(component);
        let plan = arrays.len();
        arrays.push(ArrayPlan {
            start,
            end: 0,
            length,
            ty,
        });
        let mut cursor = start + 1;
        for expected_index in 0..length {
            let duplicate = instructions.get(cursor)?;
            let index = instructions.get(cursor + 1)?;
            if duplicate.opcode != 0x59
                || !permits(cursor, duplicate)
                || self.literal_index(index) != i32::try_from(expected_index).ok()
                || !permits(cursor + 1, index)
            {
                return None;
            }
            cursor += 2;
            let value_start = cursor;
            loop {
                let op = instructions.get(cursor)?;
                if !permits(cursor, op) {
                    return None;
                }
                if matches!(op.opcode, 0x4f..=0x56) {
                    if op.opcode != store || cursor == value_start {
                        return None;
                    }
                    cursor += 1;
                    break;
                }
                if matches!(op.opcode, 0xbc | 0xbd)
                    && instructions
                        .get(cursor + 1)
                        .is_some_and(|next| next.opcode == 0x59)
                {
                    // Nested declarations need their own exact dimensions and
                    // index sequence; never interpret a stray dup as an alias.
                    let count = cursor
                        .checked_sub(1)
                        .filter(|&index| index >= value_start)?;
                    let length = usize::try_from(self.literal_index(&instructions[count])?).ok()?;
                    cursor =
                        self.plan_array(instructions, cursor, length, depth + 1, permits, arrays)?;
                } else {
                    let follows_new =
                        cursor > value_start && instructions[cursor - 1].opcode == 0xbb;
                    if !self.array_value_opcode(op, follows_new) {
                        return None;
                    }
                    cursor += 1;
                }
            }
        }
        arrays[plan].end = cursor;
        Some(cursor)
    }

    fn fold_array(
        &mut self,
        instructions: &[Instruction],
        plan: ArrayPlan,
        arrays: &mut IntoIter<ArrayPlan>,
    ) -> Result<(), LiftError> {
        if self.stack.last().and_then(array_length) != Some(plan.length) {
            return Err(self.invalid_stack("array initializer needs its literal dimension"));
        }
        let slots = self.stack_slots;
        // The allocation replaces the count (one slot), then dup and the
        // index add two more. Size checks must still see those hidden slots.
        if slots + 2 > self.max_stack {
            return Err(self.invalid_stack("array initializer exceeds max_stack"));
        }
        let outer_stack = mem::take(&mut self.stack);
        self.stack_slots = slots + 2;
        self.array_probe_depth += 1;
        let expression = self.fold_array_values(instructions, plan, arrays);
        self.array_probe_depth -= 1;
        self.stack = outer_stack;
        self.stack_slots = slots;
        *self.stack.last_mut().expect("checked dimension slot") = expression?;
        Ok(())
    }

    fn fold_array_values(
        &mut self,
        instructions: &[Instruction],
        plan: ArrayPlan,
        arrays: &mut IntoIter<ArrayPlan>,
    ) -> Result<Expr, LiftError> {
        let Type::Array(component) = &plan.ty else {
            unreachable!("planned an array")
        };
        let category = Category::of(component).expect("nonvoid JVM array component");
        let mut order = Some(Order::at(instructions[plan.start].offset));
        let mut text = Document::from("new ");
        text.push_str(&self.render_type(&plan.ty));
        let mut elements = text.array_initializer(ArrayStyle::New);
        let mut cursor = plan.start + 1;
        for _ in 0..plan.length {
            cursor += 2; // verified dup and literal index
            loop {
                let op = &instructions[cursor];
                if matches!(op.opcode, 0x4f..=0x56) {
                    self.offset = op.offset;
                    self.opcode = op.opcode;
                    self.lower_pending_comparison()?;
                    let value = self.pop_category(category)?;
                    if !self.stack_is_empty() {
                        return Err(self.invalid_stack("array initializer value leaked operands"));
                    }
                    let value = if category == Category::Ref {
                        if !matches!(value.source, Source::Null)
                            && !self.known_assignable(&value.ty, component)
                        {
                            // A cast to the component type could turn the JVM
                            // array-store exception into a cast exception.
                            return Err(
                                self.unsupported("array initializer reference is not assignable")
                            );
                        }
                        value
                    } else {
                        self.coerce(value, component, false)?
                    };
                    if let Some(value) = self.order_of([&value], true)? {
                        order = Some(self.join_order(order, value)?);
                    }
                    elements.append(value.text);
                    cursor += 1;
                    break;
                }
                if arrays
                    .as_slice()
                    .first()
                    .is_some_and(|array| array.start == cursor)
                {
                    let nested = arrays.next().expect("next nested plan");
                    cursor = nested.end;
                    self.fold_array(instructions, nested, arrays)?;
                } else {
                    if !matches!(self.step(op)?, Effect::None) {
                        return Err(self.unsupported("statement in array initializer"));
                    }
                    cursor += 1;
                }
            }
        }
        debug_assert_eq!(cursor, plan.end);
        elements.finish();
        Ok(Expr {
            order,
            observable: true,
            precedence: UNARY,
            ..Expr::atom(plan.ty, text)
        })
    }

    fn literal_index(&self, op: &Instruction) -> Option<i32> {
        match (op.opcode, &op.operand) {
            (0x02..=0x08, _) => Some(i32::from(op.opcode) - 3),
            (0x10..=0x11, Operand::Immediate(value)) => Some(*value),
            (0x12..=0x13, Operand::Constant(index)) => match self.class.pool.get(*index).ok()? {
                Constant::Integer(value) => Some(*value),
                _ => None,
            },
            _ => None,
        }
    }

    fn array_value_opcode(&self, op: &Instruction, follows_new: bool) -> bool {
        match op.opcode {
            0x00..=0x35
            | 0x5f..=0x83
            | 0x85..=0x98
            | 0xb2
            | 0xb4
            | 0xb6..=0xb9
            | 0xbc..=0xbe
            | 0xc0..=0xc1
            | 0xc5 => true,
            // This is the only allowed ordinary dup in a value. It guarantees
            // at most one surviving alias of an unfinished object allocation.
            0x59 => follows_new,
            0xbb => {
                let Operand::Constant(index) = op.operand else {
                    return false;
                };
                let Ok(name) = self.class.pool.class_name(index) else {
                    return false;
                };
                !self.options.decompile_inner
                    || !self.group.is_some_and(|group| {
                        group.is_attached(name)
                            && group
                                .nested_class(name)
                                .is_some_and(|node| matches!(node.kind, NestedKind::Anonymous))
                    })
            }
            // No local/field writes, hidden array aliases, control flow, or
            // dynamic factories that can reserve names in the enclosing scope.
            _ => false,
        }
    }
}

fn array_length(value: &Expr) -> Option<usize> {
    let Source::Integer(length) = value.source else {
        return None;
    };
    if value.ty == INT && value.order.is_none() {
        usize::try_from(length).ok()
    } else {
        None
    }
}

fn store_opcode(component: &Type) -> u8 {
    use Primitive::*;
    match component {
        Type::Primitive(Int) => 0x4f,
        Type::Primitive(Long) => 0x50,
        Type::Primitive(Float) => 0x51,
        Type::Primitive(Double) => 0x52,
        Type::Object(_) | Type::Array(_) => 0x53,
        Type::Primitive(Boolean | Byte) => 0x54,
        Type::Primitive(Char) => 0x55,
        Type::Primitive(Short) => 0x56,
        Type::Void => unreachable!("JVM array components are nonvoid"),
    }
}

fn allows_contiguous(instructions: &[Instruction], index: usize, op: &Instruction) -> bool {
    index == 0 || {
        let previous = &instructions[index - 1];
        previous.offset.checked_add(previous.len) == Some(op.offset)
    }
}
