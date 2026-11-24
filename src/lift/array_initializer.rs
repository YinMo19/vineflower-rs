// Based on Vineflower SimplifyExprentsHelper (Apache-2.0).
use std::{mem, rc::Rc, vec::IntoIter};

use crate::{
    bytecode::{Instruction, Operand},
    classfile::Constant,
    context::NestedKind,
    descriptor::{MethodDescriptor, Primitive, Type},
    source_text::{ArrayStyle, Document},
};

use super::{
    Effect, LiftError, Machine,
    expr::{Category, Expr, INT, Order, Source, UNARY},
    operations::array_store_opcode,
};

#[cfg(test)]
mod tests;

#[derive(Clone)]
pub(super) struct ArrayArgument {
    pub(super) call_offset: u32,
    pub(super) descriptor: MethodDescriptor,
    pub(super) elements: Vec<ArrayElement>,
    pub(super) known_types: bool,
}

#[derive(Clone)]
pub(super) struct ArrayElement {
    pub(super) text: Document,
    /// None denotes the null type, not its erased JVM stack type.
    pub(super) ty: Option<Type>,
    narrow_literal: bool,
}

impl ArrayElement {
    pub(super) fn prepare_invocation(&mut self) {
        if self.narrow_literal {
            self.text.prepend_str(match self.ty {
                Some(Type::Primitive(Primitive::Byte)) => "(byte)",
                Some(Type::Primitive(Primitive::Short)) => "(short)",
                _ => unreachable!("only byte and short literals need invocation narrowing"),
            });
        }
    }
}

#[derive(Clone)]
pub(super) struct OpenArray {
    length: usize,
    elements: Vec<Document>,
    stage: OpenArrayStage,
}

#[derive(Clone, Copy)]
enum OpenArrayStage {
    DuplicateAt(u32),
    StoreFrom(u32),
}

struct ArrayPlan {
    start: usize,
    first_receiver: usize,
    end: usize,
    length: usize,
    ty: Type,
}

struct ArrayProbe<'a, P> {
    instructions: &'a [Instruction],
    permits: P,
    temporary: Option<u16>,
}

impl Machine<'_, '_> {
    // The straight-line probe cannot see an element split by a value fork.
    // Where an enclosing allocation already forbids a spill, keep the
    // compiler's dup/store pair on the stack until the initializer is proven.
    pub(super) fn seed_array_initializer(&self, op: &Instruction, count: &Expr, array: &mut Expr) {
        if self.array_probe_depth == 0
            && let Some(length) = array_length(count).filter(|&length| length != 0)
            && self.stack.iter().any(|value| matches!(value.source, Source::New(_)))
        {
            array.source = Source::ArrayInitializerSeed { length, dup: op.offset + op.len };
        }
    }

    pub(super) fn duplicate_array_initializer(&mut self) -> Result<bool, LiftError> {
        let array = self.stack.last_mut().expect("dup checked its operand");
        match &mut array.source {
            Source::ArrayInitializerSeed { length, dup } if *dup == self.offset => {
                array.source = Source::OpenArray(Rc::new(OpenArray {
                    length: *length,
                    elements: Vec::new(),
                    stage: OpenArrayStage::StoreFrom(self.offset),
                }));
                array.text = Document::new();
            }
            Source::OpenArray(open)
                if matches!(open.stage, OpenArrayStage::DuplicateAt(dup) if dup == self.offset) =>
            {
                Rc::make_mut(open).stage = OpenArrayStage::StoreFrom(self.offset);
            }
            _ => return Ok(false),
        }
        // Only the carrier owns the allocation's evaluation order. The
        // duplicate has no source or order, and may only feed an array store.
        let receiver = Expr {
            source: Source::OpenArrayReceiver(self.offset),
            ..Expr::atom(array.ty.clone(), Document::new())
        };
        self.push(receiver)?;
        Ok(true)
    }

    pub(super) fn store_array_initializer_element(
        &mut self,
        opcode: u8,
        index: Expr,
        value: Expr,
    ) -> Result<Effect, LiftError> {
        let [.., array, receiver] = self.stack.as_slice() else {
            return Err(self.invalid_stack("array initializer store is missing its allocation"));
        };
        let (Source::OpenArray(open), Source::OpenArrayReceiver(dup), Type::Array(component)) =
            (&array.source, &receiver.source, &array.ty)
        else {
            return Err(self.invalid_stack("array initializer store is missing its allocation"));
        };
        if !matches!(open.stage, OpenArrayStage::StoreFrom(expected) if expected == *dup)
            || array_store_opcode(component) != opcode
            || array_length(&index) != Some(open.elements.len())
        {
            return Err(self.unsupported("array initializer needs an identical receiver and sequential literal index"));
        }
        let value = self.array_initializer_element(value, component)?;
        let order = self.order_of([array, &index, &value], true)?;

        self.stack.pop(); // verified synthetic receiver
        let mut array = self.stack.pop().expect("verified initializer carrier");
        self.stack_slots -= 2;
        let Source::OpenArray(mut open) = mem::replace(&mut array.source, Source::Plain) else {
            unreachable!("verified initializer carrier")
        };
        let state = Rc::make_mut(&mut open);
        if state.elements.len() + 1 == state.length {
            let elements = mem::take(&mut state.elements).into_iter().chain([value.text]);
            array.text = self.render_array_elements(&array.ty, elements);
        } else {
            state.elements.push(value.text);
            state.stage = OpenArrayStage::DuplicateAt(self.offset + 1);
            array.source = Source::OpenArray(open);
        }
        array.order = order;
        self.push(array)?;
        Ok(Effect::None)
    }

    /// Try a compiler-style array creation within one straight-line block.
    /// Success leaves one typed array in the dimension's original stack slot
    /// and returns the number of instructions represented by that expression.
    /// For a local transport the final aload is included, leaving its areturn
    /// to the normal return lifter.
    pub(crate) fn try_array_initializer(
        &mut self,
        instructions: &[Instruction],
        permits: impl Fn(usize, &Instruction) -> bool,
    ) -> Option<usize> {
        let [allocation, transport, ..] = instructions else {
            return None;
        };
        if !matches!(allocation.opcode, 0xbc | 0xbd) || !self.prelude.is_empty() {
            return None;
        }
        let temporary = if transport.opcode == 0x59 {
            None
        } else {
            Some(self.array_return_temporary(instructions)?)
        };
        let first_index = 2 + usize::from(temporary.is_some());
        if self.literal_index(instructions.get(first_index)?) != Some(0) {
            return None;
        }
        let length = array_length(self.stack.last()?)?;
        let probe = ArrayProbe {
            instructions,
            permits: |index: usize, op: &Instruction| {
                allows_contiguous(instructions, index, op) && permits(index, op)
            },
            temporary,
        };
        let mut arrays = Vec::new();
        self.plan_array(&probe, 0, length, 0, &mut arrays)?;
        let mut arrays = arrays.into_iter();
        let root = arrays.next().expect("array preflight produced a root");
        let consumed = if temporary.is_some() {
            let [load, ret] = &instructions[root.end..] else {
                return None;
            };
            if !(probe.permits)(root.end, load)
                || !(probe.permits)(root.end + 1, ret)
                || !self.known_assignable(&root.ty, &self.descriptor.return_type)
            {
                return None;
            }
            root.end + 1
        } else {
            root.end
        };

        // Without a local transport, the verified dup/store sequence leaves
        // exactly one reference. Only the next instruction in this region can
        // consume it as varargs: a later use might no longer own the allocation.
        let pending = if temporary.is_none() {
            instructions
                .get(consumed)
                .filter(|op| (probe.permits)(consumed, op))
                .and_then(|op| self.immediate_array_call(op, &root.ty))
                .map(|(call_offset, descriptor)| ArrayArgument {
                    call_offset,
                    descriptor,
                    elements: Vec::with_capacity(root.length),
                    known_types: true,
                })
        } else {
            None
        };

        // Only the typed pass renders. Stage method retention until it has
        // also proved the element assignment conversions and operand order.
        let original_helpers = self.dynamic_helpers.take();
        self.dynamic_helpers = original_helpers.as_ref().map(|_| Default::default());
        let position = (self.offset, self.opcode);
        let has_source = self.instruction_has_source;
        let initialized = self.initialized_this;
        let result = self.fold_array(instructions, root, &mut arrays, pending);
        self.initialized_this = initialized;
        let staged = mem::replace(&mut self.dynamic_helpers, original_helpers);
        if result.is_err() {
            (self.offset, self.opcode) = position;
            self.instruction_has_source = has_source;
            return None;
        }
        if let (Some(outer), Some(staged)) = (&self.dynamic_helpers, staged) {
            outer.borrow_mut().append(&mut staged.borrow_mut());
        }
        debug_assert!(arrays.as_slice().is_empty() && self.prelude.is_empty());
        Some(consumed)
    }

    fn immediate_array_call(&self, op: &Instruction, array: &Type) -> Option<(u32, MethodDescriptor)> {
        if self.class.major_version < 49 {
            return None;
        }
        let index = match (op.opcode, &op.operand) {
            (0xb6..=0xb8, Operand::Constant(index))
            | (0xb9, Operand::InvokeInterface { index, .. }) => *index,
            _ => return None,
        };
        let (_, name, descriptor) = self.class.pool.member_ref(index).ok()?;
        if name.starts_with('<')
            || !descriptor.contains('[')
            || self.enum_switch_action(op.offset).is_some()
        {
            return None;
        }
        let descriptor = MethodDescriptor::parse(descriptor).ok()?;
        (descriptor.parameters.last() == Some(array)).then_some((op.offset, descriptor))
    }

    pub(super) fn render_array_argument(&self, ty: &Type, elements: Vec<ArrayElement>) -> Document {
        self.render_array_elements(ty, elements.into_iter().map(|element| element.text))
    }

    fn render_array_elements(&self, ty: &Type, elements: impl IntoIterator<Item = Document>) -> Document {
        let mut text = self.array_initializer_header(ty);
        let mut initializer = text.array_initializer(ArrayStyle::New);
        for element in elements {
            initializer.append(element);
        }
        initializer.finish();
        text
    }

    fn array_initializer_element(&self, value: Expr, component: &Type) -> Result<Expr, LiftError> {
        if Category::of(component) != Some(Category::Ref) {
            return self.coerce(value, component, false);
        }
        if !matches!(value.source, Source::Null) && !self.known_assignable(&value.ty, component) {
            // A cast to the component type could turn an array-store
            // exception into a cast exception.
            return Err(self.unsupported("array initializer reference is not assignable"));
        }
        Ok(value)
    }

    fn array_initializer_header(&self, ty: &Type) -> Document {
        let mut text = Document::from("new ");
        text.push_str(&self.render_type(ty));
        text
    }

    fn array_return_temporary(&self, instructions: &[Instruction]) -> Option<u16> {
        let [allocation, store, .., load, ret] = instructions else {
            return None;
        };
        let slot = reference_store_slot(store)?;
        if !self.initialized_this
            || self.stack_slots != 1
            || slot >= self.code.max_locals
            || (self.method.access_flags & 0x0008 == 0 && slot == 0)
            || ret.opcode != 0xb0
            || local_load(load) != Some((slot, Category::Ref))
        {
            return None;
        }

        // The temporary may disappear only if no exception edge can observe it
        // before the return. Use the same instruction space as the lifted block.
        let handlers = self
            .normalized
            .map_or(self.code.exceptions.as_slice(), |code| code.handlers.as_slice());
        let end = ret.offset.checked_add(ret.len)?;
        if handlers.iter().any(|handler| {
            u32::from(handler.start_pc) < end && allocation.offset < u32::from(handler.end_pc)
        }) {
            return None;
        }
        Some(slot)
    }

    fn plan_array(
        &self,
        probe: &ArrayProbe<impl Fn(usize, &Instruction) -> bool>,
        start: usize,
        length: usize,
        depth: u8,
        arrays: &mut Vec<ArrayPlan>,
    ) -> Option<usize> {
        // Each store needs a receiver, a literal index, a value, and the
        // store itself. In particular, never allocate based on a class-file
        // dimension without a corresponding amount of bytecode.
        let ArrayProbe {
            instructions,
            permits,
            temporary,
        } = probe;
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
        let store = array_store_opcode(component);
        let local_receiver = temporary.filter(|_| start == 0);
        let first_receiver = start + 1 + usize::from(local_receiver.is_some());
        if local_receiver.is_some() && !permits(start + 1, instructions.get(start + 1)?) {
            return None;
        }
        let plan = arrays.len();
        arrays.push(ArrayPlan {
            start,
            first_receiver,
            end: 0,
            length,
            ty,
        });
        let mut cursor = first_receiver;
        for expected_index in 0..length {
            let receiver = instructions.get(cursor)?;
            let index = instructions.get(cursor + 1)?;
            let correct_receiver = local_receiver.map_or(receiver.opcode == 0x59, |slot| {
                local_load(receiver) == Some((slot, Category::Ref))
            });
            if !correct_receiver
                || !permits(cursor, receiver)
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
                // This also applies to nested array elements: no RHS can
                // inspect, publish, or load through the partially filled array.
                if temporary.is_some_and(|slot| {
                    local_load(op).is_some_and(|(index, category)| {
                        index == slot
                            || index.checked_add(1) == Some(slot)
                                && matches!(category, Category::Long | Category::Double)
                    })
                }) {
                    return None;
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
                    cursor = self.plan_array(probe, cursor, length, depth + 1, arrays)?;
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
        pending: Option<ArrayArgument>,
    ) -> Result<(), LiftError> {
        if self.stack.last().and_then(array_length) != Some(plan.length) {
            return Err(self.invalid_stack("array initializer needs its literal dimension"));
        }
        let slots = self.stack_slots;
        // With dup, the array remains below the receiver and index. A local
        // store leaves only the latter two on the stack while evaluating a RHS.
        let hidden_slots = slots + if plan.first_receiver == plan.start + 1 { 2 } else { 1 };
        if hidden_slots > self.max_stack {
            return Err(self.invalid_stack("array initializer exceeds max_stack"));
        }
        let outer_stack = mem::take(&mut self.stack);
        self.stack_slots = hidden_slots;
        self.array_probe_depth += 1;
        let expression = self.fold_array_values(instructions, plan, arrays, pending);
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
        mut pending: Option<ArrayArgument>,
    ) -> Result<Expr, LiftError> {
        let Type::Array(component) = &plan.ty else {
            unreachable!("planned an array")
        };
        let category = Category::of(component).expect("nonvoid JVM array component");
        let mut order = Some(Order::at(instructions[plan.start].offset));
        let mut text = if pending.is_none() {
            self.array_initializer_header(&plan.ty)
        } else {
            Document::new()
        };
        let mut initializer = if pending.is_none() {
            Some(text.array_initializer(ArrayStyle::New))
        } else {
            None
        };
        let mut cursor = plan.first_receiver;
        for _ in 0..plan.length {
            cursor += 2; // verified receiver and literal index
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
                    let narrow_literal = pending.is_some()
                        && value.ty != **component
                        && matches!(value.source, Source::Integer(_))
                        && matches!(
                            **component,
                            Type::Primitive(Primitive::Byte | Primitive::Short)
                        );
                    let value = self.array_initializer_element(value, component)?;
                    if let Some(value) = self.order_of([&value], true)? {
                        order = Some(self.join_order(order, value)?);
                    }
                    if let Some(pending) = &mut pending {
                        pending.known_types &= !self.local_argument_needs_erasure(&value);
                        pending.elements.push(ArrayElement {
                            ty: (!matches!(value.source, Source::Null)).then_some(value.ty),
                            text: value.text,
                            narrow_literal,
                        });
                    } else {
                        initializer
                            .as_mut()
                            .expect("ordinary array initializer")
                            .append(value.text);
                    }
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
                    self.fold_array(instructions, nested, arrays, None)?;
                } else {
                    if !matches!(self.step(op)?, Effect::None) {
                        return Err(self.unsupported("statement in array initializer"));
                    }
                    cursor += 1;
                }
            }
        }
        debug_assert_eq!(cursor, plan.end);
        if let Some(initializer) = initializer {
            initializer.finish();
        }
        let source = pending.map_or(Source::Plain, |pending| {
            Source::PendingArrayArgument(Box::new(pending))
        });
        Ok(Expr {
            order,
            observable: true,
            precedence: UNARY,
            source,
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

fn reference_store_slot(op: &Instruction) -> Option<u16> {
    match (op.opcode, &op.operand) {
        (0x3a, Operand::Local(slot)) => Some(*slot),
        (opcode @ 0x4b..=0x4e, _) => Some(u16::from(opcode - 0x4b)),
        _ => None,
    }
}

fn local_load(op: &Instruction) -> Option<(u16, Category)> {
    let (slot, kind) = match (op.opcode, &op.operand) {
        (opcode @ 0x15..=0x19, Operand::Local(slot)) => (*slot, opcode - 0x15),
        (opcode @ 0x1a..=0x2d, _) => {
            let compact = opcode - 0x1a;
            (u16::from(compact % 4), compact / 4)
        }
        _ => return None,
    };
    Some((slot, Category::for_local(kind)))
}

fn allows_contiguous(instructions: &[Instruction], index: usize, op: &Instruction) -> bool {
    index == 0 || {
        let previous = &instructions[index - 1];
        previous.offset.checked_add(previous.len) == Some(op.offset)
    }
}
