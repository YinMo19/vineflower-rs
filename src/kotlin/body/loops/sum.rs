// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Kotlin/JVM inlines Iterable.sumOf's Int selector as a bounded iterator
//! loop, keeping the old sum and the element in separate scratch slots while
//! evaluating the selector. Prove the whole recurrence before resugaring it.

use super::{Binding, Element, Shape, backward, branch_to, slot_read};
use super::super::{
    Bytecode, Constant, Expected, Expr, ExprKind, Instruction, KotlinError, Literal, Locals,
    Operand, Primitive, ScopedLocal, StackValue, ValueParameter, local_load, local_store, logic, pop_value,
};

const RANGE: &str = "kotlin/ranges/IntRange";
const INT_ITERATOR: &str = "kotlin/collections/IntIterator";
const ITERABLE: &str = "java/lang/Iterable";
const ITERATOR: &str = "java/util/Iterator";

pub(in crate::kotlin::body) struct Reduction<'a> {
    first: Expr<'a>,
    last: Expr<'a>,
    element: Binding<'a>,
    selector: Expr<'a>,
    selector_start: u32,
    sum: String,
}

pub(in crate::kotlin::body) fn recognize<'a>(
    bytecode: &Bytecode<'a, '_>, instructions: &[Instruction], locals: &Locals<'_>,
    parameters: &[ValueParameter], declaration: &str,
) -> Result<Option<Reduction<'a>>, KotlinError> {
    let [new, dup, first, last, init, iterable, save_source, zero, save_sum,
        source, iterator, save_iterator, head, has_next, exit, fetch, cast, next, save_element,
        sum, element, save_argument, save_previous, debug_zero, save_debug, selector @ ..,
        save_value, previous, value, add, update, back, result, ret] = instructions
    else { return Ok(None); };
    if selector.is_empty() || new.opcode != 0xbb || dup.opcode != 0x59
        || zero.opcode != 0x03 || debug_zero.opcode != 0x03 || add.opcode != 0x60
        || ret.opcode != 0xac || !backward(back, head) || !branch_to(exit, 0x99, result)
    {
        return Ok(None);
    }
    let (Some((0x3a, source_slot)), Some((0x36, sum_slot)), Some((0x3a, iterator_slot)),
        Some((0x36, element_slot)), Some((0x36, argument_slot)), Some((0x36, previous_slot)),
        Some((0x36, debug_slot)), Some((0x36, value_slot))) = (
        local_store(save_source), local_store(save_sum), local_store(save_iterator),
        local_store(save_element), local_store(save_argument), local_store(save_previous),
        local_store(save_debug), local_store(save_value),
    ) else { return Ok(None); };
    let slots = [source_slot, sum_slot, iterator_slot, element_slot, argument_slot, previous_slot, debug_slot, value_slot];
    let first_free = locals.next_slot();
    if slots.iter().enumerate().any(|(i, slot)| *slot < first_free || slots[..i].contains(slot))
        || local_load(source) != Some((0x19, source_slot))
        || local_load(head) != Some((0x19, iterator_slot)) || local_load(fetch) != Some((0x19, iterator_slot))
        || !slot_read(sum, sum_slot) || !slot_read(element, element_slot)
        || !slot_read(previous, previous_slot) || !slot_read(value, value_slot)
        || local_store(update) != Some((0x36, sum_slot)) || !slot_read(result, sum_slot)
    {
        return Ok(None);
    }
    let shape = Shape { bytecode, instructions, locals, parameters };
    if !shape.class_operation(new, 0xbb, RANGE)? || !shape.class_operation(iterable, 0xc0, ITERABLE)?
        || !shape.class_operation(cast, 0xc0, INT_ITERATOR)?
        || !method(bytecode, init, 0xb7, (RANGE, "<init>", "(II)V"))?
        || !method(bytecode, next, 0xb6, (INT_ITERATOR, "nextInt", "()I"))?
        || !shape.invoke_interface(iterator, ITERABLE, "iterator", "()Ljava/util/Iterator;")?
        || !shape.invoke_interface(has_next, ITERATOR, "hasNext", "()Z")?
    {
        return Ok(None);
    }
    let (Some(first), Some(last)) = (int_atom(&shape, first)?, int_atom(&shape, last)?) else { return Ok(None); };

    let mut name = format!("index{argument_slot}");
    let base = name.len();
    avoid_shadowing(&mut name, locals, parameters);
    let element = Binding {
        slot: argument_slot, element: Element::Primitive(Primitive::Int), name: None,
        suffix: name.len() - base, first_free: slots.into_iter().max().unwrap().saturating_add(1),
    };
    let mut stack = Vec::new();
    for instruction in selector {
        bytecode.expression_with_locals(instruction, locals, &mut stack, declaration, &[ScopedLocal::Loop(element)])?;
    }
    if !matches!(stack.as_slice(), [StackValue::Value(expr)] if expr.stack_load() == Some(0x15)) {
        return Ok(None);
    }
    let selector_start = selector[0].offset;
    let selector = pop_value(&mut stack, declaration)?;
    let mut sum = String::from("sum");
    avoid_shadowing(&mut sum, locals, parameters);
    Ok(Some(Reduction { first, last, element, selector, selector_start, sum }))
}

fn method(
    bytecode: &Bytecode<'_, '_>, instruction: &Instruction, opcode: u8, target: (&str, &str, &str),
) -> Result<bool, KotlinError> {
    Ok(matches!(instruction.operand, Operand::Constant(index)
        if matches!(bytecode.class.pool.get(index)?, Constant::Methodref { .. }))
        && bytecode.reference(instruction, opcode)? == Some(target))
}

fn int_atom<'a>(shape: &Shape<'_, 'a, '_>, instruction: &Instruction) -> Result<Option<Expr<'a>>, KotlinError> {
    Ok(shape.atom(instruction, 0x15)?.filter(|expr| {
        matches!(expr.kind, ExprKind::Literal(Literal::Int(_))) || expr.primitive_hint(shape.parameters) == Some(Primitive::Int)
    }))
}

fn avoid_shadowing(name: &mut String, locals: &Locals<'_>, parameters: &[ValueParameter]) {
    while parameters.iter().any(|parameter| parameter.name == name.as_str())
        || locals.templates.properties.iter().any(|property| property.name == name.as_str())
        || locals.extension.as_ref().is_some_and(|context| {
            context.members.functions.iter().any(|function| function.name == name.as_str())
                || context.local_functions.iter().any(|local| local.function.name == name.as_str())
        })
    {
        name.push('_');
    }
}

impl Reduction<'_> {
    pub(super) fn write(
        &self, out: &mut String, parameters: &[ValueParameter], declaration: &str,
        indent: &str, unit: &str, instructions: &[Instruction], mut map: impl FnMut(&Instruction, usize),
    ) -> Result<(), KotlinError> {
        let int = Expected::Primitive(Primitive::Int);
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("var ");
        out.push_str(&self.sum);
        out.push_str(" = 0\n");
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("for (");
        self.element.write(out, declaration)?;
        out.push_str(" in ");
        self.first.write_at(out, int, parameters, declaration, 0)?;
        out.push_str("..");
        self.last.write_at(out, int, parameters, declaration, 0)?;
        out.push_str(") {\n");
        out.push_str(indent);
        out.push_str(unit);
        out.push_str(unit);
        out.push_str(&self.sum);
        out.push_str(" = ");
        out.push_str(&self.sum);
        out.push_str(" + ");
        self.selector.write_at(out, int, parameters, declaration, logic::ADDITIVE + 1)?;
        out.push('\n');
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("}\n");
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("return ");
        out.push_str(&self.sum);
        out.push('\n');
        out.push_str(indent);
        out.push('}');

        let back = instructions.len() - 3;
        for (index, instruction) in instructions.iter().enumerate() {
            if instruction.opcode == 0x00 { continue; }
            map(instruction, match index {
                7..=8 => 1, // zero and its initial store
                index if index > back => 5,
                index if index < back && instruction.offset >= self.selector_start => 3,
                _ => 2,
            });
        }
        Ok(())
    }
}
