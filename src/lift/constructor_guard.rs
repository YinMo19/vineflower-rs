use crate::{bytecode::Instruction, descriptor::Type, source_text::Document};

use super::{LiftError, Machine, expr::{Expr, Order, Source, TERNARY}};

#[derive(Clone)]
pub(super) struct ConstructorGuard {
    allocation: u32,
    slot: u16,
    reload: u32,
    constructor: Option<u32>,
    order: Order,
    statement: Document,
}

impl Machine<'_, '_> {
    pub(super) fn constructor_guard_binding(
        &self,
        opcode: u8,
        member: (&str, &str, &str),
        arguments: &[Expr],
    ) -> Option<(u32, u16)> {
        if opcode != 0xb8
            || member != ("kotlin/jvm/internal/Intrinsics", "checkNotNull", "(Ljava/lang/Object;Ljava/lang/String;)V")
            || !self.supports_switch_expressions()
            || self.normalized.is_some()
            || !self.initialized_this
            || self.array_probe_depth != 0
        {
            return None;
        }
        let [alias, receiver] = self.stack.as_slice() else { return None };
        let (Source::New(allocation), Source::New(receiver_allocation)) = (&alias.source, &receiver.source) else {
            return None;
        };
        let [checked, message] = arguments else { return None };
        let (Source::Local(slot), Some(order)) = (&checked.source, checked.order) else {
            return None;
        };
        // Match NEW, DUP and a direct local read, not an earlier value held
        // across allocation or a value produced by a conditional expression.
        (*allocation == *receiver_allocation && order.first == *allocation + 4
            && order.first == order.last && message.constant && message.order.is_none()
            && matches!(&message.ty, Type::Object(name) if name == "java/lang/String"))
            .then_some((*allocation, *slot))
    }

    pub(super) fn defer_constructor_guard(
        &mut self,
        op: &Instruction,
        (allocation, slot): (u32, u16),
        order: Order,
        statement: Document,
    ) {
        self.instruction_has_source = false;
        self.constructor_guard = Some(ConstructorGuard {
            allocation, slot, reload: op.offset + op.len, constructor: None, order, statement,
        });
    }

    pub(super) fn check_constructor_guard_step(&mut self, op: &Instruction) -> Result<(), LiftError> {
        let Some(guard) = &mut self.constructor_guard else { return Ok(()) };
        if let Some(constructor) = guard.constructor {
            if op.offset == constructor && op.opcode == 0xb7 {
                let index = self.constant_index(op)?;
                if self.class.pool.member_ref(index)?.1 == "<init>" {
                    return Ok(());
                }
            }
        } else if op.offset == guard.reload && matches!(op.opcode, 0x19 | 0x2a..=0x2d)
            && op.local_access().is_some_and(|(slots, _)| slots.start == u32::from(guard.slot))
        {
            guard.constructor = Some(op.offset + op.len);
            return Ok(());
        }
        Err(self.unsupported("constructor null check is not followed by a matching argument reload and constructor"))
    }

    pub(super) fn fold_constructor_guard(&mut self, receiver: &Expr, args: &mut [Expr]) -> Result<bool, LiftError> {
        let Some(guard) = self.constructor_guard.take() else { return Ok(false) };
        let unsupported = || self.unsupported("cannot inline a constructor null check in its argument");
        let [argument] = args else { return Err(unsupported()) };
        if !matches!(receiver.source, Source::New(allocation) if allocation == guard.allocation)
            || !matches!(argument.source, Source::Local(slot) if slot == guard.slot)
            || self.code.exceptions.iter().any(|handler| {
                [handler.start_pc, handler.end_pc].into_iter().map(u32::from)
                    .any(|boundary| guard.allocation < boundary && boundary <= self.offset)
            })
        {
            return Err(unsupported());
        }
        let order = self.join_order(Some(guard.order), argument.order.ok_or_else(unsupported)?)?;
        // Java evaluates a plain class allocation before its arguments. A
        // default-only switch can run the original void call in that argument
        // without a helper frame or allocation (including on the null path).
        let mut text = Document::from("switch (0) {");
        text.hard_line(1);
        text.push_str("default -> {");
        text.hard_line(2);
        let mut statement = guard.statement;
        statement.offset_relative_depth(2);
        text.append(statement);
        text.hard_line(2);
        text.push_str("yield ");
        let mut value = std::mem::take(&mut argument.text);
        value.offset_relative_depth(2);
        text.append(value);
        text.push(';');
        text.hard_line(1);
        text.push('}');
        text.hard_line(0);
        text.push('}');
        argument.text = text;
        argument.source = Source::Plain;
        argument.precedence = TERNARY;
        argument.order = Some(order);
        argument.observable = true;
        Ok(true)
    }
}
