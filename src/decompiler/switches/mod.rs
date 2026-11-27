//! Switch rewrites in Java's method-processing loop.

pub(crate) mod expression;
pub(crate) mod patterns;

mod enums;
mod strings;

use std::io;

use super::exps::ExprKind;
use super::ir::{ExprId, Ir, StatId};
use super::stats::{StatementKind, SwitchStatement};
use crate::engine::{Cx, counter_container::CounterContainer};

/// SwitchHelper works from the outside in. A string switch can replace an
/// entire sequence, so descend through the live child list after each rewrite.
pub(crate) fn simplify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    fn visit(
        cx: &mut Cx,
        counters: &mut CounterContainer,
        stat: StatId,
        root: StatId,
    ) -> io::Result<bool> {
        let mut changed = false;
        if let StatementKind::Switch(_) = cx.ir[stat].kind {
            changed = match enums::simplify(cx, counters, stat, root)? {
                Some(result) => result,
                None => {
                    let (_, value) = switch_head(&cx.ir, stat).expect("Missing switch header");
                    strings::simplify(cx, counters, stat, value)?
                }
            };
        }
        let mut index = 0;
        while index < cx.ir[stat].stats.len() {
            changed |= visit(cx, counters, cx.ir[stat].stats[index], root)?;
            index += 1;
        }
        Ok(changed)
    }

    let cx = &mut *cx.enter_method(counters);
    visit(cx, counters, root, root)
}

fn switch(ir: &Ir, stat: StatId) -> &SwitchStatement {
    let StatementKind::Switch(switch) = &ir[stat].kind else {
        unreachable!("Expected a switch statement");
    };
    switch
}

fn switch_mut(ir: &mut Ir, stat: StatId) -> &mut SwitchStatement {
    let StatementKind::Switch(switch) = &mut ir[stat].kind else {
        unreachable!("Expected a switch statement");
    };
    switch
}

fn switch_head(ir: &Ir, stat: StatId) -> Option<(ExprId, ExprId)> {
    let head = *ir[switch(ir, stat).head_exprents?].first()?;
    let ExprKind::SwitchHead { value, .. } = ir[head].kind else {
        return None;
    };
    Some((head, value))
}
