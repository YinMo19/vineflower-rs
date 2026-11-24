// Based on Vineflower SwitchExpressionHelper (Apache-2.0).

use std::{collections::BTreeMap, mem};

use crate::{
    bytecode::{Instruction, Operand},
    lift::{Effect, LiftError, Machine},
    source_text::Document,
};

use super::{CaseLabel, Line, Rule, RuleResult, SwitchExpression, surrounded};

struct Arms {
    groups: BTreeMap<usize, Vec<CaseLabel>>,
    default: usize,
    join: usize,
}

impl Arms {
    /// In a constructor argument the compiler emits private rules in bytecode
    /// order, with every normal exit going to one forward join. An explicit
    /// jump also separates the switch from any arguments evaluated after it.
    fn prove(dispatch: &Instruction, body: &[Instruction], constructor: u32) -> Option<Self> {
        let Operand::Switch { default, cases } = &dispatch.operand else {
            return None;
        };
        let index_at = |offset| body.binary_search_by_key(&offset, |op| op.offset).ok();
        let default = index_at(*default)?;
        let mut groups = BTreeMap::<usize, Vec<CaseLabel>>::new();
        groups.entry(default).or_default();
        for &(key, target) in cases {
            let target = index_at(target)?;
            if target != default {
                groups.entry(target).or_default().push(CaseLabel {
                    text: key.to_string().into(),
                    offsets: Vec::new(),
                });
            }
        }
        if *groups.first_key_value()?.0 != 0 {
            return None;
        }
        let (&last, _) = groups.last_key_value()?;
        let mut join = None;
        for &next in groups.keys().skip(1) {
            let tail = &body[next - 1];
            match tail.opcode {
                0xa7 | 0xc8 => {
                    let Operand::Branch(target) = tail.operand else {
                        return None;
                    };
                    let index = if target == constructor {
                        body.len()
                    } else {
                        index_at(target)?
                    };
                    if index <= last || join.is_some_and(|join| join != index) {
                        return None;
                    }
                    join = Some(index);
                }
                0xbf => {}
                _ => return None,
            }
        }
        Some(Self {
            groups,
            default,
            join: join.unwrap_or(body.len()),
        })
    }
}

enum Outcome<'a, 'c> {
    Yield(Machine<'a, 'c>),
    Throw(Document),
}

/// Recover an expression in the removed enum initializer prefix without
/// lifting the allocation or the synthetic name and ordinal. At each rule
/// entry the earlier arguments are inaccessible, and exactly one new value
/// must reach the join. The prefix caller rejects outside entries and handlers.
pub(crate) fn enum_argument_switch(
    machine: &mut Machine<'_, '_>,
    instructions: &[Instruction],
    constructor: u32,
    map_offsets: bool,
) -> Result<Option<usize>, LiftError> {
    let Some((dispatch, body)) = instructions.split_first() else {
        return Ok(None);
    };
    if !machine.supports_switch_expressions() {
        return Ok(None);
    }
    let Some(Arms {
        groups,
        default,
        join,
    }) = Arms::prove(dispatch, body, constructor)
    else {
        return Ok(None);
    };
    let Some(control) = machine.control_order(dispatch)? else {
        return Ok(None);
    };
    let Effect::Switch { selector } = machine.step(dispatch)? else {
        return Ok(None);
    };
    if !machine.take_prelude().is_empty() {
        return Ok(None);
    }
    let entry = machine.switch_arm_entry(&control)?;
    let mut arms = Vec::with_capacity(groups.len());
    let mut starts = groups.keys().copied().peekable();
    let join_offset = body.get(join).map_or(constructor, |op| op.offset);
    while let Some(start) = starts.next() {
        let end = starts.peek().copied().unwrap_or(join);
        let mut arm = entry.clone();
        let mut offsets = Vec::new();
        let mut thrown = None;
        for (index, op) in body[start..end].iter().enumerate() {
            let effect = arm.step(op)?;
            if !arm.take_prelude().is_empty() {
                return Ok(None);
            }
            let is_last = start + index + 1 == end;
            match effect {
                Effect::None => {}
                Effect::Jump(target) if is_last && target == join_offset => continue,
                Effect::Throw(text) if is_last => thrown = Some(text),
                _ => return Ok(None),
            }
            if map_offsets && arm.instruction_has_source() {
                offsets.extend(op.offset..op.offset + op.len);
            }
        }
        if !arm.same_locals(&entry) || arm.has_uninitialized_stack() {
            return Ok(None);
        }
        let outcome = match thrown {
            Some(text) => Outcome::Throw(text),
            None => Outcome::Yield(arm),
        };
        arms.push((outcome, offsets));
    }
    let normal = arms
        .iter()
        .filter_map(|(outcome, _)| match outcome {
            Outcome::Yield(arm) => Some(arm),
            Outcome::Throw(_) => None,
        })
        .collect::<Vec<_>>();
    let Some(mut value) = machine.join_switch_values(&normal, &control, body[join - 1].offset)?
    else {
        return Ok(None);
    };
    let mut yields = mem::take(&mut value.yields).into_iter();
    let rules = groups
        .iter()
        .zip(arms)
        .map(|((&start, labels), (outcome, offsets))| {
            let (result, statements) = match outcome {
                Outcome::Yield(_) => (
                    RuleResult::Yield(yields.next().expect("one value per normal enum switch arm")),
                    Vec::new(),
                ),
                Outcome::Throw(text) => (
                    RuleResult::Abrupt { inline_throw: true },
                    vec![Line::new(2, surrounded(text, "throw ", ";"), Vec::new())],
                ),
            };
            Rule {
                labels,
                default: (start == default).into(),
                statements,
                trailing_offsets: offsets,
                result,
            }
        })
        .collect();
    let expression = SwitchExpression {
        selector: &selector,
        rules,
        depth: 0,
    };
    machine.push_switch_value(value, expression.render())?;
    machine.commit_switch_dynamic_helpers(&entry);
    Ok(Some(join + 1))
}
