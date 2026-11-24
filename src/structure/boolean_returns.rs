// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{borrow::Cow, collections::HashSet};

use crate::{lift::{BooleanCondition, BooleanFact, BooleanSelection}, source_text::Document};

use super::{Arm, Emitter, Line, Region, surrounded};

#[derive(Clone, Copy, Debug)]
pub(super) struct BooleanReturn {
    fact: BooleanFact,
    transfer: Option<u32>,
}

impl BooleanReturn {
    pub(super) fn direct(fact: BooleanFact, transfer: u32) -> Self {
        Self { fact, transfer: Some(transfer) }
    }

    fn take_value(line: &mut Line, used: bool) -> (BooleanFact, Cow<'static, Document>) {
        let returned = line.boolean_return.expect("a proven boolean return");
        if !used {
            return (returned.fact, Cow::Owned(Document::new()));
        }
        // Remove this emitter's own statement punctuation, not Java syntax
        // inferred from the value. Keep original layout events and tokens.
        let mut value = std::mem::take(&mut line.text);
        value.replace_literal_prefix("return ".len(), "");
        value.pop();
        (returned.fact, Cow::Owned(value))
    }
}

impl Emitter<'_> {
    /// Distinguish another terminal expression tree from the normal
    /// continuation of a guard clause. The lifted lines provide the final
    /// proof; this CFG check only controls whether we try both arms together.
    pub(super) fn pair_boolean_terminal_paths(&self, region: Region<'_, '_, '_>, entries: [usize; 2]) -> bool {
        let mut seen = HashSet::new();
        let mut pending = Vec::from(entries);
        while let Some(block) = pending.pop() {
            if !self.layout.inside(block, region)
                || self.emitted[block]
                || self.layout.loops[block].is_some()
                || self.exceptions.at_start(region.exception_arm, block).is_some()
                || !seen.insert(block)
            {
                return false;
            }
            let node = &self.graph.blocks[block];
            let instructions = &self.instructions[node.instructions.clone()];
            if instructions.iter().any(|op| matches!(op.opcode,
                0x36..=0x58 | 0x84 | 0xaa..=0xab | 0xb3 | 0xb5 | 0xc2..=0xc3))
            {
                return false;
            }
            if node.successors.is_empty() && instructions.last().is_none_or(|op| op.opcode != 0xac) {
                return false;
            }
            pending.extend(&node.successors);
        }
        true
    }

    pub(super) fn combine_boolean_returns(
        &mut self,
        arms: [&Arm<'_, '_>; 2],
        depth: usize,
        condition: (&Document, &Document, BooleanCondition),
    ) -> Option<Line> {
        let [yes, no] = arms;
        if yes.exit.is_some() || no.exit.is_some()
            || yes.end - yes.start != 1 || no.end - no.start != 1
        {
            return None;
        }
        let yes_fact = self.lines[yes.start].boolean_return?.fact;
        let no_fact = self.lines[no.start].boolean_return?.fact;
        let (condition, inverse, facts) = condition;
        let selection = BooleanSelection::of(facts, yes_fact, no_fact, true);
        let mut no = self.lines.pop().expect("last line of the false arm");
        let mut yes = self.lines.pop().expect("last line of the true arm");
        let (fact, value) = selection.render(
            (facts, [Cow::Borrowed(condition), Cow::Borrowed(inverse)]),
            BooleanReturn::take_value(&mut yes, selection.uses(true)),
            BooleanReturn::take_value(&mut no, selection.uses(false)),
        );
        let mut offsets = Vec::new();
        for (true_arm, line) in [(true, yes), (false, no)] {
            if selection.uses(true_arm) {
                let transfer = line.boolean_return.and_then(|value| value.transfer);
                offsets.extend(line.offsets.into_iter().filter(|offset| Some(*offset) != transfer));
            }
        }
        let mut line = Line::new(depth, surrounded(value, "return ", ";"), offsets);
        line.boolean_return = Some(BooleanReturn { fact, transfer: None });
        Some(line)
    }
}
