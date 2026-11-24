use std::{cell::RefCell, cmp::Reverse, mem};

use crate::{lift::Machine, source_text::Document};

use super::{Arm, Line, StructureError, flow::Region, protected::ArmId};

pub(super) struct Scope<'a, 'c> {
    pub(super) target: usize,
    loop_header: Option<usize>,
    exception_arm: Option<ArmId>,
    exits: RefCell<Vec<Option<Machine<'a, 'c>>>>,
}

impl<'a, 'c> Scope<'a, 'c> {
    pub(super) fn new(target: usize, region: Region<'_, 'a, 'c>) -> Self {
        Self {
            target,
            loop_header: region.loop_header,
            exception_arm: region.exception_arm,
            exits: RefCell::default(),
        }
    }

    pub(super) fn permits(&self, region: Region<'_, 'a, 'c>) -> bool {
        region.loop_header == self.loop_header && region.exception_arm == self.exception_arm
    }

    pub(super) fn record(&self, state: &Machine<'a, 'c>, depth: usize, offsets: Vec<u32>) -> Line {
        let mut exits = self.exits.borrow_mut();
        let index = exits.len();
        exits.push(Some(state.clone()));
        let mut line = Line::new(depth, "break;", offsets);
        line.switch_break = Some(index);
        line
    }

    pub(super) fn append_arms(
        self,
        lines: &mut [Line],
        start: usize,
        target_offset: u32,
        arms: &mut Vec<Arm<'a, 'c>>,
    ) -> Result<(), StructureError> {
        let mut exits = self.exits.into_inner();
        if exits.is_empty() {
            return Ok(());
        }
        for (position, line) in lines[start..].iter_mut().enumerate() {
            if let Some(index) = line.switch_break.take() {
                let end = start + position;
                let exit = exits.get_mut(index).and_then(Option::take)
                    .ok_or(StructureError::Flow { offset: target_offset })?;
                // A break can occur in a nested lexical scope. Do not hoist
                // another path's declaration through this edge's empty slice.
                arms.push(Arm { exit: Some(exit), offsets: Vec::new(), start: end, end });
            }
        }
        if exits.iter().any(Option::is_some) {
            return Err(StructureError::Flow { offset: target_offset });
        }
        Ok(())
    }
}

pub(super) fn write_join_copies(
    lines: &mut Vec<Line>,
    arms: Vec<Arm<'_, '_>>,
    assignments: Vec<Vec<Document>>,
    normal_count: usize,
    depth: usize,
) {
    let nested = arms.len() != normal_count;
    let edits = arms.into_iter().zip(assignments).enumerate().filter(|(_, (_, edits))| !edits.is_empty());
    let mut write = |(index, (arm, assignments)): (_, (Arm<'_, '_>, Vec<Document>))| {
        let depth = if index < normal_count { depth } else { lines[arm.end].depth };
        let mut offsets = arm.offsets;
        lines.splice(arm.end..arm.end, assignments.into_iter().map(|text| {
            Line::new(depth, text, mem::take(&mut offsets))
        }));
    };
    if nested {
        let mut edits: Vec<_> = edits.collect();
        edits.sort_unstable_by_key(|(_, (arm, _))| Reverse(arm.end));
        edits.into_iter().for_each(&mut write);
    } else {
        edits.rev().for_each(&mut write);
    }
}
