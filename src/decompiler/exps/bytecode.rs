// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Bytecode position sets attached to expressions.

use std::ops::Range;
use std::sync::Arc;

use itertools::Itertools;

use super::{Expr, ExprKind, SwitchCaseValues};
use crate::decompiler::ir::{ExprId, Ir};
use crate::decompiler::stats::StatementKind;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BytecodeOffsets(OffsetRanges);

/// One instruction normally supplies a single interval. Split intervals
/// share their storage when an expression is copied.
#[derive(Clone, Debug, Eq, PartialEq)]
enum OffsetRanges {
    Contiguous(Range<u32>),
    Disjoint(Arc<Vec<Range<u32>>>),
}

impl BytecodeOffsets {
    /// BitSet.length, one past the last marked bytecode position.
    pub(crate) fn length(&self) -> i32 {
        self.ranges().last().map_or(0, |range| range.end as i32)
    }

    /// Every byte of a decoded instruction contributes its position. Negative
    /// offsets belong to synthesized instructions.
    pub fn for_instruction(offset: i32, length: i32) -> Option<Self> {
        let start = u32::try_from(offset).ok()?;
        let length = u32::try_from(length).expect("Negative instruction length");
        let range = if length == 0 {
            0..0
        } else {
            start..start + length
        };
        Some(Self(OffsetRanges::Contiguous(range)))
    }

    pub fn iter(&self) -> impl Iterator<Item = u32> + '_ {
        self.ranges().iter().cloned().flatten()
    }

    pub fn union(&mut self, other: &Self) {
        if let (OffsetRanges::Contiguous(left), OffsetRanges::Contiguous(right)) =
            (&mut self.0, &other.0)
        {
            if right.is_empty() {
                return;
            }
            if Range::is_empty(left) {
                *left = right.clone();
                return;
            }
            if left.start <= right.end && right.start <= left.end {
                left.start = left.start.min(right.start);
                left.end = left.end.max(right.end);
                return;
            }
        }
        let left = self.ranges();
        let right = other.ranges();
        let mut ranges: Vec<Range<u32>> = Vec::with_capacity(left.len() + right.len());
        for range in left.iter().merge_by(right, |a, b| a.start <= b.start) {
            if range.is_empty() {
                continue;
            }
            if let Some(last) = ranges.last_mut()
                && range.start <= last.end
            {
                last.end = last.end.max(range.end);
            } else {
                ranges.push(range.clone());
            }
        }
        self.0 = if ranges.len() == 1 {
            OffsetRanges::Contiguous(ranges.pop().unwrap())
        } else {
            OffsetRanges::Disjoint(Arc::new(ranges))
        };
    }

    fn ranges(&self) -> &[Range<u32>] {
        match &self.0 {
            OffsetRanges::Contiguous(range) => std::slice::from_ref(range),
            OffsetRanges::Disjoint(ranges) => ranges,
        }
    }
}

impl Expr {
    /// `Exprent.addBytecodeOffsets`.
    pub fn add_offsets(ir: &mut Ir, dst: ExprId, src: Option<&BytecodeOffsets>) {
        let Some(src) = src else { return };
        match &mut ir[dst].bytecode {
            Some(existing) => existing.union(src),
            bytecode @ None => *bytecode = Some(src.clone()),
        }
    }

    /// `src.getBytecodeRange(dst.bytecode)` only updates an existing set.
    pub(crate) fn add_bytecode_range(ir: &mut Ir, dst: ExprId, src: ExprId) {
        if let Some(mut offsets) = ir[dst].bytecode.clone() {
            Self::measure_bytecode(ir, src, &mut offsets);
            ir[dst].bytecode = Some(offsets);
        }
    }

    fn measure_bytecode(ir: &Ir, expr: ExprId, offsets: &mut BytecodeOffsets) {
        match &ir[expr].kind {
            ExprKind::New {
                array_elements,
                dimensions,
                constructor,
                ..
            } => {
                // NewExprent includes the constructor's own offsets in its range.
                for &child in array_elements.iter().chain(dimensions).chain(constructor) {
                    Self::measure_bytecode(ir, child, offsets);
                }
            }
            ExprKind::SwitchHead { value, case_values } => {
                match case_values {
                    Some(SwitchCaseValues::Statement(stat)) => {
                        let StatementKind::Switch(switch) = &ir[*stat].kind else {
                            unreachable!("Switch header case values belong to a switch statement");
                        };
                        for &label in switch.case_values().flatten().flatten() {
                            Self::measure_bytecode(ir, label, offsets);
                        }
                    }
                    Some(SwitchCaseValues::Copied(cases)) => {
                        for &label in cases.iter().flatten().flatten() {
                            Self::measure_bytecode(ir, label, offsets);
                        }
                    }
                    None => {}
                }
                Self::measure_bytecode(ir, *value, offsets);
            }
            _ => {
                for child in Self::children(ir, expr) {
                    Self::measure_bytecode(ir, child, offsets);
                }
            }
        }
        if let Some(bytecode) = &ir[expr].bytecode {
            offsets.union(bytecode);
        }
    }
}
