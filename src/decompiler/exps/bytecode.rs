// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Bytecode position sets attached to expressions.

use std::ops::Range;
use std::sync::Arc;

use itertools::Itertools;

use super::Expr;
use crate::decompiler::ir::{ExprId, Ir};

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
}
