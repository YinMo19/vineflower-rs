// Based on Vineflower's enum constant initializer recovery (Apache-2.0).

use std::ops::Range;

use crate::{
    bytecode::Instruction, descriptor::MethodDescriptor, source_text::Document,
    structure::enum_argument_switch,
};

use super::{Effect, LiftError, Machine};

struct Span {
    /// Lowest stack entry participating in the operation, later reduced to
    /// the surviving source argument that contains this evaluation.
    argument: usize,
    bytes: Range<u32>,
}

impl Machine<'_, '_> {
    /// The supplied slice omits `new`, its duplicate, and the two mandatory JVM
    /// enum constructor arguments. Only an ordered, self-contained expression
    /// for each source parameter may migrate to the constant declaration. The
    /// result holds the grouped parentheses, or is empty for a bare constant.
    pub(crate) fn enum_constant_arguments(
        &mut self,
        instructions: &[Instruction],
        constructor_offset: u32,
        user_arguments: &MethodDescriptor,
        map_offsets: bool,
    ) -> Result<Document, LiftError> {
        let mut spans = map_offsets.then(Vec::new);
        let mut remaining = instructions;
        while let Some((op, rest)) = remaining.split_first() {
            let shuffled = if map_offsets {
                self.enum_shuffle_floor(op)?
            } else {
                None
            };
            remaining = if matches!(op.opcode, 0xaa | 0xab) {
                let consumed =
                    enum_argument_switch(self, remaining, constructor_offset, map_offsets)?
                        .ok_or_else(|| {
                            self.unsupported("enum constant switch has no independent value join")
                        })?;
                &remaining[consumed..]
            } else {
                if !matches!(self.step(op)?, Effect::None) || !self.prelude.is_empty() {
                    return Err(self.unsupported(
                        "enum constant arguments require expression-only evaluation",
                    ));
                }
                rest
            };
            if let Some(spans) = &mut spans {
                let depth = self.stack.len();
                let visible = self.instruction_has_source();
                // An expression-only operation places its result at the top;
                // a stack permutation may also touch earlier entries. A nop
                // does not connect otherwise independent arguments.
                let argument = shuffled.unwrap_or_else(|| {
                    if op.opcode == 0 { depth } else { depth.saturating_sub(1) }
                });
                spans.push(Span {
                    argument,
                    bytes: if visible { op.offset..op.offset + op.len } else { 0..0 },
                });
            }
        }
        let values = self.arguments(user_arguments, None)?;
        if !self.stack_is_empty() {
            return Err(self.invalid_stack("enum constant arguments leave unused operands"));
        }
        self.order_of(&values, false)?;
        if values.is_empty() {
            return Ok(Document::new());
        }
        let Some(mut spans) = spans else {
            return Ok(Document::relative_delimited(values.into_iter().map(|value| value.text)));
        };
        // When a later instruction combines two operands, the earlier
        // producer belongs to the combined argument rather than the
        // temporary stack position it originally occupied.
        let mut floor = values.len();
        for span in spans.iter_mut().rev() {
            floor = floor.min(span.argument);
            span.argument = floor;
        }
        let mut remaining = spans.into_iter().peekable();
        Ok(Document::relative_delimited_with(
            values.into_iter().enumerate(),
            |doc, (index, value)| {
                let mut run: Option<Range<u32>> = None;
                while let Some(span) = remaining.next_if(|span| span.argument == index) {
                    if span.bytes.is_empty() {
                        continue;
                    }
                    if let Some(previous) = &mut run
                        && previous.end == span.bytes.start
                    {
                        previous.end = span.bytes.end;
                    } else if let Some(previous) = run.replace(span.bytes) {
                        doc.anchor(previous);
                    }
                }
                if let Some(run) = run {
                    doc.anchor(run);
                }
                doc.append(value.text);
            },
        ))
    }

    fn enum_shuffle_floor(&self, op: &Instruction) -> Result<Option<usize>, LiftError> {
        match op.opcode {
            0x59..=0x5e => {
                let relative = op.opcode - 0x59;
                let duplicated = self.group(self.stack.len(), 1 + relative / 3)?;
                Ok(Some(self.group(duplicated, relative % 3)?))
            }
            0x5f => Ok(Some(self.group(self.stack.len(), 2)?)),
            _ => Ok(None),
        }
    }
}
