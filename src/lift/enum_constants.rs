// Based on Vineflower's enum constant initializer recovery (Apache-2.0).

use crate::{bytecode::Instruction, descriptor::MethodDescriptor, source_text::Document};

use super::{Effect, LiftError, Machine};

impl Machine<'_, '_> {
    /// The supplied slice omits `new`, its duplicate, and the two mandatory JVM
    /// enum constructor arguments. Only an ordered, self-contained expression
    /// for each source parameter may migrate to the constant declaration. The
    /// result holds the grouped parentheses, or is empty for a bare constant.
    pub(crate) fn enum_constant_arguments(
        &mut self,
        instructions: &[Instruction],
        user_arguments: &MethodDescriptor,
    ) -> Result<Document, LiftError> {
        for op in instructions {
            if !matches!(self.step(op)?, Effect::None) || !self.prelude.is_empty() {
                return Err(
                    self.unsupported("enum constant arguments require expression-only evaluation")
                );
            }
        }
        let values = self.arguments(user_arguments, None)?;
        if !self.stack_is_empty() {
            return Err(self.invalid_stack("enum constant arguments leave unused operands"));
        }
        self.order_of(&values, false)?;
        Ok(if values.is_empty() {
            Document::new()
        } else {
            Document::relative_delimited(values.into_iter().map(|value| value.text))
        })
    }
}
