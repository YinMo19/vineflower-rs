// Based on Vineflower's enum constant initializer recovery (Apache-2.0).

use crate::{bytecode::Instruction, descriptor::MethodDescriptor};

use super::{Effect, LiftError, Machine, members::render_arguments};

impl Machine<'_, '_> {
    /// The supplied slice omits `new`, its duplicate, and the two mandatory JVM
    /// enum constructor arguments. Only an ordered, self-contained expression
    /// for each source parameter may migrate to the constant declaration.
    pub(crate) fn enum_constant_arguments(
        &mut self,
        instructions: &[Instruction],
        user_arguments: &MethodDescriptor,
    ) -> Result<String, LiftError> {
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
        Ok(render_arguments(&values))
    }
}
