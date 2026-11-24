use crate::{
    bytecode::{Instruction, Operand},
    classfile::find_attribute,
};

use super::{
    Effect, LiftError, Machine,
    expr::{Expr, Source},
};

impl Machine<'_, '_> {
    pub(super) fn invoke_constructor(
        &mut self,
        owner: &str,
        descriptor: &str,
        args: Vec<Expr>,
    ) -> Result<Effect, LiftError> {
        if !self.stack_is_empty() || !self.prelude.is_empty() {
            return Err(self.unsupported("constructor chaining with pending stack values"));
        }
        self.order_of(&args, true)?;
        let kind = self.constructor_invocation_kind(owner, descriptor)?;
        let (mut target, args) = self.constructor_target(owner, descriptor, &args, Some(kind))?;
        let args = if self.class.access_flags & 0x4000 != 0 && owner == self.owner {
            let [label, ordinal, visible @ ..] = args else {
                return Err(self.invalid_operand("missing implicit enum constructor arguments"));
            };
            if !matches!(label.source, Source::Local(1))
                || !matches!(ordinal.source, Source::Local(2))
            {
                return Err(self.unsupported("noncanonical enum constructor delegation"));
            }
            visible
        } else {
            args
        };
        self.initialized_this = true;
        target.append_relative_arguments(args.iter().map(|argument| &argument.text));
        target.push(';');
        Ok(Effect::Statement(target))
    }

    pub(super) fn check_instance_field_receiver(
        &mut self,
        receiver: &Expr,
        owner: &str,
        name: &str,
        descriptor: &str,
        write: bool,
    ) -> Result<(), LiftError> {
        let early = receiver.is_uninitialized(self.initialized_this);
        if early && (!write || owner != self.owner || !matches!(receiver.source, Source::This)) {
            return Err(self.invalid_stack("uninitialized receiver used before invokespecial"));
        }
        if !early && (self.early_final_fields.is_empty() || !write || owner != self.owner
            || !matches!(receiver.source, Source::This))
        {
            return Ok(());
        }
        let pool = &self.class.pool;
        for (index, field) in self.class.fields.iter().enumerate() {
            if pool.utf8(field.name_index)? != name || pool.utf8(field.descriptor_index)? != descriptor {
                continue;
            }
            if early && (field.access_flags & 0x0008 != 0
                || find_attribute(&field.attributes, pool, "ConstantValue")?.is_some()
                || (self.options.remove_synthetic && (field.access_flags & 0x1000 != 0
                    || find_attribute(&field.attributes, pool, "Synthetic")?.is_some())))
            {
                return Err(self.invalid_operand("early assignment requires a blank declared instance field"));
            }
            if self.early_final_fields.contains_key(&index) {
                return Err(self.invalid_operand("final instance field already assigned in constructor prologue"));
            }
            if early && field.access_flags & 0x0010 != 0 {
                self.early_final_fields.insert(index, true);
            }
            return Ok(());
        }
        if early {
            return Err(self.invalid_operand("early assignment requires a blank declared instance field"));
        }
        Ok(())
    }

    pub(super) fn constructor_invocation_kind(
        &self,
        owner: &str,
        descriptor: &str,
    ) -> Result<&'static str, LiftError> {
        let pool = &self.class.pool;
        let current = pool.utf8(self.method.descriptor_index)?;
        let delegates = owner == self.owner;
        if delegates {
            if descriptor == current {
                return Err(self.invalid_operand("constructor delegates to itself"));
            }
            if !self.early_final_fields.is_empty() {
                return Err(self.invalid_operand("alternate constructor invocation after early final field assignment"));
            }
        } else if self.super_class != Some(owner) {
            return Err(self.invalid_operand("constructor must target this class or its direct superclass"));
        }
        if self.super_class == Some("java/lang/Record")
            && let Some(components) = self.class.record_components()?
        {
            let mut remaining = current.strip_prefix('(');
            for component in components {
                let ty = pool.utf8(component.descriptor_index)?;
                remaining = remaining.and_then(|rest| rest.strip_prefix(ty));
            }
            let canonical = remaining == Some(")V");
            if canonical == delegates || (!delegates && descriptor != "()V") {
                return Err(self.invalid_operand("invalid record constructor delegation"));
            }
        }
        if self.class.access_flags & 0x4000 != 0 && self.super_class == Some("java/lang/Enum") {
            if !delegates {
                return Err(self.invalid_operand("explicit superclass invocation in enum constructor"));
            }
            if !descriptor.starts_with("(Ljava/lang/String;I") || !self.class.methods.iter().any(|method| {
                method.access_flags & 0x1000 == 0
                    && pool.utf8(method.name_index).is_ok_and(|name| name == "<init>")
                    && pool.utf8(method.descriptor_index).is_ok_and(|ty| ty == descriptor)
            }) {
                return Err(self.invalid_operand("invalid alternate enum constructor invocation"));
            }
        }
        Ok(if delegates { "this" } else { "super" })
    }

    pub(crate) fn may_chain_constructor(&self, instruction: &Instruction) -> bool {
        let (0xb7, Operand::Constant(index)) = (instruction.opcode, &instruction.operand) else {
            return false;
        };
        // A call to one of these owners may also belong to a `new`
        // expression. The lift still proves which receiver it consumes;
        // this check only rules out definitively pre-initialization tails.
        match self.class.pool.member_ref(*index) {
            Ok((owner, "<init>", _)) => owner == self.owner || Some(owner) == self.super_class,
            Ok(_) => false,
            Err(_) => true,
        }
    }

    pub(crate) fn requires_implicit_record_super(&self) -> Result<bool, LiftError> {
        Ok(self.super_class == Some("java/lang/Record")
            && self.class.record_components()?.is_some())
    }

    pub(super) fn merge_early_final_fields(&mut self, arms: &[&Self]) {
        // Absence means unassigned; the value records definite assignment.
        // Only normally completing arms contribute to the constructor join.
        if let Some((first, rest)) = arms.split_first() {
            self.early_final_fields.clone_from(&first.early_final_fields);
            for arm in rest {
                for (field, definite) in &mut self.early_final_fields {
                    *definite &= arm.early_final_fields.get(field).copied().unwrap_or(false);
                }
                for &field in arm.early_final_fields.keys() {
                    self.early_final_fields.entry(field).or_insert(false);
                }
            }
        }
    }
}
