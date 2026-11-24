use std::collections::BTreeSet;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{Constant, VerificationType, find_attribute, initial_stack_map_locals},
    descriptor::{MethodDescriptor, Type},
};

use super::{
    Effect, LiftError, Machine,
    expr::{Category, Expr, Source},
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

    pub(crate) fn has_constructor_switch_receiver(&self) -> bool {
        !self.initialized_this && matches!(self.stack.as_slice(), [receiver]
            if matches!(receiver.source, Source::This) && receiver.order.is_none())
    }

    /// The synthetic dispatch and the arms must carry the same uninitialized
    /// receiver underneath their temporary values, never as a Java operand.
    /// Every real branch target must supply that identity in its verifier frame.
    pub(crate) fn proves_constructor_switch(
        &self,
        instructions: &[Instruction],
        consumer: &Instruction,
    ) -> bool {
        let prove = || {
            if !self.has_constructor_switch_receiver() || self.normalized.is_some()
                || consumer.opcode != 0xb7 || self.max_stack < 3
            {
                return None;
            }
            let Operand::Constant(index) = consumer.operand else { return None };
            let pool = &self.class.pool;
            if !matches!(pool.get(index).ok()?, Constant::Methodref { .. }) {
                return None;
            }
            let (owner, "<init>", descriptor) = pool.member_ref(index).ok()? else { return None };
            self.constructor_invocation_kind(owner, descriptor).ok()?;
            let descriptor = MethodDescriptor::parse(descriptor).ok()?;
            let [expected] = descriptor.parameters.as_slice() else { return None };
            if descriptor.return_type != Type::Void {
                return None;
            }
            let first = instructions.first()?.offset;
            let end = consumer.offset;
            let mut targets = BTreeSet::new();
            for op in instructions {
                // The actual receiver load preceded the selector. Slot zero
                // is not used again by the skipped dispatch or any rule.
                if matches!((op.opcode, &op.operand),
                    (0x1a | 0x1e | 0x22 | 0x26 | 0x2a | 0x3b | 0x3f | 0x43 | 0x47 | 0x4b, _)
                    | (0x15..=0x19 | 0x36..=0x3a, Operand::Local(0))
                    | (0x84, Operand::Increment { index: 0, .. }))
                {
                    return None;
                }
                match &op.operand {
                    Operand::Branch(target) => { targets.insert(*target); }
                    Operand::Switch { default, cases } => {
                        targets.insert(*default);
                        targets.extend(cases.iter().map(|&(_, target)| target));
                    }
                    _ => {}
                }
            }
            if targets.first().is_none_or(|&target| target < first)
                || targets.last().is_some_and(|&target| target > end)
            {
                return None;
            }
            let initial = initial_stack_map_locals(self.class, self.method, self.descriptor).ok()?;
            let raw = crate::bytecode::decode(self.code.bytes).ok()?;
            let mut valid = true;
            self.code.visit_stack_map_frames(pool, &initial, Some(&raw), |frame| {
                let offset = u32::from(frame.offset);
                if !(first..=end).contains(&offset) {
                    return;
                }
                targets.remove(&offset);
                valid &= frame.local(0) == VerificationType::UninitializedThis
                    && !frame.locals.get(1..).unwrap_or_default().contains(&VerificationType::UninitializedThis)
                    && match frame.stack {
                        [VerificationType::UninitializedThis] => offset != end,
                        [VerificationType::UninitializedThis, value] if offset == end => {
                            self.constructor_switch_frame_value(*value, expected)
                        }
                        _ => false,
                    };
            }).ok()?;
            (valid && targets.is_empty()).then_some(())
        };
        prove().is_some()
    }

    fn constructor_switch_frame_value(&self, value: VerificationType<'_>, expected: &Type) -> bool {
        match (value, Category::of(expected)) {
            (VerificationType::Integer, Some(Category::Int))
            | (VerificationType::Long, Some(Category::Long))
            | (VerificationType::Float, Some(Category::Float))
            | (VerificationType::Double, Some(Category::Double))
            | (VerificationType::Null, Some(Category::Ref)) => true,
            (VerificationType::Object(index), Some(Category::Ref)) => {
                self.class_type(index).is_ok_and(|ty| self.known_assignable(&ty, expected))
            }
            (VerificationType::DescriptorReference(ty), Some(Category::Ref)) => {
                self.known_assignable(ty, expected)
            }
            _ => false,
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
