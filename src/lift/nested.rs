// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::{ClassError, find_attribute},
    context::NestedKind,
    descriptor::{MethodDescriptor, Type},
    source_text::Document,
};

mod field_accessor;

use super::{
    Effect, LiftError, Machine,
    expr::{Category, Expr, PRIMARY, Source},
};

impl<'a, 'c> Machine<'a, 'c> {
    pub(super) fn lexical_parameter(&self, index: u16) -> Option<Expr> {
        if let Some(capture) = self.captured_parameter(index) {
            return Some(capture);
        }
        let group = self.group.filter(|_| self.options.decompile_inner)?;
        if index != 1 || self.method_name != "<init>" || !group.is_attached(self.owner) {
            return None;
        }
        let outer = group.enclosing_instance(self.owner)?;
        match self.descriptor.parameters.first() {
            Some(Type::Object(name)) if name == outer => Some(self.outer_this(outer)),
            _ => None,
        }
    }

    fn outer_this(&self, outer: &str) -> Expr {
        let mut text = self.class_reference(outer);
        text.push_str(".this");
        Expr {
            source: Source::OuterThis,
            ..Expr::atom(Type::Object(outer.into()), text)
        }
    }

    pub(super) fn synthetic_outer_access(
        &mut self,
        owner: &str,
        name: &str,
        descriptor: &str,
        receiver: &Expr,
        value: Option<&Expr>,
    ) -> Result<Option<Effect>, LiftError> {
        let Some(group) = self.group.filter(|_| self.options.decompile_inner) else {
            return Ok(None);
        };
        if !group.is_attached(self.owner) {
            return Ok(None);
        }
        let Some(outer) = group.outer_field(owner, name, descriptor) else {
            return Ok(None);
        };
        let lexical_receiver = matches!(receiver.source, Source::This | Source::OuterThis)
            && matches!(&receiver.ty, Type::Object(receiver_owner) if receiver_owner == owner);
        if !lexical_receiver {
            return Err(
                self.unsupported("access to a different object's synthetic enclosing instance")
            );
        }
        if let Some(value) = value {
            if self.method_name != "<init>"
                || !matches!(receiver.source, Source::This)
                || !matches!(value.source, Source::OuterThis)
                || !matches!(&value.ty, Type::Object(name) if name == outer)
            {
                return Err(self.unsupported("noninitial synthetic enclosing-instance field write"));
            }
        } else {
            self.push(self.outer_this(outer))?;
        }
        Ok(Some(Effect::None))
    }

    /// Return the Java constructor head and the JVM arguments that remain
    /// visible after removing its implicit enclosing instance.
    pub(super) fn constructor_target<'args>(
        &self,
        owner: &str,
        descriptor: &str,
        args: &'args [Expr],
        target: Option<&str>,
    ) -> Result<(Document, &'args [Expr]), LiftError> {
        let plain = || {
            target.map_or_else(
                || {
                    let mut head = Document::from("new ");
                    head.append(self.class_reference(owner));
                    head
                },
                Document::from,
            )
        };
        let Some(group) = self.group.filter(|_| self.options.decompile_inner) else {
            return Ok((plain(), args));
        };
        if owner == self.owner && !group.is_attached(owner) {
            return Ok((plain(), args));
        }
        let args = self.legacy_constructor_arguments(owner, descriptor, args)?;
        let args = self.local_constructor_arguments(owner, descriptor, args)?;
        if target.is_none()
            && group.is_attached(owner)
            && let Some(class) = group.nested_class(owner)
        {
            match class.kind {
                NestedKind::Anonymous => return Err(self.unsupported("anonymous class body")),
                NestedKind::Local(_) if class.method.is_none() => {
                    return Err(self.unsupported("local class in a field initializer"));
                }
                _ => {}
            }
        }
        let Some(outer) = group.constructor_outer(owner, descriptor) else {
            return Ok((plain(), args));
        };
        let (receiver, visible_args) = args.split_first().ok_or_else(|| {
            self.invalid_operand("inner class constructor has no enclosing-instance argument")
        })?;
        let mut scope = match target {
            Some(_) => group.enclosing_instance(self.owner),
            None => Some(self.owner),
        };
        let mut default_instance = None;
        while let Some(candidate) = scope {
            if group.is_assignable(candidate, outer) {
                default_instance = Some(candidate);
                break;
            }
            scope = group.enclosing_instance(candidate);
        }
        let implicit = matches!(receiver.source, Source::This | Source::OuterThis)
            && matches!(&receiver.ty, Type::Object(ty) if Some(ty.as_str()) == default_instance);
        if implicit
            && (target.is_some()
                || matches!(receiver.source, Source::This)
                || self.unnamed_enclosing_receiver(receiver)
                || group.member_class(owner).is_none())
        {
            return Ok((plain(), visible_args));
        }
        let head = match target {
            Some("super") => {
                let mut head = receiver.at(PRIMARY).into_owned();
                head.push_str(".super");
                head
            }
            Some(_) => {
                return Err(self.unsupported("constructor delegation changes enclosing instance"));
            }
            None => {
                let Some(member) = group.member_class(owner) else {
                    return Err(
                        self.unsupported("local class construction changes enclosing instance")
                    );
                };
                let name = self
                    .renames
                    .and_then(|plan| plan.simple_class_alias(owner))
                    .unwrap_or(member.simple_name);
                let mut head = receiver.at(PRIMARY).into_owned();
                head.push_str(".new ");
                self.append_class_reference(&mut head, name, owner);
                head
            }
        };
        Ok((head, visible_args))
    }

    /// Some pre-nestmate ECJ inputs name the enclosing class in the
    /// Methodref for a synthetic member-class constructor.
    pub(super) fn relocated_legacy_constructor(
        &self,
        symbolic_owner: &str,
        raw: &str,
        descriptor: &MethodDescriptor,
        arguments: &[Expr],
    ) -> Result<Option<&'c str>, LiftError> {
        if !self.options.ignore_invalid_bytecode || self.class.major_version >= 55 {
            return Ok(None);
        }
        let Some(group) = self.group.filter(|_| self.options.decompile_inner) else {
            return Ok(None);
        };
        let ([Type::Object(outer), Type::Object(marker)], [enclosing, null]) =
            (descriptor.parameters.as_slice(), arguments)
        else {
            return Ok(None);
        };
        let Some(receiver) = self.stack.last() else { return Ok(None) };
        let Type::Object(allocated) = &receiver.ty else { return Ok(None) };
        if !matches!(receiver.source, Source::New(_))
            || !matches!(null.source, Source::Null)
            || !matches!(&enclosing.ty, Type::Object(actual) if actual == outer)
            || allocated == symbolic_owner
            || outer != symbolic_owner
            || marker != allocated
            || group.constructor_outer(allocated, raw) != Some(symbolic_owner)
            || !group.is_attached(allocated)
        {
            return Ok(None);
        }
        let (Some(original), Some(inner)) = (group.get(symbolic_owner), group.get(allocated)) else {
            return Ok(None);
        };
        for method in &original.methods {
            if original.pool.utf8(method.name_index)? == "<init>"
                && original.pool.utf8(method.descriptor_index)? == raw
            {
                return Ok(None);
            }
        }
        if self.legacy_constructor_descriptor(allocated, raw)?.is_none() {
            return Ok(None);
        }
        Ok(Some(inner.pool.class_name(inner.this_class)?))
    }

    /// Pre-nestmate javac used a synthetic forwarding constructor with an
    /// extra, unused anonymous marker argument for private nest access.
    fn legacy_constructor_arguments<'args>(
        &self,
        owner: &str,
        descriptor: &str,
        args: &'args [Expr],
    ) -> Result<&'args [Expr], LiftError> {
        if self
            .legacy_constructor_descriptor(owner, descriptor)?
            .is_none()
        {
            return Ok(args);
        }
        let Some((marker_value, args)) = args.split_last() else {
            return Err(self.invalid_operand("missing synthetic constructor argument"));
        };
        if marker_value.observable {
            return Err(self.unsupported("observable synthetic constructor marker"));
        }
        Ok(args)
    }

    pub(super) fn legacy_constructor_descriptor(
        &self,
        owner: &str,
        descriptor: &str,
    ) -> Result<Option<&str>, LiftError> {
        let Some(group) = self.group else {
            return Ok(None);
        };
        let Some(class) = group.get(owner) else {
            return Ok(None);
        };
        if group.compilation_root(self.owner) != group.compilation_root(owner) {
            return Ok(None);
        }
        let pool = &class.pool;
        let mut code = None;
        for method in &class.methods {
            if pool.utf8(method.name_index)? == "<init>"
                && pool.utf8(method.descriptor_index)? == descriptor
                && (method.access_flags & 0x1000 != 0
                    || find_attribute(&method.attributes, pool, "Synthetic")?.is_some())
            {
                code = method.code(pool)?;
                break;
            }
        }
        let Some(code) = code else { return Ok(None) };
        if !code.exceptions.is_empty() {
            return Ok(None);
        }
        let signature = MethodDescriptor::parse(descriptor)?;
        let Some((Type::Object(marker), parameters)) = signature.parameters.split_last() else {
            return Ok(None);
        };
        // Older javac may use an empty synthetic marker or an actual
        // anonymous class already in the nest. The complete trivial bridge
        // body below, not absence of methods on the marker type, is the proof.
        let anonymous_marker = group.compilation_root(marker) == group.compilation_root(owner)
            && group.nested_class(marker)
                .is_some_and(|node| matches!(node.kind, NestedKind::Anonymous));
        let ecj_marker = self.options.ignore_invalid_bytecode
            && class.major_version < 55
            && marker == owner
            && group.constructor_outer(owner, descriptor).is_some();
        if !anonymous_marker && !ecj_marker {
            return Ok(None);
        }
        let Ok(instructions) = bytecode::decode(code.bytes) else {
            return Ok(None);
        };
        let [receiver, loads @ .., call, ret] = instructions.as_slice() else {
            return Ok(None);
        };
        if receiver.opcode != 0x2a
            || call.opcode != 0xb7
            || ret.opcode != 0xb1
            || loads.len() != parameters.len()
        {
            return Ok(None);
        }
        let mut slot = 1;
        for (load, ty) in loads.iter().zip(parameters) {
            if parameter_load_slot(load, ty).map(usize::from) != Some(slot) {
                return Ok(None);
            }
            slot += usize::from(ty.slots());
        }
        let Operand::Constant(index) = call.operand else {
            return Ok(None);
        };
        let (target_owner, target, desc) = pool.member_ref(index)?;
        if target_owner != owner
            || target != "<init>"
            || !private_instance_method(class, target, desc)?
        {
            return Ok(None);
        }
        let target = MethodDescriptor::parse(desc)?;
        if target.parameters.as_slice() != parameters || target.return_type != Type::Void {
            return Ok(None);
        }
        Ok(Some(desc))
    }

    pub(super) fn unnamed_enclosing_receiver(&self, receiver: &Expr) -> bool {
        matches!(receiver.source, Source::OuterThis)
            && matches!(&receiver.ty, Type::Object(owner)
                if self.group.is_some_and(|group| group.is_attached(owner)
                    && group.nested_class(owner).is_some_and(|node| matches!(node.kind, NestedKind::Anonymous))))
    }

    pub(super) fn synthetic_nest_accessor(
        &mut self,
        owner: &str,
        name: &str,
        descriptor: &str,
        signature: &MethodDescriptor,
        args: &[Expr],
    ) -> Result<Option<Effect>, LiftError> {
        let Some(group) = self.group.filter(|_| self.options.decompile_inner) else {
            return Ok(None);
        };
        if !name.starts_with("access$") {
            return Ok(None);
        }
        let Some(class) = group.get(owner) else {
            return Ok(None);
        };
        let pool = &class.pool;
        let mut accessor = None;
        for method in &class.methods {
            if method.access_flags & 0x0008 != 0
                && pool.utf8(method.name_index)? == name
                && pool.utf8(method.descriptor_index)? == descriptor
                && (method.access_flags & 0x1000 != 0
                    || find_attribute(&method.attributes, pool, "Synthetic")?.is_some())
            {
                accessor = Some(method);
                break;
            }
        }
        let Some(accessor) = accessor else {
            return Ok(None);
        };
        let fail = || self.unsupported("unproven synthetic nest accessor");
        if group.compilation_root(owner) != group.compilation_root(self.owner)
            || accessor.access_flags & 0x0020 != 0
        {
            return Err(fail());
        }
        let code = accessor.code(pool)?.ok_or_else(fail)?;
        if !code.exceptions.is_empty()
            || signature.parameters.iter().map(Type::slots).sum::<u16>() > code.max_locals
        {
            return Err(fail());
        }
        let instructions = bytecode::decode(code.bytes).map_err(|_| fail())?;
        let Some((ret, before_return)) = instructions.split_last() else {
            return Err(fail());
        };
        if return_opcode(&signature.return_type) != ret.opcode {
            return Err(fail());
        }
        let Some((member, loads)) = before_return.split_last() else {
            return Err(fail());
        };
        if matches!(member.opcode, 0xb2..=0xb5) {
            let field = field_accessor::FieldAccessor::recognize(
                class,
                owner,
                signature,
                before_return,
                code.max_stack,
            )?
            .ok_or_else(fail)?;
            return self.emit_field_accessor(owner, signature, args, field).map(Some);
        }
        if loads.len() != signature.parameters.len() || !matches!(member.opcode, 0xb6..=0xb9) {
            return Err(fail());
        }
        let mut slot = 0;
        for (load, ty) in loads.iter().zip(&signature.parameters) {
            if parameter_load_slot(load, ty) != Some(slot) {
                return Err(fail());
            }
            slot += ty.slots();
        }
        let index = match member.operand {
            Operand::Constant(index) | Operand::InvokeInterface { index, .. } => index,
            _ => return Err(fail()),
        };
        let (target_owner, name, target_descriptor) = pool.member_ref(index)?;
        // A special call to a superclass, or a forwarding method into a
        // different class, cannot be replaced with normal virtual dispatch.
        if target_owner != owner || name.starts_with('<') {
            return Err(fail());
        }
        let is_static = member.opcode == 0xb8;
        let skip = usize::from(!is_static);
        let (mut qualifier, passed) = if is_static {
            (self.class_reference(owner), args)
        } else {
            let Some((receiver, passed)) = args.split_first() else {
                return Err(fail());
            };
            if !matches!(signature.parameters.first(), Some(Type::Object(ty)) if ty == owner) {
                return Err(fail());
            }
            (receiver.at(PRIMARY).into_owned(), passed)
        };
        let target = MethodDescriptor::parse(target_descriptor)?;
        if signature.parameters[skip..] != target.parameters
            || signature.return_type != target.return_type
            || (member.opcode == 0xb7 && !private_instance_method(class, name, target_descriptor)?)
        {
            return Err(fail());
        }
        self.record_synthetic_invocation(owner, name, target_descriptor);
        let source = self.source_invocation_name(owner, name, target_descriptor);
        qualifier.push('.');
        self.append_method_reference(&mut qualifier, &source, owner, name, target_descriptor);
        qualifier.append_relative_arguments(passed.iter().map(|arg| &arg.text));
        if target.return_type == Type::Void {
            let order = self.order_of(args, true)?;
            self.before_statement(order)?;
            qualifier.push(';');
            return Ok(Some(Effect::Statement(qualifier)));
        }
        let expression = self.expression(target.return_type, qualifier, PRIMARY, args, true)?;
        self.push(Expr {
            statement: true,
            ..expression
        })?;
        Ok(Some(Effect::None))
    }
}

pub(super) fn parameter_load_slot(instruction: &Instruction, ty: &Type) -> Option<u16> {
    let category = match Category::of(ty)? {
        Category::Int => 0,
        Category::Long => 1,
        Category::Float => 2,
        Category::Double => 3,
        Category::Ref => 4,
    };
    if instruction.opcode == 0x15 + category {
        if let Operand::Local(slot) = instruction.operand {
            return Some(slot);
        }
        return None;
    }
    let base = 0x1a + 4 * category;
    (base..base + 4)
        .contains(&instruction.opcode)
        .then(|| u16::from(instruction.opcode - base))
}

fn return_opcode(ty: &Type) -> u8 {
    match Category::of(ty) {
        Some(Category::Int) => 0xac,
        Some(Category::Long) => 0xad,
        Some(Category::Float) => 0xae,
        Some(Category::Double) => 0xaf,
        Some(Category::Ref) => 0xb0,
        None => 0xb1,
    }
}

fn private_instance_method(
    class: &crate::classfile::ClassFile<'_>,
    name: &str,
    descriptor: &str,
) -> Result<bool, ClassError> {
    for method in &class.methods {
        if method.access_flags & (0x0002 | 0x0008) == 0x0002
            && class.pool.utf8(method.name_index)? == name
            && class.pool.utf8(method.descriptor_index)? == descriptor
        {
            return Ok(true);
        }
    }
    Ok(false)
}
