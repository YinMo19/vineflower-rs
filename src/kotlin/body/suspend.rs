// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Recognize a capture-free Kotlin/JVM suspend lambda with only the initial
//! state. No compiler scaffolding is dropped until all its entry points and
//! both switch arms have been matched.

use crate::{
    context::{ClassGroup, NestedKind},
    kotlin::{Declaration, model::CONTINUATION, read_metadata},
};

use super::{
    Assignment, Bytecode, Constant, Expr, ExprKind, FINAL, Instruction, JvmType, KotlinError,
    Locals, Member, MethodDescriptor, Operand, Property, STATIC, Type, bytecode, local_load,
    statements, templates,
};

pub(super) const FUNCTION1: &str = "kotlin/jvm/functions/Function1";
const FUNCTION1_FIELD: &str = "Lkotlin/jvm/functions/Function1;";
const SUSPEND_LAMBDA: &str = "kotlin/coroutines/jvm/internal/SuspendLambda";
const CONSTRUCTOR: &str = "(Lkotlin/coroutines/Continuation;)V";
const CREATE: &str = "(Lkotlin/coroutines/Continuation;)Lkotlin/coroutines/Continuation;";
const INVOKE: &str = "(Lkotlin/coroutines/Continuation;)Ljava/lang/Object;";
const ERASED_INVOKE: &str = "(Ljava/lang/Object;)Ljava/lang/Object;";
const PUBLIC: u16 = 0x0001;
const SUPER: u16 = 0x0020;
const BRIDGE: u16 = 0x0040;
const SYNTHETIC: u16 = 0x1000;

pub(super) const COROUTINE_MARKER: (&str, &str, &str) = (
    "kotlin/coroutines/intrinsics/IntrinsicsKt", "getCOROUTINE_SUSPENDED", "()Ljava/lang/Object;",
);
pub(super) const THROW_ON_FAILURE: (&str, &str, &str) = (
    "kotlin/ResultKt", "throwOnFailure", "(Ljava/lang/Object;)V",
);

pub(super) fn unit_return(ty: &Type) -> Option<&Type> {
    let (parameters, returns) = ty.suspend_signature()?;
    (parameters.is_empty()
        && ty.annotations.is_empty()
        && !returns.nullable
        && returns.simple_class("kotlin/Unit")
        && returns.arguments.is_empty())
        .then_some(returns)
}

impl<'a, 'data> Bytecode<'a, 'data> {
    pub(in crate::kotlin) fn package_initialization(
        &self,
        member: &Member<'data>,
        descriptor: &MethodDescriptor,
        group: &'a ClassGroup<'data>,
        properties: &[Property],
    ) -> Result<Vec<Assignment<'a>>, KotlinError> {
        if !properties.iter().any(|property| suspend_property(property).is_some()) {
            return self.initialization(member, descriptor, &[], None, self.owner);
        }
        let invalid = || KotlinError::unsupported(self.owner, "unproven Kotlin package initializer");
        let instructions = self.instructions(member, self.owner)?;
        let Some((ret, code)) = instructions.split_last() else { return Err(invalid()); };
        if member.access_flags != STATIC || ret.opcode != 0xb1 {
            return Err(invalid());
        }
        let mut assignments = Vec::new();
        let mut first = 0;
        let mut index = 0;
        while index < code.len() {
            if code[index].opcode == 0xbb
                && let Some((assignment, consumed)) = self.suspend_assignment(&code[index..], group, properties)?
            {
                assignments.extend(self.static_assignments(&code[first..index], self.owner)?);
                assignments.push(assignment);
                index += consumed;
                first = index;
            } else {
                index += 1;
            }
        }
        assignments.extend(self.static_assignments(&code[first..], self.owner)?);
        Ok(assignments)
    }

    fn suspend_assignment(
        &self,
        code: &[Instruction],
        group: &'a ClassGroup<'data>,
        properties: &[Property],
    ) -> Result<Option<(Assignment<'a>, usize)>, KotlinError> {
        let [new, dup, null, init, after @ ..] = code else { return Ok(None); };
        let (after, cast) = match after {
            [cast, after @ ..] if cast.opcode == 0xc0 => (after, Some(cast)),
            _ => (after, None),
        };
        let [put, ..] = after else { return Ok(None); };
        let Some((owner, field, descriptor)) = self.reference(put, 0xb3)? else { return Ok(None); };
        if owner != self.owner || descriptor != FUNCTION1_FIELD {
            return Ok(None);
        }
        let Some((property, returns)) = properties.iter().find_map(|property| {
            suspend_property(property)
                .filter(|(name, _)| *name == field)
                .map(|(_, returns)| (property, returns))
        }) else {
            return Ok(None);
        };
        let invalid = || KotlinError::unsupported(&property.name, "unproven suspend lambda allocation");
        let closure = class_operand(self, new, 0xbb)?.ok_or_else(invalid)?;
        if dup.opcode != 0x59 || null.opcode != 0x01
            || self.reference(init, 0xb7)? != Some((closure, "<init>", CONSTRUCTOR))
            || matches!(cast, Some(cast) if class_operand(self, cast, 0xc0)? != Some(FUNCTION1))
        {
            return Err(invalid());
        }
        let class = group.get(closure).ok_or_else(invalid)?;
        if !group.is_attached(closure)
            || group.nested_class(closure).is_none_or(|node| {
                node.outer != self.owner || node.method.is_some() || !matches!(node.kind, NestedKind::Anonymous)
            })
        {
            return Err(invalid());
        }
        let body = Bytecode { class, owner: closure };
        let statements = body.suspend_closure(returns, properties, &property.name)?;
        Ok(Some((Assignment {
            field,
            descriptor,
            value: Expr { kind: ExprKind::SuspendClosure(statements), depth: 1 },
            rhs_offsets: Some(new.offset..put.offset),
        }, 5 + usize::from(cast.is_some()))))
    }

    fn suspend_closure(
        &self,
        returns: &Type,
        properties: &[Property],
        declaration: &str,
    ) -> Result<Vec<statements::Statement<'a>>, KotlinError> {
        let invalid = || KotlinError::unsupported(declaration, "unproven capture-free suspend lambda class");
        let pool = &self.class.pool;
        let [interface] = self.class.interfaces.as_slice() else { return Err(invalid()); };
        let [state] = self.class.fields.as_slice() else { return Err(invalid()); };
        if self.class.access_flags != FINAL | SUPER || self.class.super_class == 0
            || pool.class_name(self.class.super_class)? != SUSPEND_LAMBDA
            || pool.class_name(*interface)? != FUNCTION1
            || state.access_flags != 0 || pool.utf8(state.descriptor_index)? != "I"
            || self.class.methods.len() != 5
        {
            return Err(invalid());
        }
        let metadata = read_metadata(self.class)?.ok_or_else(invalid)?;
        let Declaration::Synthetic(Some(function)) = &metadata.declaration else { return Err(invalid()); };
        if function.name != "<anonymous>" || function.returns != *returns || function.has_contract
            || function.receiver.is_some() || !function.parameters.is_empty()
            || !function.type_parameters.is_empty() || !function.context_receivers.is_empty()
            || !function.context_parameters.is_empty()
        {
            return Err(invalid());
        }

        let ctor = self.suspend_method("<init>", CONSTRUCTOR, 0, declaration)?;
        let ctor = self.instructions(ctor, declaration)?;
        let create = self.suspend_method("create", CREATE, PUBLIC | FINAL, declaration)?;
        let create = self.instructions(create, declaration)?;
        let invoke = self.suspend_method("invoke", INVOKE, PUBLIC | FINAL, declaration)?;
        let invoke = self.instructions(invoke, declaration)?;
        let bridge = self.suspend_method("invoke", ERASED_INVOKE, PUBLIC | BRIDGE | SYNTHETIC, declaration)?;
        let bridge = self.instructions(bridge, declaration)?;
        if !matches!(ctor.as_slice(), [this, arity, completion, super_call, ret]
            if aload(this, 0) && arity.opcode == 0x04 && aload(completion, 1) && ret.opcode == 0xb1
                && self.reference(super_call, 0xb7)? == Some((SUSPEND_LAMBDA, "<init>", "(ILkotlin/coroutines/Continuation;)V")))
            || !matches!(create.as_slice(), [new, dup, completion, call, cast, ret]
                if class_operand(self, new, 0xbb)? == Some(self.owner) && dup.opcode == 0x59
                    && aload(completion, 1) && self.reference(call, 0xb7)? == Some((self.owner, "<init>", CONSTRUCTOR))
                    && class_operand(self, cast, 0xc0)? == Some(CONTINUATION) && ret.opcode == 0xb0)
            || !matches!(invoke.as_slice(), [this, completion, create, cast, unit, call, ret]
                if aload(this, 0) && aload(completion, 1)
                    && self.reference(create, 0xb6)? == Some((self.owner, "create", CREATE))
                    && class_operand(self, cast, 0xc0)? == Some(self.owner) && self.unit(unit)?
                    && self.reference(call, 0xb6)? == Some((self.owner, "invokeSuspend", ERASED_INVOKE)) && ret.opcode == 0xb0)
            || !matches!(bridge.as_slice(), [this, completion, cast, call, ret]
                if aload(this, 0) && aload(completion, 1) && class_operand(self, cast, 0xc0)? == Some(CONTINUATION)
                    && self.reference(call, 0xb6)? == Some((self.owner, "invoke", INVOKE)) && ret.opcode == 0xb0)
        {
            return Err(invalid());
        }
        let resume = self.suspend_method("invokeSuspend", ERASED_INVOKE, PUBLIC | FINAL, declaration)?;
        self.initial_state(resume, pool.utf8(state.name_index)?, properties, declaration)
    }

    fn initial_state(
        &self,
        member: &Member<'data>,
        state: &str,
        properties: &[Property],
        declaration: &str,
    ) -> Result<Vec<statements::Statement<'a>>, KotlinError> {
        let invalid = || KotlinError::unsupported(declaration, "suspend lambda has an unknown state or suspension point");
        let code = self.code(member, declaration)?;
        let instructions = bytecode::decode(code.bytes)?;
        let [marker, pop, this, load, dispatch, result, check, tail @ ..] = instructions.as_slice()
        else { return Err(invalid()); };
        let Operand::Switch { default, cases } = &dispatch.operand else { return Err(invalid()); };
        if !matches!(cases.as_slice(), [(0, start)] if *start == result.offset && *default > check.offset)
            || self.reference(marker, 0xb8)? != Some(COROUTINE_MARKER)
            || pop.opcode != 0x57 || !aload(this, 0) || self.reference(load, 0xb4)? != Some((self.owner, state, "I"))
            || !aload(result, 1)
            || self.reference(check, 0xb8)? != Some(THROW_ON_FAILURE)
        {
            return Err(invalid());
        }
        let first = instructions.len() - tail.len();
        let default = instructions.binary_search_by_key(default, |instruction| instruction.offset).map_err(|_| invalid())?;
        let [body @ .., unit, ret] = &instructions[first..default] else { return Err(invalid()); };
        if !self.unit(unit)? || ret.opcode != 0xb0 || !self.bad_resume(&instructions[default..])?
            || body.iter().any(|instruction| {
                matches!(instruction.operand, Operand::Branch(_) | Operand::Switch { .. })
                    || instruction.local_access().is_some_and(|(slots, _)| slots.start < 2)
            })
        {
            return Err(invalid());
        }
        let mut locals = Locals {
            slots: Vec::new(),
            instance: false,
            alias: None,
            dispatch_alias: None,
            templates: templates::Context::default(),
            extension: None,
        };
        locals.templates.member = Some(member);
        locals.templates.properties = properties;
        statements::lower_debug_range(self, &instructions, first..default - 2, &code, &locals, declaration)
    }

    pub(super) fn bad_resume(&self, instructions: &[Instruction]) -> Result<bool, KotlinError> {
        const ILLEGAL_STATE: &str = "java/lang/IllegalStateException";
        let [new, dup, message, call, throw] = instructions else { return Ok(false); };
        let Operand::Constant(message_index) = message.operand else { return Ok(false); };
        let pool = &self.class.pool;
        let Constant::String(text) = *pool.get(message_index)? else { return Ok(false); };
        Ok(class_operand(self, new, 0xbb)? == Some(ILLEGAL_STATE)
            && dup.opcode == 0x59 && matches!(message.opcode, 0x12 | 0x13)
            && pool.utf8(text)? == "call to 'resume' before 'invoke' with coroutine"
            && self.reference(call, 0xb7)? == Some((ILLEGAL_STATE, "<init>", "(Ljava/lang/String;)V"))
            && throw.opcode == 0xbf)
    }

    pub(super) fn unit(&self, instruction: &Instruction) -> Result<bool, KotlinError> {
        Ok(self.reference(instruction, 0xb2)? == Some(("kotlin/Unit", "INSTANCE", "Lkotlin/Unit;")))
    }

    pub(super) fn suspend_method(
        &self,
        name: &str,
        descriptor: &str,
        access_flags: u16,
        declaration: &str,
    ) -> Result<&'a Member<'data>, KotlinError> {
        let pool = &self.class.pool;
        for method in &self.class.methods {
            if method.access_flags == access_flags && pool.utf8(method.name_index)? == name
                && pool.utf8(method.descriptor_index)? == descriptor
            {
                return Ok(method);
            }
        }
        Err(KotlinError::unsupported(declaration, "unproven coroutine entry point"))
    }
}

fn suspend_property(property: &Property) -> Option<(&str, &Type)> {
    let field = property.signature.field.as_ref()?;
    if property.mutable() || !matches!(&field.descriptor, JvmType::Object(name) if name == FUNCTION1) {
        return None;
    }
    Some((&field.name, unit_return(&property.ty)?))
}

pub(super) fn class_operand<'a>(bytecode: &Bytecode<'a, '_>, instruction: &Instruction, opcode: u8) -> Result<Option<&'a str>, KotlinError> {
    if instruction.opcode == opcode && let Operand::Constant(index) = instruction.operand {
        Ok(Some(bytecode.class.pool.class_name(index)?))
    } else {
        Ok(None)
    }
}

pub(super) fn aload(instruction: &Instruction, slot: u16) -> bool {
    local_load(instruction) == Some((0x19, slot))
}
