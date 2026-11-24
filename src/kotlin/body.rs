// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! The bytecode subset accepted by the Kotlin declaration writer. Every
//! instruction is consumed by a proven compiler pattern or typed expression.

use std::{borrow::Cow, fmt::Write};

use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::{ClassFile, Code, Constant, Member, find_attribute},
    descriptor::{MethodDescriptor, Primitive, Type as JvmType},
};

use super::{JvmFieldSignature, JvmMethodSignature, KotlinError, Type, ValueParameter, syntax::identifier};

mod control;
mod logic;
mod statements;

use logic::{Comparison, Conditional, Relation};

pub(super) const STATIC: u16 = 0x0008;
pub(super) const FINAL: u16 = 0x0010;
pub(super) const NATIVE: u16 = 0x0100;
pub(super) const ABSTRACT: u16 = 0x0400;

pub(super) struct Bytecode<'a, 'data> {
    pub class: &'a ClassFile<'data>,
    pub owner: &'a str,
}

pub(super) enum Body<'a> {
    Empty,
    Expression(Expr<'a>),
    Statements(statements::StatementBlock<'a>),
}

pub(super) struct Assignment<'a> {
    pub field: &'a str,
    pub descriptor: &'a str,
    pub value: Expr<'a>,
}

#[derive(Debug)]
pub(super) struct Expr<'a> {
    kind: ExprKind<'a>,
    depth: u8,
}

#[derive(Debug)]
enum ExprKind<'a> {
    Literal(Literal<'a>),
    Parameter { index: usize, load: u8 },
    Binary(Operator, Primitive, Box<(Expr<'a>, Expr<'a>)>),
    Compare(Box<Comparison<'a>>),
    Not(Box<Expr<'a>>),
    Conditional(Box<Conditional<'a>>),
}

#[derive(Debug)]
enum Literal<'a> {
    Null,
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    String(Cow<'a, [u16]>),
}

#[derive(Clone, Copy, Debug)]
enum Operator {
    Add, Subtract, Multiply, Divide, Remainder,
    ShiftLeft, ShiftRight, UnsignedShiftRight, And, Or, Xor,
}

impl Operator {
    fn binding(self) -> u8 {
        match self {
            Self::Add | Self::Subtract => logic::ADDITIVE,
            Self::Multiply | Self::Divide | Self::Remainder => logic::MULTIPLICATIVE,
            _ => logic::INFIX,
        }
    }

    fn text(self) -> &'static str {
        match self {
            Self::Add => " + ", Self::Subtract => " - ", Self::Multiply => " * ",
            Self::Divide => " / ", Self::Remainder => " % ",
            Self::ShiftLeft => " shl ", Self::ShiftRight => " shr ", Self::UnsignedShiftRight => " ushr ",
            Self::And => " and ", Self::Or => " or ", Self::Xor => " xor ",
        }
    }

    fn boolean_compatible(self) -> bool { matches!(self, Self::And | Self::Or | Self::Xor) }

    fn rhs_type(self, lhs: Primitive) -> Primitive {
        match self {
            Self::ShiftLeft | Self::ShiftRight | Self::UnsignedShiftRight => Primitive::Int,
            _ => lhs,
        }
    }
}

struct Locals<'a> {
    slots: Vec<(u16, &'a JvmType)>,
    instance: bool,
}

impl<'a> Locals<'a> {
    fn new(descriptor: &'a MethodDescriptor, instance: bool, parameters: &[ValueParameter], declaration: &str) -> Result<Self, KotlinError> {
        if descriptor.parameters.len() != parameters.len() {
            return Err(KotlinError::unsupported(declaration, "JVM parameters do not match Kotlin parameters"));
        }
        let mut next = u16::from(instance);
        let slots = descriptor.parameters.iter().map(|ty| {
            let slot = next;
            next += ty.slots();
            (slot, ty)
        }).collect();
        Ok(Self { slots, instance })
    }

    fn parameter(&self, slot: u16, expected: u8) -> Option<usize> {
        self.slots.binary_search_by_key(&slot, |&(slot, _)| slot).ok()
            .filter(|&index| load_opcode(self.slots[index].1) == expected)
    }
}

enum StackValue<'a> {
    This,
    Value(Expr<'a>),
    PrintStream,
    /// The two Long operands remain immediately below this stack marker.
    LongOrder,
}

impl<'a, 'data> Bytecode<'a, 'data> {
    pub fn find_method(&self, signature: &JvmMethodSignature) -> Result<Option<&'a Member<'data>>, KotlinError> {
        for method in &self.class.methods {
            let pool = &self.class.pool;
            if pool.utf8(method.name_index)? == signature.name
                && MethodDescriptor::parse(pool.utf8(method.descriptor_index)?)? == signature.descriptor
            {
                return Ok(Some(method));
            }
        }
        Ok(None)
    }

    pub fn find_field(&self, signature: &JvmFieldSignature) -> Result<Option<&'a Member<'data>>, KotlinError> {
        for field in &self.class.fields {
            let pool = &self.class.pool;
            if pool.utf8(field.name_index)? == signature.name
                && JvmType::parse(pool.utf8(field.descriptor_index)?)? == signature.descriptor
            {
                return Ok(Some(field));
            }
        }
        Ok(None)
    }

    pub fn constant(&self, member: &Member<'data>, declaration: &str) -> Result<Option<Expr<'a>>, KotlinError> {
        let Some(value) = find_attribute(&member.attributes, &self.class.pool, "ConstantValue")? else { return Ok(None); };
        let index = u16::from_be_bytes(value.try_into().map_err(|_| KotlinError::unsupported(declaration, "invalid ConstantValue"))?);
        self.literal(index, declaration).map(|literal| Some(Expr::literal(literal)))
    }

    pub fn instructions(&self, member: &Member<'data>, declaration: &str) -> Result<Vec<Instruction>, KotlinError> {
        Ok(bytecode::decode(self.code(member, declaration)?.bytes)?)
    }

    pub fn code(&self, member: &Member<'data>, declaration: &str) -> Result<Code<'data>, KotlinError> {
        let code = member.code(&self.class.pool)?.ok_or_else(|| KotlinError::unsupported(declaration, "missing method implementation"))?;
        if !code.exceptions.is_empty() {
            return Err(KotlinError::unsupported(declaration, "exception handlers"));
        }
        Ok(code)
    }

    pub fn function(&self, member: &Member<'data>, descriptor: &MethodDescriptor, parameters: &[ValueParameter], declaration: &str, trace: bool) -> Result<Body<'a>, KotlinError> {
        let locals = Locals::new(descriptor, member.access_flags & STATIC == 0, parameters, declaration)?;
        let code = self.code(member, declaration)?;
        let decoded = bytecode::decode(code.bytes)?;
        let instructions = self.parameter_checks(&decoded, &locals, parameters)?;
        if instructions.iter().any(|instruction| matches!(instruction.operand, Operand::Branch(_) | Operand::Switch { .. })) {
            return control::lower(self, instructions, &locals, &descriptor.return_type, parameters, declaration);
        }
        let (ret, body) = instructions.split_last().ok_or_else(|| KotlinError::unsupported(declaration, "empty method"))?;
        if ret.opcode != return_opcode(&descriptor.return_type) {
            return Err(KotlinError::unsupported(declaration, "non-returning or mismatched method body"));
        }
        if ret.opcode == 0xb1 {
            let start = decoded.len() - instructions.len();
            let statements = statements::lower(self, &decoded, start, &locals, declaration)?;
            if statements.is_empty() { return Ok(Body::Empty); }
            let lines = if trace { code.line_numbers(&self.class.pool)? } else { Vec::new() };
            return Ok(Body::Statements(statements::StatementBlock { statements, instructions: decoded, lines }));
        }
        let mut stack = Vec::new();
        for instruction in body {
            self.expression(instruction, &locals, &mut stack, declaration)?;
        }
        if stack.len() != 1 {
            return Err(KotlinError::unsupported(declaration, "expected one live expression at method return"));
        }
        Ok(Body::Expression(pop_value(&mut stack, declaration)?))
    }

    pub fn initialization(&self, member: &Member<'data>, descriptor: &MethodDescriptor, parameters: &[ValueParameter], superclass: Option<&str>, declaration: &str) -> Result<Vec<Assignment<'a>>, KotlinError> {
        let locals = Locals::new(descriptor, superclass.is_some(), parameters, declaration)?;
        if descriptor.return_type != JvmType::Void || (member.access_flags & STATIC == 0) != locals.instance {
            return Err(KotlinError::unsupported(declaration, "mismatched JVM initializer"));
        }
        let instructions = self.instructions(member, declaration)?;
        let mut instructions = self.parameter_checks(&instructions, &locals, parameters)?;
        if let Some(superclass) = superclass {
            match instructions {
                [receiver, call, rest @ ..] if local_load(receiver) == Some((0x19, 0))
                    && self.reference(call, 0xb7)? == Some((superclass, "<init>", "()V")) => instructions = rest,
                _ => return Err(KotlinError::unsupported(declaration, "non-trivial superclass constructor call")),
            }
        }
        let (ret, statements) = instructions.split_last().ok_or_else(|| KotlinError::unsupported(declaration, "missing initializer return"))?;
        if ret.opcode != 0xb1 {
            return Err(KotlinError::unsupported(declaration, "non-returning initializer"));
        }
        let mut stack = Vec::new();
        let mut assignments = Vec::new();
        for instruction in statements {
            let opcode = if locals.instance { 0xb5 } else { 0xb3 };
            if let Some((owner, field, descriptor)) = self.reference(instruction, opcode)? {
                if owner != self.owner { return Err(KotlinError::unsupported(declaration, "initializer writes an external field")); }
                let value = pop_value(&mut stack, declaration)?;
                if (locals.instance && !matches!(stack.pop(), Some(StackValue::This))) || !stack.is_empty() {
                    return Err(KotlinError::unsupported(declaration, "initializer has live stack values at field write"));
                }
                assignments.push(Assignment { field, descriptor, value });
            } else {
                self.expression(instruction, &locals, &mut stack, declaration)?;
            }
        }
        if !stack.is_empty() { return Err(KotlinError::unsupported(declaration, "initializer has live stack values at return")); }
        Ok(assignments)
    }

    pub fn default_getter(&self, member: &Member<'data>, field: &JvmFieldSignature, raw_descriptor: &str, declaration: &str) -> Result<(), KotlinError> {
        let instance = member.access_flags & STATIC == 0;
        let instructions = self.instructions(member, declaration)?;
        let valid = if instance {
            matches!(instructions.as_slice(), [receiver, get, ret] if local_load(receiver) == Some((0x19, 0))
                && self.reference(get, 0xb4)? == Some((self.owner, field.name.as_str(), raw_descriptor))
                && ret.opcode == return_opcode(&field.descriptor))
        } else {
            matches!(instructions.as_slice(), [get, ret] if self.reference(get, 0xb2)? == Some((self.owner, field.name.as_str(), raw_descriptor))
                && ret.opcode == return_opcode(&field.descriptor))
        };
        if !valid { return Err(KotlinError::unsupported(declaration, "getter is not a direct field read")); }
        Ok(())
    }

    pub fn default_setter(&self, member: &Member<'data>, field: &JvmFieldSignature, raw_descriptor: &str, ty: &Type, declaration: &str) -> Result<(), KotlinError> {
        let instance = member.access_flags & STATIC == 0;
        let slot = u16::from(instance);
        let instructions = self.instructions(member, declaration)?;
        let mut instructions = instructions.as_slice();
        if !ty.nullable && load_opcode(&field.descriptor) == 0x19
            && let Some((checked_slot, "<set-?>", rest)) = self.null_check(instructions)?
            && checked_slot == slot
        {
            instructions = rest;
        }
        let load = Some((load_opcode(&field.descriptor), slot));
        let valid = if instance {
            matches!(instructions, [receiver, value, put, ret] if local_load(receiver) == Some((0x19, 0))
                && local_load(value) == load && ret.opcode == 0xb1
                && self.reference(put, 0xb5)? == Some((self.owner, field.name.as_str(), raw_descriptor)))
        } else {
            matches!(instructions, [value, put, ret] if local_load(value) == load && ret.opcode == 0xb1
                && self.reference(put, 0xb3)? == Some((self.owner, field.name.as_str(), raw_descriptor)))
        };
        if !valid { return Err(KotlinError::unsupported(declaration, "setter is not a direct field write")); }
        Ok(())
    }

    fn parameter_checks<'b>(&self, mut instructions: &'b [Instruction], locals: &Locals<'_>, parameters: &[ValueParameter]) -> Result<&'b [Instruction], KotlinError> {
        let mut next = 0;
        while let Some((slot, name, rest)) = self.null_check(instructions)? {
            let Some(index) = locals.parameter(slot, 0x19) else { break; };
            let parameter = &parameters[index];
            if index < next || parameter.ty.nullable || name != parameter.name { break; }
            next = index + 1;
            instructions = rest;
        }
        Ok(instructions)
    }

    fn null_check<'b>(&self, instructions: &'b [Instruction]) -> Result<Option<(u16, &'a str, &'b [Instruction])>, KotlinError> {
        let [value, label, call, rest @ ..] = instructions else { return Ok(None); };
        let Some((0x19, slot)) = local_load(value) else { return Ok(None); };
        if !matches!(label.opcode, 0x12 | 0x13)
            || !matches!(self.reference(call, 0xb8)?, Some(("kotlin/jvm/internal/Intrinsics", "checkNotNullParameter" | "checkParameterIsNotNull", "(Ljava/lang/Object;Ljava/lang/String;)V")))
        {
            return Ok(None);
        }
        let Operand::Constant(index) = label.operand else { return Ok(None); };
        let Constant::String(index) = *self.class.pool.get(index)? else { return Ok(None); };
        Ok(Some((slot, self.class.pool.utf8(index)?, rest)))
    }

    pub fn reference(&self, instruction: &Instruction, opcode: u8) -> Result<Option<(&'a str, &'a str, &'a str)>, KotlinError> {
        if instruction.opcode != opcode { return Ok(None); }
        let Operand::Constant(index) = instruction.operand else { return Ok(None); };
        let constant = self.class.pool.get(index)?;
        if !matches!((opcode, constant), (0xb2..=0xb5, Constant::Fieldref { .. })
            | (0xb6..=0xb8, Constant::Methodref { .. } | Constant::InterfaceMethodref { .. }))
        {
            return Ok(None);
        }
        Ok(Some(self.class.pool.member_ref(index)?))
    }

    fn expression(&self, instruction: &Instruction, locals: &Locals<'_>, stack: &mut Vec<StackValue<'a>>, declaration: &str) -> Result<(), KotlinError> {
        if instruction.opcode == 0x00 { return Ok(()); }
        if let Some((opcode, slot)) = local_load(instruction) {
            if locals.instance && opcode == 0x19 && slot == 0 {
                stack.push(StackValue::This);
            } else {
                let param = locals.parameter(slot, opcode).ok_or_else(|| KotlinError::unsupported(declaration, "load of non-parameter local"))?;
                stack.push(StackValue::Value(Expr { kind: ExprKind::Parameter { index: param, load: opcode }, depth: 1 }));
            }
            return Ok(());
        }
        let op = instruction.opcode;
        let expr = match (op, &instruction.operand) {
            (0x01, _) => Expr::literal(Literal::Null),
            (0x02..=0x08, _) => Expr::literal(Literal::Int(i32::from(op) - 3)),
            (0x09..=0x0a, _) => Expr::literal(Literal::Long(i64::from(op) - 9)),
            (0x0b..=0x0d, _) => Expr::literal(Literal::Float(f32::from(op - 0x0b))),
            (0x0e..=0x0f, _) => Expr::literal(Literal::Double(f64::from(op - 0x0e))),
            (0x10..=0x11, Operand::Immediate(n)) => Expr::literal(Literal::Int(*n)),
            (0x12..=0x14, Operand::Constant(index)) => {
                let literal = self.literal(*index, declaration)?;
                if matches!(literal, Literal::Long(_) | Literal::Double(_)) != (op == 0x14) {
                    return Err(KotlinError::unsupported(declaration, "invalid constant load category"));
                }
                Expr::literal(literal)
            }
            (0x60..=0x73, _) => {
                let group = (op - 0x60) / 4;
                let primitive = [Primitive::Int, Primitive::Long, Primitive::Float, Primitive::Double][usize::from(op % 4)];
                let operator = [Operator::Add, Operator::Subtract, Operator::Multiply, Operator::Divide, Operator::Remainder][usize::from(group)];
                Expr::binary(operator, primitive, stack, declaration)?
            }
            (0x78..=0x83, _) => {
                let primitive = if op % 2 == 0 { Primitive::Int } else { Primitive::Long };
                let operator = [Operator::ShiftLeft, Operator::ShiftRight, Operator::UnsignedShiftRight,
                    Operator::And, Operator::Or, Operator::Xor][usize::from((op - 0x78) / 2)];
                Expr::binary(operator, primitive, stack, declaration)?
            }
            (0x94, _) => {
                if !matches!(stack.as_slice(), [.., StackValue::Value(_), StackValue::Value(_)]) {
                    return Err(KotlinError::unsupported(declaration, "missing Long comparison operands"));
                }
                stack.push(StackValue::LongOrder);
                return Ok(());
            }
            (0xb8, _) if self.reference(instruction, 0xb8)? == Some((
                "kotlin/jvm/internal/Intrinsics", "areEqual", "(Ljava/lang/Object;Ljava/lang/Object;)Z",
            )) => {
                let rhs = pop_value(stack, declaration)?;
                let lhs = pop_value(stack, declaration)?;
                Comparison::reference(Relation::Eq, lhs, rhs, declaration)?
            }
            _ => return Err(KotlinError::unsupported(declaration, "bytecode outside the supported expression subset")),
        };
        stack.push(StackValue::Value(expr));
        Ok(())
    }

    fn literal(&self, index: u16, declaration: &str) -> Result<Literal<'a>, KotlinError> {
        Ok(match *self.class.pool.get(index)? {
            Constant::Integer(value) => Literal::Int(value),
            Constant::Long(value) => Literal::Long(value),
            Constant::Float(value) => Literal::Float(value),
            Constant::Double(value) => Literal::Double(value),
            Constant::String(index) => Literal::String(self.class.pool.utf16(index)?),
            _ => return Err(KotlinError::unsupported(declaration, "constant cannot be rendered as a Kotlin literal")),
        })
    }
}

fn pop_value<'a>(stack: &mut Vec<StackValue<'a>>, declaration: &str) -> Result<Expr<'a>, KotlinError> {
    match stack.pop() {
        Some(StackValue::Value(expr)) => Ok(expr),
        _ => Err(KotlinError::unsupported(declaration, "missing expression stack value")),
    }
}

pub(super) fn local_load(instruction: &Instruction) -> Option<(u8, u16)> {
    match (instruction.opcode, &instruction.operand) {
        (op @ 0x15..=0x19, Operand::Local(slot)) => Some((op, *slot)),
        (op @ 0x1a..=0x2d, Operand::None) => Some((0x15 + (op - 0x1a) / 4, u16::from((op - 0x1a) % 4))),
        _ => None,
    }
}

pub(super) fn load_opcode(ty: &JvmType) -> u8 {
    match ty {
        JvmType::Primitive(Primitive::Long) => 0x16,
        JvmType::Primitive(Primitive::Float) => 0x17,
        JvmType::Primitive(Primitive::Double) => 0x18,
        JvmType::Primitive(_) => 0x15,
        _ => 0x19,
    }
}

pub(super) fn return_opcode(ty: &JvmType) -> u8 {
    if *ty == JvmType::Void { 0xb1 } else { load_opcode(ty) + 0x97 }
}

impl<'a> Expr<'a> {
    fn literal(literal: Literal<'a>) -> Self { Self { kind: ExprKind::Literal(literal), depth: 1 } }

    fn new(kind: ExprKind<'a>, depth: u8, declaration: &str) -> Result<Self, KotlinError> {
        if depth > 64 { return Err(KotlinError::unsupported(declaration, "Kotlin expression nesting limit")); }
        Ok(Self { kind, depth })
    }

    fn binary(operator: Operator, primitive: Primitive, stack: &mut Vec<StackValue<'a>>, declaration: &str) -> Result<Self, KotlinError> {
        let rhs = pop_value(stack, declaration)?;
        let lhs = pop_value(stack, declaration)?;
        let depth = lhs.depth.max(rhs.depth) + 1;
        Self::new(ExprKind::Binary(operator, primitive, Box::new((lhs, rhs))), depth, declaration)
    }

    fn primitive_hint(&self, parameters: &[ValueParameter]) -> Option<Primitive> {
        match &self.kind {
            ExprKind::Parameter { index, .. } => logic::primitive_type(&parameters[*index].ty),
            ExprKind::Literal(Literal::Long(_)) => Some(Primitive::Long),
            ExprKind::Literal(Literal::Float(_)) => Some(Primitive::Float),
            ExprKind::Literal(Literal::Double(_)) => Some(Primitive::Double),
            ExprKind::Literal(_) => None,
            ExprKind::Compare(_) | ExprKind::Not(_) => Some(Primitive::Boolean),
            ExprKind::Conditional(conditional) => conditional.primitive_hint(parameters),
            ExprKind::Binary(operator, primitive, pair) => {
                if *primitive == Primitive::Int && operator.boolean_compatible()
                    && (pair.0.primitive_hint(parameters) == Some(Primitive::Boolean)
                        || pair.1.primitive_hint(parameters) == Some(Primitive::Boolean))
                {
                    Some(Primitive::Boolean)
                } else {
                    Some(*primitive)
                }
            }
        }
    }

    pub fn parameter(&self, descriptor: &JvmType) -> Option<usize> {
        match self.kind {
            ExprKind::Parameter { index, load } if load == load_opcode(descriptor) => Some(index),
            _ => None,
        }
    }

    pub fn write(&self, out: &mut String, expected: &Type, jvm_type: &JvmType, parameters: &[ValueParameter], declaration: &str) -> Result<(), KotlinError> {
        self.write_at(out, Expected::Type(expected, jvm_type), parameters, declaration, 0)
    }

    fn write_at(&self, out: &mut String, expected: Expected<'_>, parameters: &[ValueParameter], declaration: &str, binding: u8) -> Result<(), KotlinError> {
        let mismatch = || KotlinError::unsupported(declaration, "expression type does not match the Kotlin declaration");
        match &self.kind {
            ExprKind::Literal(literal) => literal.write(out, expected).ok_or_else(mismatch)?,
            ExprKind::Parameter { index, load } => {
                let parameter = &parameters[*index];
                if *load != expected.load() || !expected.accepts(&parameter.ty) { return Err(mismatch()); }
                identifier(out, &parameter.name, declaration)?;
            }
            ExprKind::Binary(operator, primitive, arguments) => {
                let result = expected.primitive().ok_or_else(mismatch)?;
                if result != *primitive && !(result == Primitive::Boolean && *primitive == Primitive::Int && operator.boolean_compatible()) {
                    return Err(mismatch());
                }
                let current = operator.binding();
                if binding > current { out.push('('); }
                arguments.0.write_at(out, Expected::Primitive(result), parameters, declaration, current)?;
                out.push_str(operator.text());
                arguments.1.write_at(out, Expected::Primitive(operator.rhs_type(result)), parameters, declaration, current + 1)?;
                if binding > current { out.push(')'); }
            }
            ExprKind::Compare(comparison) => comparison.write(out, expected, parameters, declaration, binding)?,
            ExprKind::Not(operand) => {
                logic::require_boolean(expected, declaration)?;
                logic::write_negation(out, operand, parameters, declaration, binding)?;
            }
            ExprKind::Conditional(conditional) => conditional.write(out, expected, parameters, declaration, binding)?,
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum Expected<'a> {
    Type(&'a Type, &'a JvmType),
    Primitive(Primitive),
    Reference,
}

impl Expected<'_> {
    fn primitive(self) -> Option<Primitive> {
        match self {
            Self::Primitive(primitive) => Some(primitive),
            Self::Type(ty, JvmType::Primitive(primitive)) if logic::primitive_type(ty) == Some(*primitive) => Some(*primitive),
            _ => None,
        }
    }

    fn load(self) -> u8 {
        match self {
            Self::Type(_, jvm_type) => load_opcode(jvm_type),
            Self::Primitive(primitive) => load_opcode(&JvmType::Primitive(primitive)),
            Self::Reference => 0x19,
        }
    }

    fn accepts(self, source: &Type) -> bool {
        match self {
            Self::Primitive(primitive) => logic::primitive_type(source) == Some(primitive),
            Self::Reference => logic::primitive_type(source).is_none(),
            Self::Type(ty, _) => source == ty || (!source.nullable && ty.nullable && source.classifier == ty.classifier
                && source.arguments == ty.arguments && source.outer == ty.outer && source.flexible == ty.flexible),
        }
    }
}


impl Literal<'_> {
    fn write(&self, out: &mut String, expected: Expected<'_>) -> Option<()> {
        match self {
            Self::Null => {
                if !matches!(expected, Expected::Reference)
                    && !matches!(expected, Expected::Type(ty, JvmType::Object(_) | JvmType::Array(_)) if ty.nullable)
                { return None; }
                out.push_str("null");
            }
            Self::String(value) => {
                if !matches!(expected, Expected::Reference)
                    && !matches!(expected, Expected::Type(ty, JvmType::Object(jvm)) if ty.class_id() == Some("kotlin/String") && jvm == "java/lang/String")
                { return None; }
                write_string(out, value.iter().copied());
            }
            Self::Int(value) => match expected.primitive()? {
                Primitive::Int => write!(out, "{value}").unwrap(),
                Primitive::Byte if i8::try_from(*value).is_ok() => write!(out, "{value}").unwrap(),
                Primitive::Short if i16::try_from(*value).is_ok() => write!(out, "{value}").unwrap(),
                Primitive::Boolean if *value == 0 || *value == 1 => out.push_str(if *value == 0 { "false" } else { "true" }),
                Primitive::Char => {
                    let unit = u16::try_from(*value).ok()?;
                    out.push('\'');
                    match char::from_u32(u32::from(unit)) {
                        Some(c) => escaped_char(out, c, '\''),
                        None => write!(out, "\\u{unit:04X}").unwrap(),
                    }
                    out.push('\'');
                }
                _ => return None,
            },
            Self::Long(value) if expected.primitive()? == Primitive::Long => {
                if *value == i64::MIN { out.push_str("kotlin.Long.MIN_VALUE"); } else { write!(out, "{value}L").unwrap(); }
            }
            Self::Float(value) if expected.primitive()? == Primitive::Float => {
                if value.is_finite() { write!(out, "{value:?}f").unwrap(); }
                else { out.push_str("kotlin.Float."); out.push_str(nonfinite(f64::from(*value))); }
            }
            Self::Double(value) if expected.primitive()? == Primitive::Double => {
                if value.is_finite() { write!(out, "{value:?}").unwrap(); }
                else { out.push_str("kotlin.Double."); out.push_str(nonfinite(*value)); }
            }
            _ => return None,
        }
        Some(())
    }
}

fn nonfinite(value: f64) -> &'static str {
    if value.is_nan() { "NaN" } else if value.is_sign_positive() { "POSITIVE_INFINITY" } else { "NEGATIVE_INFINITY" }
}

pub(super) fn write_string(out: &mut String, value: impl Iterator<Item = u16>) {
    out.push('"');
    for c in char::decode_utf16(value) {
        match c {
            Ok(c) => escaped_char(out, c, '"'),
            Err(unit) => write!(out, "\\u{:04X}", unit.unpaired_surrogate()).unwrap(),
        }
    }
    out.push('"');
}

fn escaped_char(out: &mut String, c: char, quote: char) {
    match c {
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\r' => out.push_str("\\r"),
        '\t' => out.push_str("\\t"),
        '\x08' => out.push_str("\\b"),
        '$' if quote == '"' => out.push_str("\\$"),
        c if c == quote => { out.push('\\'); out.push(c); }
        c if c.is_control() || matches!(c, '\u{2028}' | '\u{2029}') => write!(out, "\\u{:04X}", u32::from(c)).unwrap(),
        c => out.push(c),
    }
}
