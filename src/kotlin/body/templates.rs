// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{borrow::Cow, cell::OnceCell, ops::Range};

use crate::classfile::{BootstrapMethod, Member, find_attribute};

use super::{
    Bytecode, Constant, Expected, Expr, ExprKind, FINAL, Instruction, JvmType, KotlinError,
    Literal, Locals, MethodDescriptor, Operand, Primitive, Property, STATIC, ScopedLocal,
    StackValue, ValueParameter, logic, loops, pop_value, unsupported_expression,
    write_string_contents,
};
use crate::kotlin::{Modality, syntax::plain_identifier};

const BUILDER: &str = "java/lang/StringBuilder";
const STRING: &str = "java/lang/String";
const OBJECT: &str = "java/lang/Object";
const CLASS: &str = "java/lang/Class";
const KCLASS: &str = "kotlin/reflect/KClass";
const FACTORY: &str = "java/lang/invoke/StringConcatFactory";
const CONCAT: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
const WITH_CONSTANTS: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";

#[derive(Default)]
pub(super) struct Context<'a> {
    pub(super) member: Option<&'a Member<'a>>,
    pub(super) properties: &'a [Property],
    bootstraps: OnceCell<Vec<BootstrapMethod>>,
}

#[derive(Debug)]
pub(super) struct Template<'a> {
    // Literal runs in an indy recipe share this allocation.
    recipe: Cow<'a, [u16]>,
    parts: Vec<Part<'a>>,
    infallible: bool,
    depth: u8,
}

#[derive(Debug)]
enum Part<'a> {
    Recipe(Range<usize>),
    Text(Cow<'a, [u16]>),
    Char(u16),
    Value(Argument<'a>),
}

#[derive(Debug)]
struct Argument<'a> {
    expr: Expr<'a>,
    primitive: Option<Primitive>,
}

pub(super) enum Builder<'a> {
    New,
    Duplicated,
    Ready(Template<'a>),
}

impl<'a> Template<'a> {
    fn new() -> Self {
        Self { recipe: Cow::Borrowed(&[]), parts: Vec::new(), infallible: true, depth: 1 }
    }

    fn push_value(&mut self, argument: Argument<'a>, infallible: bool) {
        self.depth = self.depth.max(argument.expr.depth + 1);
        self.infallible &= infallible;
        self.parts.push(Part::Value(argument));
    }

    fn push_text(&mut self, value: Cow<'a, [u16]>) {
        if !value.is_empty() {
            self.parts.push(Part::Text(value));
        }
    }

    fn finish(self, declaration: &str) -> Result<Expr<'a>, KotlinError> {
        if !self.parts.iter().any(|part| matches!(part, Part::Value(arg)
            if !matches!(arg.expr.kind, ExprKind::Literal(_))))
        {
            return Err(KotlinError::unsupported(declaration, "constant-only string concatenation"));
        }
        let depth = self.depth;
        Expr::new(ExprKind::Template(self), depth, declaration)
    }

    pub(super) fn infallible(&self) -> bool {
        self.infallible
    }

    pub(super) fn write(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
    ) -> Result<(), KotlinError> {
        out.push('"');
        let mut parts = self.parts.iter().peekable();
        while let Some(part) = parts.next() {
            match part {
                Part::Recipe(range) => write_string_contents(out, self.recipe[range.clone()].iter().copied()),
                Part::Text(text) => write_string_contents(out, text.iter().copied()),
                Part::Char(unit) => write_string_contents(out, std::iter::once(*unit)),
                Part::Value(argument) => {
                    let next = parts.peek().and_then(|part| match part {
                        Part::Recipe(range) => self.recipe[range.clone()].first().copied(),
                        Part::Text(text) => text.first().copied(),
                        Part::Char(unit) => Some(*unit),
                        Part::Value(_) => None,
                    });
                    // A following Unicode letter or digit can extend `$name`.
                    // Braces are also mandatory for a quoted Kotlin name.
                    let short = matches!(argument.expr.kind, ExprKind::Parameter { index, .. }
                        if plain_identifier(&parameters[index].name))
                        && next.is_none_or(|unit| u8::try_from(unit).is_ok_and(|byte|
                            byte.is_ascii() && !byte.is_ascii_alphanumeric() && byte != b'_'));
                    out.push_str(if short { "$" } else { "${" });
                    argument.expr.write_at(
                        out,
                        argument.primitive.map_or(Expected::Reference, Expected::Primitive),
                        parameters,
                        declaration,
                        0,
                    )?;
                    if !short {
                        out.push('}');
                    }
                }
            }
        }
        out.push('"');
        Ok(())
    }
}

pub(super) fn lower<'a>(
    bytecode: &Bytecode<'a, '_>,
    instruction: &Instruction,
    locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<bool, KotlinError> {
    let invalid = || unsupported_expression(declaration);
    let pool = &bytecode.class.pool;
    if let Some(StackValue::StringBuilder(state)) = stack.last_mut() {
        match state {
            Builder::New if instruction.opcode == 0x59 => {
                *state = Builder::Duplicated;
                return Ok(true);
            }
            Builder::Duplicated if builder_call(bytecode, instruction, 0xb7)? == Some(("<init>", "()V")) => {
                *state = Builder::Ready(Template::new());
                return Ok(true);
            }
            Builder::New | Builder::Duplicated => return Err(invalid()),
            Builder::Ready(_) => {}
        }
    }
    let expression = match (instruction.opcode, &instruction.operand) {
        (0xba, Operand::Constant(index)) => indy(bytecode, *index, locals, stack, declaration)?,
        (0xbb, Operand::Constant(index)) if pool.class_name(*index)? == BUILDER => {
            stack.push(StackValue::StringBuilder(Builder::New));
            return Ok(true);
        }
        (0xb6, _) if matches!(stack.as_slice(),
            [.., StackValue::StringBuilder(Builder::Ready(_))]
                | [.., StackValue::StringBuilder(Builder::Ready(_)), StackValue::Value(_)]) => {
            match builder_call(bytecode, instruction, 0xb6)? {
                Some(("append", descriptor)) => {
                    let requested = append_parameter(descriptor).ok_or_else(invalid)?;
                    let expr = pop_value(stack, declaration)?;
                    let Some(StackValue::StringBuilder(Builder::Ready(template))) = stack.last_mut() else {
                        return Err(invalid());
                    };
                    let (argument, safe) = argument(expr, requested, locals, declaration)?;
                    match argument.expr.kind {
                        ExprKind::Literal(Literal::String(text)) => template.push_text(text),
                        ExprKind::Literal(Literal::Int(value)) if requested == Shape::Primitive(Primitive::Char) => {
                            let unit = u16::try_from(value).map_err(|_| invalid())?;
                            template.parts.push(Part::Char(unit));
                        }
                        _ => {
                            let infallible = safe && argument.expr.infallible();
                            template.push_value(argument, infallible);
                        }
                    }
                    return Ok(true);
                }
                Some(("toString", "()Ljava/lang/String;")) => {
                    let Some(StackValue::StringBuilder(Builder::Ready(template))) = stack.pop() else {
                        return Err(invalid());
                    };
                    template.finish(declaration)?
                }
                Some(_) => return Err(invalid()),
                None => return Ok(false),
            }
        }
        (0xb4, _) => this_property(bytecode, instruction, locals, stack, declaration)?,
        _ => return Ok(false),
    };
    stack.push(StackValue::Value(expression));
    Ok(true)
}

pub(super) fn class_literal<'a>(
    bytecode: &Bytecode<'a, '_>,
    owner: &'a str,
    locals: &Locals<'_>,
    declaration: &str,
    scoped: &[ScopedLocal<'a>],
) -> Result<Expr<'a>, KotlinError> {
    let invalid = || unsupported_expression(declaration);
    let (_, name) = owner.rsplit_once('/').unwrap_or(("", owner));
    let Some(method) = locals.templates.member else { return Err(invalid()); };
    let pool = &bytecode.class.pool;
    // Only use an unqualified class literal when a local/property or generic
    // parameter cannot shadow it.
    if owner != bytecode.owner || name.contains('$') || !scoped.is_empty() || locals.has_extension_receiver()
        || locals.templates.properties.iter().any(|property| property.name == name)
        || find_attribute(&bytecode.class.attributes, pool, "Signature")?.is_some()
        || find_attribute(&method.attributes, pool, "Signature")?.is_some()
    {
        return Err(invalid());
    }
    Expr::new(ExprKind::ClassLiteral(name), 1, declaration)
}

fn this_property<'a>(
    bytecode: &Bytecode<'a, '_>,
    instruction: &Instruction,
    locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Expr<'a>, KotlinError> {
    let invalid = || unsupported_expression(declaration);
    let Some((owner, name, descriptor)) = bytecode.reference(instruction, 0xb4)? else {
        return Err(invalid());
    };
    if owner != bytecode.owner || !matches!(stack.last(), Some(StackValue::This)) || locals.has_extension_receiver() {
        return Err(invalid());
    }
    let ty = JvmType::parse(descriptor)?;
    let JvmType::Primitive(primitive) = ty else { return Err(invalid()); };
    let Some(signature) = locals.templates.properties.iter().find_map(|property| {
        let signature = property.signature.field.as_ref()?;
        (property.name == name && signature.name == name && signature.descriptor == ty
            && !property.mutable() && !property.delegated() && property.flags.modality() == Modality::Final
            && !property.getter_flags.is_some_and(|flags| flags.has(6))
            && logic::primitive_type(&property.ty) == Some(primitive)).then_some(signature)
    }) else { return Err(invalid()); };
    if !bytecode.find_field(signature)?.is_some_and(|field| field.access_flags & (0x0002 | FINAL | STATIC | 0x0040) == (0x0002 | FINAL)) {
        return Err(invalid());
    }
    let _ = stack.pop();
    Expr::new(ExprKind::ThisProperty { name, primitive }, 2, declaration)
}

fn builder_call<'a>(
    bytecode: &Bytecode<'a, '_>,
    instruction: &Instruction,
    opcode: u8,
) -> Result<Option<(&'a str, &'a str)>, KotlinError> {
    if instruction.opcode != opcode {
        return Ok(None);
    }
    let Operand::Constant(index) = instruction.operand else { return Ok(None); };
    let pool = &bytecode.class.pool;
    if !matches!(pool.get(index)?, Constant::Methodref { .. }) {
        return Ok(None);
    }
    let (owner, name, descriptor) = pool.member_ref(index)?;
    Ok((owner == BUILDER).then_some((name, descriptor)))
}

fn append_parameter(descriptor: &str) -> Option<Shape<'static>> {
    let parameter = descriptor.strip_prefix('(')?.strip_suffix(")Ljava/lang/StringBuilder;")?;
    Some(match parameter {
        "Z" => Shape::Primitive(Primitive::Boolean),
        "C" => Shape::Primitive(Primitive::Char),
        "I" => Shape::Primitive(Primitive::Int),
        "J" => Shape::Primitive(Primitive::Long),
        "F" => Shape::Primitive(Primitive::Float),
        "D" => Shape::Primitive(Primitive::Double),
        "Ljava/lang/String;" => Shape::Object(STRING),
        "Ljava/lang/Object;" => Shape::Object(OBJECT),
        // CharSequence and char[] overloads do not use Object's string conversion.
        _ => return None,
    })
}

fn indy<'a>(
    bytecode: &Bytecode<'a, '_>,
    index: u16,
    locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Expr<'a>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "invalid Kotlin string concatenation site");
    let pool = &bytecode.class.pool;
    let Constant::InvokeDynamic { bootstrap_index, name_and_type_index } = *pool.get(index)? else {
        return Err(invalid());
    };
    if locals.templates.bootstraps.get().is_none() {
        let _ = locals.templates.bootstraps.set(bytecode.class.bootstrap_methods()?);
    }
    let bootstrap = locals.templates.bootstraps.get().expect("loaded bootstrap methods")
        .get(usize::from(bootstrap_index)).ok_or_else(invalid)?;
    let Constant::MethodHandle { reference_kind: 6, reference_index } = *pool.get(bootstrap.method_ref)? else {
        return Err(invalid());
    };
    if !matches!(pool.get(reference_index)?, Constant::Methodref { .. }) {
        return Err(invalid());
    }
    let (site, descriptor) = pool.name_and_type(name_and_type_index)?;
    let factory = pool.member_ref(reference_index)?;
    let descriptor = MethodDescriptor::parse(descriptor)?;
    if !matches!(&descriptor.return_type, JvmType::Object(name) if name == STRING)
        || descriptor.parameters.iter().map(JvmType::slots).sum::<u16>() > 200
    {
        return Err(invalid());
    }

    let first = stack.len().checked_sub(descriptor.parameters.len()).ok_or_else(invalid)?;
    let mut arguments = stack.drain(first..).zip(&descriptor.parameters);
    let mut template = Template::new();
    let mut can_call_user_code = false;
    let mut next = |template: &mut Template<'a>| -> Result<(), KotlinError> {
        let Some((StackValue::Value(expr), parameter)) = arguments.next() else {
            return Err(invalid());
        };
        let (argument, safe) = argument(expr, shape(parameter), locals, declaration)?;
        let infallible = argument.expr.infallible();
        // A template interleaves evaluation and conversion; indy evaluates every
        // operand before the first conversion that might invoke user toString.
        if can_call_user_code && !infallible {
            return Err(KotlinError::unsupported(declaration, "Kotlin string concatenation would reorder argument evaluation"));
        }
        can_call_user_code |= !safe;
        template.push_value(argument, safe && infallible);
        Ok(())
    };
    match (site, factory, bootstrap.arguments.as_slice()) {
        ("makeConcat", (FACTORY, "makeConcat", CONCAT), []) => {
            for _ in &descriptor.parameters {
                next(&mut template)?;
            }
        }
        ("makeConcatWithConstants", (FACTORY, "makeConcatWithConstants", WITH_CONSTANTS), [recipe, constants @ ..]) => {
            let Constant::String(text) = *pool.get(*recipe)? else { return Err(invalid()); };
            let recipe = pool.utf16(text)?;
            let mut constants = constants.iter();
            let mut start = 0;
            for (index, unit) in recipe.iter().copied().enumerate() {
                if !matches!(unit, 1 | 2) { continue; }
                if start < index {
                    template.parts.push(Part::Recipe(start..index));
                }
                if unit == 1 {
                    next(&mut template)?;
                } else {
                    let index = *constants.next().ok_or_else(invalid)?;
                    match pool.get(index)? {
                        Constant::String(text) => template.push_text(pool.utf16(*text)?),
                        constant @ (Constant::Integer(_) | Constant::Long(_) | Constant::Float(_) | Constant::Double(_)) => {
                            let expr = Expr::literal(bytecode.literal(constant, declaration)?);
                            let primitive = match actual(&expr, locals) {
                                Shape::IntConstant(_) => Primitive::Int,
                                Shape::Primitive(primitive) => primitive,
                                _ => unreachable!("numeric constant"),
                            };
                            template.push_value(Argument { expr, primitive: Some(primitive) }, true);
                        }
                        _ => return Err(invalid()),
                    }
                }
                start = index + 1;
            }
            if constants.next().is_some() { return Err(invalid()); }
            if start < recipe.len() {
                template.parts.push(Part::Recipe(start..recipe.len()));
            }
            template.recipe = recipe;
        }
        _ => return Err(invalid()),
    }
    if arguments.next().is_some() {
        return Err(invalid());
    }
    template.finish(declaration)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape<'a> {
    Primitive(Primitive),
    IntConstant(i32),
    Object(&'a str),
    Array(&'a JvmType),
    Null,
    Unknown,
}

fn shape(ty: &JvmType) -> Shape<'_> {
    match ty {
        JvmType::Primitive(primitive) => Shape::Primitive(*primitive),
        JvmType::Object(name) => Shape::Object(name),
        JvmType::Array(_) => Shape::Array(ty),
        JvmType::Void => Shape::Unknown,
    }
}

fn actual<'a>(expr: &'a Expr<'_>, locals: &'a Locals<'_>) -> Shape<'a> {
    match &expr.kind {
        ExprKind::Parameter { index, .. } => shape(locals.slots[*index].1),
        ExprKind::ExtensionReceiver(super::extensions::Receiver::Primitive(primitive)) => Shape::Primitive(*primitive),
        ExprKind::ExtensionReceiver(super::extensions::Receiver::Reference(receiver)) => shape(&receiver.jvm),
        ExprKind::BoundGetter(read) => shape(&read.value().jvm),
        ExprKind::Local(local) => shape(&local.value.jvm),
        ExprKind::Invocation(call) => shape(&call.result().jvm),
        ExprKind::Literal(Literal::Int(value)) => Shape::IntConstant(*value),
        ExprKind::Literal(Literal::Long(_)) => Shape::Primitive(Primitive::Long),
        ExprKind::Literal(Literal::Float(_)) => Shape::Primitive(Primitive::Float),
        ExprKind::Literal(Literal::Double(_)) => Shape::Primitive(Primitive::Double),
        ExprKind::Literal(Literal::Null) => Shape::Null,
        ExprKind::Literal(Literal::String(_)) | ExprKind::Template(_) | ExprKind::CatchMessage(_) => Shape::Object(STRING),
        ExprKind::CatchLocal(local) => Shape::Object(local.ty),
        ExprKind::LoopLocal(local) => match local.element {
            loops::Element::Primitive(primitive) => Shape::Primitive(primitive),
            loops::Element::String => Shape::Object(STRING),
            loops::Element::Object => Shape::Object(OBJECT),
        },
        ExprKind::Binary(operator, Primitive::Int, pair) if operator.boolean_compatible()
            && [ &pair.0, &pair.1 ].into_iter().any(|operand|
                actual(operand, locals) == Shape::Primitive(Primitive::Boolean)) => Shape::Primitive(Primitive::Boolean),
        ExprKind::Binary(_, primitive, _) | ExprKind::ThisProperty { primitive, .. } => Shape::Primitive(*primitive),
        ExprKind::Compare(_) | ExprKind::Not(_) | ExprKind::TypeTest { .. } => Shape::Primitive(Primitive::Boolean),
        ExprKind::BoxedInt(_) => Shape::Object("java/lang/Integer"),
        ExprKind::ClassLiteral(_) => Shape::Object(CLASS),
        ExprKind::Conditional(_) | ExprKind::Nullable(_) => Shape::Unknown,
    }
}

fn argument<'a>(
    expr: Expr<'a>,
    requested: Shape<'_>,
    locals: &Locals<'_>,
    declaration: &str,
) -> Result<(Argument<'a>, bool), KotlinError> {
    use Shape::{Array, IntConstant, Null, Object, Primitive as Prim};
    let actual = actual(&expr, locals);
    let primitive = match (requested, actual) {
        (Prim(requested), Prim(actual)) if requested == actual => Some(actual),
        (Prim(Primitive::Int), Prim(actual @ (Primitive::Byte | Primitive::Short))) => Some(actual),
        (Prim(requested), IntConstant(value)) if match requested {
            Primitive::Int => true,
            Primitive::Byte => i8::try_from(value).is_ok(),
            Primitive::Short => i16::try_from(value).is_ok(),
            Primitive::Char => u16::try_from(value).is_ok(),
            Primitive::Boolean => matches!(value, 0 | 1),
            _ => false,
        } => Some(requested),
        (Object(OBJECT), Object(_) | Array(_) | Null) | (Object(_) | Array(_), Null) => None,
        (Object(requested), Object(actual)) if requested == actual => None,
        (Array(requested), Array(actual)) if requested == actual => None,
        // The Kotlin indy backend can retain KClass in the call-site type for
        // an ldc that has already been lowered to java.lang.Class. This is an
        // interface input to the concat factory's Object string conversion.
        (Object(KCLASS), Object(CLASS)) if matches!(expr.kind, ExprKind::ClassLiteral(_)) => None,
        _ => return Err(KotlinError::unsupported(declaration, "Kotlin template argument does not match its JVM descriptor")),
    };
    let safe = matches!(actual, Prim(_) | IntConstant(_) | Null | Object(STRING | CLASS | "java/lang/Integer"));
    Ok((Argument { expr, primitive }, safe))
}

/// Called only for successfully lowered statement ranges. The builder and
/// literals folded into it no longer have corresponding source expressions.
pub(super) fn elided_trace(
    bytecode: &Bytecode<'_, '_>,
    instruction: &Instruction,
    next: Option<&Instruction>,
) -> Result<bool, KotlinError> {
    let builder_allocation = instruction.opcode == 0xbb
        && matches!(instruction.operand, Operand::Constant(index)
            if bytecode.class.pool.class_name(index)? == BUILDER);
    if builder_allocation || instruction.opcode == 0x59
        || builder_call(bytecode, instruction, 0xb7)? == Some(("<init>", "()V"))
        || matches!(builder_call(bytecode, instruction, 0xb6)?, Some(("append", _)))
    {
        return Ok(true);
    }
    if !matches!(instruction.opcode, 0x02..=0x08 | 0x10..=0x13) {
        return Ok(false);
    }
    let Some(next) = next else { return Ok(false); };
    let Some(("append", descriptor)) = builder_call(bytecode, next, 0xb6)? else {
        return Ok(false);
    };
    let kind = append_parameter(descriptor);
    if matches!(instruction.opcode, 0x02..=0x08 | 0x10..=0x11) {
        return Ok(kind == Some(Shape::Primitive(Primitive::Char)));
    }
    let Operand::Constant(index) = instruction.operand else { return Ok(false); };
    Ok(match bytecode.class.pool.get(index)? {
        Constant::Integer(_) => kind == Some(Shape::Primitive(Primitive::Char)),
        Constant::String(_) => matches!(kind, Some(Shape::Object(STRING | OBJECT))),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        bytecode, classfile::ClassFile,
        kotlin::tests::{INDY_TEMPLATE, bytes},
    };

    use super::*;

    #[test]
    fn rejects_moving_user_string_conversion_ahead_of_a_fallible_operand() {
        let mut data = bytes(INDY_TEMPLATE);
        let old = b"(ILjava/lang/String;)Ljava/lang/String;";
        let start = data.windows(old.len()).position(|window| window == old).unwrap();
        data[start..start + old.len()].copy_from_slice(b"(Ljava/lang/Object;I)Ljava/lang/String;");
        let class = ClassFile::parse(&data).unwrap();
        let bytecode = Bytecode { class: &class, owner: class.pool.class_name(class.this_class).unwrap() };
        let method = class.methods.iter().find(|method|
            class.pool.utf8(method.name_index).unwrap() == "stringInterpolation").unwrap();
        let code = method.code(&class.pool).unwrap().unwrap();
        let site = bytecode::decode(code.bytes).unwrap().into_iter().find_map(|instruction|
            match (instruction.opcode, instruction.operand) {
                (0xba, Operand::Constant(index)) => Some(index),
                _ => None,
            }).unwrap();
        let descriptor = MethodDescriptor::parse("(Ljava/lang/Object;I)V").unwrap();
        let locals = Locals {
            slots: descriptor.parameters.iter().enumerate().map(|(index, ty)| (index as u16, ty)).collect(),
            instance: false,
            alias: None,
            dispatch_alias: None,
            templates: Context::default(),
            extension: None,
        };
        let parameter = |index, load| Expr { kind: ExprKind::Parameter { index, load }, depth: 1 };
        let mut stack = vec![
            StackValue::Value(parameter(0, 0x19)),
            StackValue::Value(parameter(1, 0x15)),
            StackValue::Value(Expr::literal(Literal::Int(2))),
        ];
        let division = Expr::binary(super::super::Operator::Divide, Primitive::Int, &mut stack, "test").unwrap();
        stack.push(StackValue::Value(division));
        assert!(matches!(
            indy(&bytecode, site, &locals, &mut stack, "test"),
            Err(KotlinError::Unsupported { feature: "Kotlin string concatenation would reorder argument evaluation", .. })
        ));

        let mut stack = vec![
            StackValue::Value(parameter(0, 0x19)),
            StackValue::Value(parameter(1, 0x15)),
        ];
        let expression = indy(&bytecode, site, &locals, &mut stack, "test").unwrap();
        assert!(!expression.infallible(), "Object.toString can execute user code");
    }

    #[test]
    fn escapes_utf16_at_each_nested_template_boundary() {
        let mut inner = Template::new();
        inner.push_text(Cow::Borrowed(&[0x22, 0x24, 0xd800, 0x2028]));
        inner.push_value(Argument {
            expr: Expr { kind: ExprKind::ThisProperty { name: "x", primitive: Primitive::Int }, depth: 2 },
            primitive: Some(Primitive::Int),
        }, true);
        let mut outer = Template::new();
        outer.push_value(Argument { expr: inner.finish("test").unwrap(), primitive: None }, true);
        outer.push_text(Cow::Borrowed(&[0x24, 0x22, 0xd83d, 0xde00]));
        let mut rendered = String::new();
        outer.finish("test").unwrap().write_at(&mut rendered, Expected::Reference, &[], "test", 0).unwrap();
        assert_eq!(rendered, r#""${"\"\$\uD800\u2028${this.x}"}\$\"😀""#);
    }

    #[test]
    fn nested_templates_obey_the_expression_depth_limit() {
        let mut expression = Expr {
            kind: ExprKind::ThisProperty { name: "x", primitive: Primitive::Int },
            depth: 2,
        };
        for _ in 2..64 {
            let primitive = (expression.depth == 2).then_some(Primitive::Int);
            let mut template = Template::new();
            template.push_value(Argument { expr: expression, primitive }, true);
            expression = template.finish("test").unwrap();
        }
        let mut template = Template::new();
        template.push_value(Argument { expr: expression, primitive: None }, true);
        assert!(matches!(
            template.finish("test"),
            Err(KotlinError::Unsupported { feature: "Kotlin expression nesting limit", .. })
        ));
    }
}
