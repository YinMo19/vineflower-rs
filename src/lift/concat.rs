// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use std::fmt::Write;
use std::sync::Arc;

use crate::descriptor::{MethodDescriptor, Primitive, Type};

use super::expr::{ADDITIVE, Category, Expr, Source};
use super::{Effect, LiftError, Machine};

#[derive(Clone)]
pub(super) struct Operand {
    text: String,
    string: bool,
    constant: bool,
}

impl From<Expr> for Operand {
    fn from(value: Expr) -> Self {
        Self {
            string: is_string(&value.ty),
            constant: value.constant,
            text: if value.precedence <= ADDITIVE {
                format!("({})", value.text)
            } else {
                value.text
            },
        }
    }
}

pub(super) fn is_string(ty: &Type) -> bool {
    matches!(ty, Type::Object(name) if name == "java/lang/String")
}

fn is_builder(owner: &str) -> bool {
    matches!(owner, "java/lang/StringBuilder" | "java/lang/StringBuffer")
}

fn printable(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Primitive(
            Primitive::Boolean
                | Primitive::Char
                | Primitive::Int
                | Primitive::Long
                | Primitive::Float
                | Primitive::Double
        )
    ) || matches!(ty, Type::Object(name) if name == "java/lang/Object")
}

pub(super) fn builder_constructor(owner: &str, descriptor: &str, mut args: Vec<Expr>) -> Source {
    match (is_builder(owner), descriptor) {
        (true, "()V") => Source::StringBuilder(Arc::new(Vec::new())),
        (true, "(Ljava/lang/String;)V") if args[0].constant => {
            // The String constructor dereferences its argument. A nullable
            // argument cannot be replaced with a null-tolerant concatenation.
            Source::StringBuilder(Arc::new(vec![args.pop().unwrap().into()]))
        }
        _ => Source::Plain,
    }
}

pub(super) fn call_source(
    owner: &str,
    name: &str,
    descriptor: &MethodDescriptor,
    receiver: Option<Expr>,
    mut args: Vec<Expr>,
) -> Source {
    let [parameter] = descriptor.parameters.as_slice() else {
        return Source::Plain;
    };
    match receiver {
        Some(Expr {
            source: Source::StringBuilder(mut parts),
            ..
        }) if name == "append"
            && is_builder(owner)
            && matches!(&descriptor.return_type, Type::Object(result) if result == owner)
            && (printable(parameter) || is_string(parameter)) =>
        {
            Arc::make_mut(&mut parts).push(args.pop().unwrap().into());
            Source::StringBuilder(parts)
        }
        None if owner == "java/lang/String"
            && name == "valueOf"
            && is_string(&descriptor.return_type)
            && printable(parameter) =>
        {
            Source::StringConversion(Box::new(args.pop().unwrap()))
        }
        _ => Source::Plain,
    }
}

impl Machine<'_, '_> {
    pub(super) fn emit_builder_concat(
        &mut self,
        owner: &str,
        name: &str,
        descriptor: &str,
        receiver: Option<&Expr>,
    ) -> Result<Option<Effect>, LiftError> {
        let Some(receiver) = receiver else {
            return Ok(None);
        };
        if !is_builder(owner) || name != "toString" || descriptor != "()Ljava/lang/String;" {
            return Ok(None);
        }
        let Source::StringBuilder(parts) = &receiver.source else {
            return Ok(None);
        };
        if parts.is_empty() || parts.iter().all(|part| part.constant) {
            return Ok(None);
        }
        let mut text = String::new();
        if !parts.iter().take(2).any(|part| part.string) {
            text.push_str("\"\"");
        }
        for part in parts.iter() {
            if !text.is_empty() {
                text.push_str(" + ");
            }
            text.push_str(&part.text);
        }
        if parts.len() == 1 && parts[0].string {
            // Appending an empty literal still creates a fresh String on the
            // evaluated path, unlike simply returning the String operand.
            text.push_str(" + \"\"");
        }
        self.push(self.expression(
            Type::Object("java/lang/String".into()),
            text,
            ADDITIVE,
            [receiver],
            true,
        )?)?;
        Ok(Some(Effect::None))
    }
}

/// Move eager javac conversions into the infix expression only when the
/// operation cannot pass any delayed conversion or observable argument.
pub(super) fn inline_value_of(args: &mut [Expr]) {
    let eager_reference = |arg: &Expr| {
        matches!(&arg.source, Source::StringConversion(value)
        if Category::of(&value.ty) == Some(Category::Ref))
    };
    let can_move_references = if let Some(first) = args.iter().position(eager_reference) {
        let last = args
            .iter()
            .rposition(eager_reference)
            .expect("first conversion exists");
        // Either move all eager reference conversions in order or keep all
        // of them; retaining a later one could move it ahead of an earlier
        // converted operand.
        let no_intervening_evaluation = args[first + 1..].iter().all(|arg| match &arg.source {
            Source::StringConversion(value) => !value.observable,
            _ => !arg.observable,
        });
        let no_delayed_conversion_overtakes = args[..last].iter().all(|arg| {
            matches!(arg.source, Source::StringConversion(_) | Source::Null)
                || Category::of(&arg.ty) != Some(Category::Ref)
                || is_string(&arg.ty)
        });
        no_intervening_evaluation && no_delayed_conversion_overtakes
    } else {
        false
    };
    for arg in args {
        if matches!(arg.source, Source::StringConversion(_))
            && (can_move_references || !eager_reference(arg))
        {
            let Source::StringConversion(inner) = std::mem::replace(&mut arg.source, Source::Plain)
            else {
                unreachable!();
            };
            let mut inner = *inner;
            inner.order = arg.order;
            inner.observable = arg.observable;
            *arg = inner;
        }
    }
}

pub(super) fn push_joined(text: &mut String, operand: &Expr) {
    if !text.is_empty() {
        text.push_str(" + ");
    }
    let _ = write!(text, "{}", operand.at(ADDITIVE + 1));
}
