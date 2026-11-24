// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    descriptor::{MethodDescriptor, Primitive, Type},
    source_text::Document,
};

use super::{
    LiftError, Machine, concat,
    expr::{Expr, Source},
};

// This surface fragment has already been rendered. Retaining another full
// expression would unnecessarily keep nested invocation metadata alive.
#[derive(Clone, PartialEq)]
pub(super) struct ReducedOperand {
    text: Document,
    precedence: u8,
}

impl From<Expr> for ReducedOperand {
    fn from(expr: Expr) -> Self {
        Self {
            text: expr.text,
            precedence: expr.precedence,
        }
    }
}

pub(super) fn wrapper(primitive: Primitive) -> (&'static str, &'static str) {
    use Primitive::*;
    match primitive {
        Boolean => ("java/lang/Boolean", "booleanValue"),
        Byte => ("java/lang/Byte", "byteValue"),
        Char => ("java/lang/Character", "charValue"),
        Short => ("java/lang/Short", "shortValue"),
        Int => ("java/lang/Integer", "intValue"),
        Long => ("java/lang/Long", "longValue"),
        Float => ("java/lang/Float", "floatValue"),
        Double => ("java/lang/Double", "doubleValue"),
    }
}

pub(super) fn unboxed(name: &str) -> Option<Primitive> {
    use Primitive::*;
    [Boolean, Byte, Char, Short, Int, Long, Float, Double]
        .into_iter()
        .find(|&primitive| wrapper(primitive).0 == name)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Conversion {
    Box,
    Unbox,
}

/// Recognize only wrappers' canonical valueOf/accessor pair. Other Number
/// methods may narrow, widen, or invoke an arbitrary override.
fn wrapper_conversion(
    opcode: u8,
    owner: &str,
    name: &str,
    descriptor: &MethodDescriptor,
) -> Option<Conversion> {
    if !owner.starts_with("java/lang/") || !matches!(opcode, 0xb6 | 0xb8)
        || !(name == "valueOf" || name.ends_with("Value"))
    {
        return None;
    }
    let primitive = unboxed(owner)?;
    let (_, accessor) = wrapper(primitive);
    let primitive = Type::Primitive(primitive);
    match opcode {
        0xb8 if name == "valueOf"
            && descriptor.parameters.as_slice() == std::slice::from_ref(&primitive)
            && matches!(&descriptor.return_type, Type::Object(result) if result == owner) => Some(Conversion::Box),
        0xb6 if name == accessor
            && descriptor.parameters.is_empty()
            && descriptor.return_type == primitive => Some(Conversion::Unbox),
        _ => None,
    }
}

impl Machine<'_, '_> {
    pub(super) fn invocation_source(
        &self,
        opcode: u8,
        owner: &str,
        name: &str,
        descriptor: &MethodDescriptor,
        receiver: Option<Expr>,
        mut args: Vec<Expr>,
    ) -> Source {
        if self.class.major_version >= 49 {
            match wrapper_conversion(opcode, owner, name, descriptor) {
                Some(Conversion::Box) => {
                    let operand = args.pop().expect("wrapper valueOf takes one argument");
                    if operand.ty == descriptor.parameters[0] {
                        // If javac widened an argument before invoking valueOf,
                        // implicit boxing might choose a different wrapper.
                        return Source::Boxing(Box::new(operand.into()));
                    }
                    return Source::Plain;
                }
                Some(Conversion::Unbox) => {
                    let receiver = receiver.expect("wrapper accessor is a virtual call");
                    if matches!(&receiver.ty, Type::Object(ty) if ty == owner) {
                        return Source::Unboxing(Box::new(receiver.into()));
                    }
                    return Source::Plain;
                }
                None => {}
            }
        }
        let omission = (self.options.include_line_mappings
            && self.normalized.is_none()
            && matches!(opcode, 0xb6 | 0xb8))
        .then(|| self.offset..self.offset + 3);
        concat::call_source(owner, name, descriptor, receiver, args, omission)
    }

    // These fragments are committed directly into Java assignment contexts.
    // In particular, do not use this for operands of a conditional expression,
    // where removing a wrapper changes the conditional's standalone type.
    pub(super) fn coerce_assignment(&self, value: Expr, expected: &Type) -> Result<Expr, LiftError> {
        let mut value = self.coerce(value, expected, false)?;
        if value.elide_final_widening(expected) {
            return Ok(value);
        }
        Ok(match (&value.source, expected) {
            (Source::Boxing(_), Type::Object(_)) if self.known_assignable(&value.ty, expected) => {
                self.implicit_conversion(value, Conversion::Box)
            }
            (Source::Unboxing(_), Type::Primitive(_)) => self.implicit_unboxing(value),
            _ => value,
        })
    }

    /// Use only where the Java operator or context forces primitive evaluation.
    /// The retained schedule includes the accessor's null check.
    pub(super) fn implicit_unboxing(&self, value: Expr) -> Expr {
        self.implicit_conversion(value, Conversion::Unbox)
    }

    pub(super) fn unbox_comparison(&self, left: Expr, right: Expr, equality: bool) -> (Expr, Expr) {
        // Java equality on two wrappers is a reference comparison (or is
        // invalid for distinct wrapper types), unlike JVM primitive equality.
        if equality && matches!(left.source, Source::Unboxing(_)) && matches!(right.source, Source::Unboxing(_)) {
            (self.implicit_unboxing(left), right)
        } else {
            (self.implicit_unboxing(left), self.implicit_unboxing(right))
        }
    }

    fn implicit_conversion(&self, value: Expr, class: Conversion) -> Expr {
        let operand = match value.source {
            Source::Boxing(operand) if class == Conversion::Box => operand,
            Source::Unboxing(operand) if class == Conversion::Unbox => operand,
            _ => return value,
        };
        let ReducedOperand { mut text, precedence } = *operand;
        if self.options.include_line_mappings && self.normalized.is_none()
            && let Some(order) = value.order
        {
            let mut mapped = Document::new();
            // Both recognized invocation opcodes are exactly three bytes.
            mapped.anchor(order.last..order.last + 3);
            mapped.append(text);
            text = mapped;
        }
        Expr {
            text,
            precedence,
            source: Source::Plain,
            // Assignment or the primitive operator will perform this call.
            // Keep effects/ordering, but it is no longer a standalone call.
            statement: false,
            constant: false,
            ..value
        }
    }
}

impl Expr {
    /// Keep any preceding cast: an intermediate float conversion may round.
    pub(super) fn elide_final_widening(&mut self, expected: &Type) -> bool {
        let Source::WidenedPrimitive { operand_precedence, .. } = self.source else {
            return false;
        };
        let Type::Primitive(target) = expected else { return false };
        if self.ty != *expected {
            return false;
        }
        let enclosed = operand_precedence < super::expr::UNARY;
        let prefix_len = target.java_name().len() + 2 + usize::from(enclosed);
        self.text.replace_literal_prefix(prefix_len, "");
        if enclosed {
            self.text.pop();
        }
        self.precedence = operand_precedence;
        self.source = Source::Plain;
        true
    }
}
