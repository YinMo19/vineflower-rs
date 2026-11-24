// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::borrow::Cow;

use crate::{
    descriptor::{Primitive, Type},
    source_text::Document,
};

use super::{LiftError, Machine};

pub(super) const TERNARY: u8 = 1;
pub(super) const BIT_OR: u8 = 4;
pub(super) const BIT_XOR: u8 = 5;
pub(super) const BIT_AND: u8 = 6;
pub(super) const EQUALITY: u8 = 7;
pub(super) const RELATIONAL: u8 = 8;
pub(super) const SHIFT: u8 = 9;
pub(super) const ADDITIVE: u8 = 10;
pub(super) const MULTIPLICATIVE: u8 = 11;
pub(super) const UNARY: u8 = 12;
pub(super) const PRIMARY: u8 = 13;

pub(super) const INT: Type = Type::Primitive(Primitive::Int);
pub(super) const BOOLEAN: Type = Type::Primitive(Primitive::Boolean);

#[derive(Clone, Copy)]
pub(super) struct Order {
    pub(super) first: u32,
    pub(super) last: u32,
}

impl Order {
    pub(super) fn at(offset: u32) -> Self {
        Self {
            first: offset,
            last: offset,
        }
    }

    pub(super) fn includes_after(self, next: Self) -> Option<Self> {
        (self.last < next.first).then_some(Self {
            first: self.first,
            last: next.last,
        })
    }
}

#[derive(Clone)]
pub(super) enum Source {
    Local(u16),
    CapturedLocal,
    Plain,
    Integer(i32),
    Null,
    This,
    OuterThis,
    New(u32),
    Comparison(Box<Comparison>),
    StringBuilder(std::sync::Arc<Vec<super::concat::Operand>>),
    StringConversion(Box<Expr>),
}

#[derive(Clone)]
pub(super) struct Comparison {
    pub(super) left: Expr,
    pub(super) right: Expr,
    /// None for lcmp; -1 or 1 is the float/double result on NaN.
    pub(super) nan: Option<i8>,
}

#[derive(Clone)]
pub(super) struct Expr {
    pub(super) ty: Type,
    pub(super) text: Document,
    pub(super) source: Source,
    pub(super) precedence: u8,
    pub(super) order: Option<Order>,
    pub(super) observable: bool,
    pub(super) statement: bool,
    pub(super) constant: bool,
}

impl Expr {
    pub(super) fn atom(ty: Type, text: Document) -> Self {
        Self {
            ty,
            precedence: if text.starts_with('-') {
                UNARY
            } else {
                PRIMARY
            },
            text,
            source: Source::Plain,
            order: None,
            observable: false,
            statement: false,
            constant: false,
        }
    }

    pub(super) fn literal(ty: Type, text: Document) -> Self {
        Self {
            constant: true,
            ..Self::atom(ty, text)
        }
    }

    pub(super) fn integer(value: i32) -> Self {
        Self {
            source: Source::Integer(value),
            ..Self::literal(INT, value.to_string().into())
        }
    }

    pub(super) fn fits_int_local(&self, ty: &Type) -> bool {
        self.ty == *ty
            || *ty == INT
            || match (ty, &self.source) {
                (Type::Primitive(Primitive::Boolean), Source::Integer(0 | 1)) => true,
                (
                    Type::Primitive(
                        primitive @ (Primitive::Byte | Primitive::Char | Primitive::Short),
                    ),
                    Source::Integer(value),
                ) => representable(*value, *primitive),
                (Type::Primitive(Primitive::Short), _) => {
                    self.ty == Type::Primitive(Primitive::Byte)
                }
                _ => false,
            }
    }

    pub(super) fn at(&self, min: u8) -> Cow<'_, Document> {
        if self.needs_parens(min) {
            let mut text = self.text.clone();
            text.surround("(", ")");
            Cow::Owned(text)
        } else {
            Cow::Borrowed(&self.text)
        }
    }

    pub(super) fn append_at(&self, min: u8, out: &mut Document) {
        let parens = self.needs_parens(min);
        let starts_expression = !parens && out.is_empty();
        if parens {
            out.push('(');
        }
        out.append_ref(&self.text);
        if starts_expression {
            out.seal_qualifier();
        }
        if parens {
            out.push(')');
        }
    }

    pub(super) fn into_at(mut self, min: u8) -> Document {
        self.parenthesize(min);
        self.text
    }

    fn parenthesize(&mut self, min: u8) {
        if self.needs_parens(min) {
            self.text.surround("(", ")");
        }
    }

    fn needs_parens(&self, min: u8) -> bool {
        debug_assert!(!matches!(
            self.source,
            Source::New(_) | Source::Comparison(_)
        ));
        self.precedence < min
    }

    pub(super) fn is_uninitialized(&self, this_initialized: bool) -> bool {
        matches!(self.source, Source::New(_))
            || (!this_initialized && matches!(self.source, Source::This))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Category {
    Int,
    Long,
    Float,
    Double,
    Ref,
}

impl Category {
    pub(super) fn of(ty: &Type) -> Option<Self> {
        Some(match ty {
            Type::Primitive(Primitive::Long) => Self::Long,
            Type::Primitive(Primitive::Float) => Self::Float,
            Type::Primitive(Primitive::Double) => Self::Double,
            Type::Primitive(_) => Self::Int,
            Type::Object(_) | Type::Array(_) => Self::Ref,
            Type::Void => return None,
        })
    }

    pub(super) const fn for_local(opcode_index: u8) -> Self {
        [Self::Int, Self::Long, Self::Float, Self::Double, Self::Ref][opcode_index as usize]
    }

    pub(super) fn numeric_type(self) -> Type {
        Type::Primitive(match self {
            Self::Int => Primitive::Int,
            Self::Long => Primitive::Long,
            Self::Float => Primitive::Float,
            Self::Double => Primitive::Double,
            Self::Ref => unreachable!("reference is not numeric"),
        })
    }
}

#[derive(Clone, Copy)]
pub(super) enum Relation {
    Eq,
    Ne,
    Lt,
    Ge,
    Gt,
    Le,
}

impl Relation {
    pub(super) const fn opcode_index(index: u8) -> Self {
        [Self::Eq, Self::Ne, Self::Lt, Self::Ge, Self::Gt, Self::Le][index as usize]
    }

    pub(super) fn inverse(self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Ge => Self::Lt,
            Self::Gt => Self::Le,
            Self::Le => Self::Gt,
        }
    }

    pub(super) const fn operator(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Ge => ">=",
            Self::Gt => ">",
            Self::Le => "<=",
        }
    }

    pub(super) fn equality(self) -> bool {
        matches!(self, Self::Eq | Self::Ne)
    }

    pub(super) fn against(self, left: &Expr, right: &Expr) -> Document {
        let precedence = if self.equality() {
            EQUALITY
        } else {
            RELATIONAL
        };
        let mut text = Document::new();
        left.append_at(precedence, &mut text);
        text.push(' ');
        text.push_str(self.operator());
        text.push(' ');
        right.append_at(precedence + 1, &mut text);
        text
    }

    pub(super) fn against_cmp(self, cmp: &Comparison) -> Document {
        // Negating an ordered comparison is necessary to include NaN on
        // the side selected by fcmpl/fcmpg (and dcmpl/dcmpg).
        if matches!(
            (cmp.nan, self),
            (Some(-1), Self::Lt | Self::Le) | (Some(1), Self::Ge | Self::Gt)
        ) {
            let mut text = self.inverse().against(&cmp.left, &cmp.right);
            text.surround("!(", ")");
            text
        } else {
            self.against(&cmp.left, &cmp.right)
        }
    }
}

impl Machine<'_, '_> {
    pub(super) fn order_of<'e>(
        &self,
        values: impl IntoIterator<Item = &'e Expr>,
        own_effect: bool,
    ) -> Result<Option<Order>, LiftError> {
        let mut result = None;
        for next in values
            .into_iter()
            .filter_map(|value| value.order)
            .chain(own_effect.then(|| Order::at(self.offset)))
        {
            result = Some(self.join_order(result, next)?);
        }
        Ok(result)
    }

    pub(super) fn join_order(
        &self,
        previous: Option<Order>,
        next: Order,
    ) -> Result<Order, LiftError> {
        match previous {
            Some(previous) => previous
                .includes_after(next)
                .ok_or_else(|| self.unsupported("expression evaluation order")),
            None => Ok(next),
        }
    }

    pub(super) fn expression<'e>(
        &self,
        ty: Type,
        text: Document,
        precedence: u8,
        operands: impl IntoIterator<Item = &'e Expr> + Clone,
        effect: bool,
    ) -> Result<Expr, LiftError> {
        let order = self.order_of(operands.clone(), effect)?;
        let mut observable = effect;
        let mut constant = !effect
            && (matches!(&ty, Type::Primitive(_))
                || matches!(&ty, Type::Object(name) if name == "java/lang/String"));
        for operand in operands {
            observable |= operand.observable;
            constant &= operand.constant;
        }
        Ok(Expr {
            precedence,
            order,
            observable,
            constant,
            ..Expr::atom(ty, text)
        })
    }

    pub(super) fn cast(&self, expr: Expr, ty: Type, effect: bool) -> Result<Expr, LiftError> {
        let name = self.type_document(&ty);
        self.cast_named(expr, ty, effect, name)
    }

    fn cast_named(
        &self,
        expr: Expr,
        ty: Type,
        effect: bool,
        name: Document,
    ) -> Result<Expr, LiftError> {
        let mut text = Document::from("(");
        text.append(name);
        text.push(')');
        expr.append_at(UNARY, &mut text);
        self.expression(ty, text, UNARY, [&expr], effect)
    }

    pub(super) fn as_int(&self, mut expr: Expr) -> Expr {
        if expr.ty == BOOLEAN {
            expr.parenthesize(TERNARY + 1);
            expr.text.push_str(" ? 1 : 0");
            Expr {
                ty: INT,
                precedence: TERNARY,
                source: Source::Plain,
                statement: false,
                ..expr
            }
        } else {
            expr
        }
    }

    pub(super) fn boolean_value(&self, mut expr: Expr) -> Expr {
        if expr.ty == BOOLEAN {
            expr
        } else if let Source::Integer(value) = expr.source {
            Expr::literal(BOOLEAN, ((value & 1) != 0).to_string().into())
        } else {
            expr.parenthesize(BIT_AND);
            expr.text.surround("(", " & 1) != 0");
            Expr {
                ty: BOOLEAN,
                precedence: EQUALITY,
                source: Source::Plain,
                statement: false,
                ..expr
            }
        }
    }

    pub(super) fn coerce(
        &self,
        expr: Expr,
        ty: &Type,
        invocation: bool,
    ) -> Result<Expr, LiftError> {
        if Category::of(&expr.ty) != Category::of(ty) {
            return Err(self.invalid_stack("incompatible descriptor type"));
        }
        if expr.ty == *ty && !(invocation && matches!(expr.source, Source::Null)) {
            return Ok(expr);
        }
        if *ty == BOOLEAN {
            if invocation && !matches!(expr.source, Source::Integer(0 | 1)) {
                return Err(self.unsupported("non-boolean JVM int passed as a boolean argument"));
            }
            return Ok(self.boolean_value(expr));
        }
        if *ty == INT {
            let expr = self.as_int(expr);
            return if invocation && expr.ty != INT {
                self.cast(expr, INT, false)
            } else {
                Ok(expr)
            };
        }
        if let Type::Primitive(primitive @ (Primitive::Byte | Primitive::Char | Primitive::Short)) =
            ty
        {
            if let Source::Integer(value) = expr.source {
                if invocation && !representable(value, *primitive) {
                    return Err(self.unsupported("out-of-range int passed as a narrow argument"));
                }
                let value = Expr::literal(
                    ty.clone(),
                    super::literal::integer_literal(value, Some(ty), self.options.ascii_strings)
                        .into(),
                );
                return if invocation && *primitive != Primitive::Char {
                    self.cast(value, ty.clone(), false)
                } else {
                    Ok(value)
                };
            }
            if invocation
                && !matches!(
                    (&expr.ty, primitive),
                    (Type::Primitive(Primitive::Byte), Primitive::Short)
                )
            {
                return Err(self.unsupported("JVM int passed as a narrow argument"));
            }
            return self.cast(self.as_int(expr), ty.clone(), false);
        }
        if Category::of(ty) == Some(Category::Ref) {
            if !invocation
                && (matches!(expr.source, Source::Null) || self.known_assignable(&expr.ty, ty))
            {
                return Ok(expr);
            }
            return self.reference_cast(expr, ty.clone(), false);
        }
        Err(self.invalid_stack("incompatible descriptor type"))
    }

    pub(super) fn reference_cast(
        &self,
        expr: Expr,
        ty: Type,
        effect: bool,
    ) -> Result<Expr, LiftError> {
        self.reference_cast_with_name(expr, ty, effect, None)
    }

    pub(super) fn reference_cast_with_name(
        &self,
        expr: Expr,
        ty: Type,
        effect: bool,
        name: Option<Document>,
    ) -> Result<Expr, LiftError> {
        let object = Type::Object("java/lang/Object".into());
        let expr = if !matches!(expr.source, Source::Null)
            && !self.known_assignable(&expr.ty, &ty)
            && !self.known_assignable(&ty, &expr.ty)
            && (effect || matches!(expr.ty, Type::Array(_)) || matches!(ty, Type::Array(_)))
        {
            // Bytecode checkcast also accepts statically unrelated references.
            // Java requires a widening conversion in between.
            self.cast(expr, object, false)?
        } else {
            expr
        };
        if let Some(name) = name {
            self.cast_named(expr, ty, effect, name)
        } else {
            self.cast(expr, ty, effect)
        }
    }
}

fn representable(value: i32, primitive: Primitive) -> bool {
    match primitive {
        Primitive::Byte => i8::try_from(value).is_ok(),
        Primitive::Char => u16::try_from(value).is_ok(),
        Primitive::Short => i16::try_from(value).is_ok(),
        _ => unreachable!(),
    }
}
