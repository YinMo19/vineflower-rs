// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{
    Expected, Expr, ExprKind, KotlinError, Literal, Primitive, StackValue, Type, ValueParameter,
    pop_value,
};

// From tightest to loosest: unary, multiplicative, additive, infix,
// relational, equality, conjunction, disjunction, conditional.
pub(super) const UNARY: u8 = 8;
pub(super) const MULTIPLICATIVE: u8 = 7;
pub(super) const ADDITIVE: u8 = 6;
pub(super) const INFIX: u8 = 5;
pub(super) const RELATIONAL: u8 = 4;
const EQUALITY: u8 = 3;
const AND: u8 = 2;
const OR: u8 = 1;

#[derive(Clone, Copy, Debug)]
pub(super) enum Relation {
    Eq,
    Ne,
    Lt,
    Ge,
    Gt,
    Le,
    Same,
    Different,
}

impl Relation {
    fn complement(self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Ge => Self::Lt,
            Self::Gt => Self::Le,
            Self::Le => Self::Gt,
            Self::Same => Self::Different,
            Self::Different => Self::Same,
        }
    }

    fn text(self) -> &'static str {
        match self {
            Self::Eq => " == ",
            Self::Ne => " != ",
            Self::Lt => " < ",
            Self::Ge => " >= ",
            Self::Gt => " > ",
            Self::Le => " <= ",
            Self::Same => " === ",
            Self::Different => " !== ",
        }
    }

    fn equality(self) -> bool {
        matches!(self, Self::Eq | Self::Ne | Self::Same | Self::Different)
    }
}

#[derive(Debug)]
pub(super) struct Comparison<'a> {
    left: Expr<'a>,
    right: Expr<'a>,
    relation: Relation,
    operand: Expected<'a>,
}

impl<'a> Comparison<'a> {
    pub(super) fn reference(
        relation: Relation,
        left: Expr<'a>,
        right: Expr<'a>,
        declaration: &str,
    ) -> Result<Expr<'a>, KotlinError> {
        Self::new(relation, left, right, Expected::Reference, declaration)
    }

    fn new(
        relation: Relation,
        left: Expr<'a>,
        right: Expr<'a>,
        operand: Expected<'a>,
        declaration: &str,
    ) -> Result<Expr<'a>, KotlinError> {
        let depth = left.depth.max(right.depth) + 1;
        Expr::new(
            ExprKind::Compare(Box::new(Self {
                left,
                right,
                relation,
                operand,
            })),
            depth,
            declaration,
        )
    }

    pub(super) fn write(
        &self,
        out: &mut String,
        expected: Expected<'_>,
        parameters: &[ValueParameter],
        declaration: &str,
        binding: u8,
    ) -> Result<(), KotlinError> {
        require_boolean(expected, declaration)?;
        let current = if self.relation.equality() {
            EQUALITY
        } else {
            RELATIONAL
        };
        let cast = matches!(self.operand, Expected::Reference)
            && reference_cast(&self.left, &self.right, parameters);
        if binding > current {
            out.push('(');
        }
        self.write_operand(out, &self.left, parameters, declaration, current + 1, cast)?;
        out.push_str(self.relation.text());
        self.write_operand(out, &self.right, parameters, declaration, current + 1, cast)?;
        if binding > current {
            out.push(')');
        }
        Ok(())
    }

    fn write_operand(
        &self,
        out: &mut String,
        expr: &Expr<'_>,
        parameters: &[ValueParameter],
        declaration: &str,
        binding: u8,
        cast: bool,
    ) -> Result<(), KotlinError> {
        // Comparison is not an expected-type context for integer literals.
        let narrowing = if matches!(expr.kind, ExprKind::Literal(Literal::Int(_))) {
            match self.operand {
                Expected::Primitive(Primitive::Byte) => Some(").toByte()"),
                Expected::Primitive(Primitive::Short) => Some(").toShort()"),
                _ => None,
            }
        } else {
            None
        };
        if cast {
            out.push('(');
            expr.write_at(out, self.operand, parameters, declaration, UNARY)?;
            out.push_str(" as kotlin.Any?)");
        } else if let Some(conversion) = narrowing {
            out.push('(');
            expr.write_at(out, self.operand, parameters, declaration, 0)?;
            out.push_str(conversion);
        } else {
            expr.write_at(out, self.operand, parameters, declaration, binding)?;
        }
        Ok(())
    }
}

fn reference_cast(left: &Expr<'_>, right: &Expr<'_>, parameters: &[ValueParameter]) -> bool {
    // An Object/Object Intrinsics.areEqual uses boxed equality. In particular,
    // Float? == Float? in Kotlin instead uses IEEE rules. Upcast when source
    // equality has different semantics or static types could make it illegal.
    if matches!(left.kind, ExprKind::Literal(Literal::Null))
        || matches!(right.kind, ExprKind::Literal(Literal::Null))
    {
        return false;
    }
    let ty = |index: usize| &parameters[index].ty;
    let any_or_string = |ty: &Type| matches!(ty.class_id(), Some("kotlin/Any" | "kotlin/String"));
    match (&left.kind, &right.kind) {
        (ExprKind::Parameter { index: a, .. }, ExprKind::Parameter { index: b, .. }) => {
            let (a, b) = (ty(*a), ty(*b));
            !any_or_string(a) || !any_or_string(b)
        }
        (ExprKind::Literal(Literal::String(_)), ExprKind::Parameter { index, .. })
        | (ExprKind::Parameter { index, .. }, ExprKind::Literal(Literal::String(_))) => {
            !any_or_string(ty(*index))
        }
        (ExprKind::BoxedInt(_), ExprKind::Parameter { index, .. })
        | (ExprKind::Parameter { index, .. }, ExprKind::BoxedInt(_)) => {
            ty(*index).class_id() != Some("kotlin/Any")
        }
        (ExprKind::Literal(Literal::String(_)), ExprKind::Literal(Literal::String(_))) => false,
        _ => true,
    }
}

#[derive(Debug)]
pub(super) struct Conditional<'a> {
    guard: Expr<'a>,
    yes: Expr<'a>,
    no: Expr<'a>,
}

impl<'a> Conditional<'a> {
    pub(super) fn new(
        guard: Expr<'a>,
        yes: Expr<'a>,
        no: Expr<'a>,
        declaration: &str,
    ) -> Result<Expr<'a>, KotlinError> {
        let depth = guard.depth.max(yes.depth).max(no.depth) + 1;
        Expr::new(
            ExprKind::Conditional(Box::new(Self { guard, yes, no })),
            depth,
            declaration,
        )
    }

    pub(super) fn primitive_hint(&self, parameters: &[ValueParameter]) -> Option<Primitive> {
        compatible_hint(
            self.yes.primitive_hint(parameters),
            self.no.primitive_hint(parameters),
        )
    }

    pub(super) fn write(
        &self,
        out: &mut String,
        expected: Expected<'_>,
        parameters: &[ValueParameter],
        declaration: &str,
        binding: u8,
    ) -> Result<(), KotlinError> {
        let boolean = Expected::Primitive(Primitive::Boolean);
        if expected.primitive() == Some(Primitive::Boolean) {
            let yes = boolean_constant(&self.yes);
            let no = boolean_constant(&self.no);
            match (yes, no) {
                (Some(true), Some(false)) => {
                    return self
                        .guard
                        .write_at(out, boolean, parameters, declaration, binding);
                }
                (Some(false), Some(true)) => {
                    return write_negation(out, &self.guard, parameters, declaration, binding);
                }
                (Some(true), _) | (_, Some(false)) | (Some(false), _) | (_, Some(true)) => {
                    let (and, negate, rhs) = match (yes, no) {
                        (Some(true), _) => (false, false, &self.no),
                        (_, Some(false)) => (true, false, &self.yes),
                        (Some(false), _) => (true, true, &self.no),
                        (_, Some(true)) => (false, true, &self.yes),
                        _ => unreachable!(),
                    };
                    let current = if and { AND } else { OR };
                    if binding > current {
                        out.push('(');
                    }
                    if negate {
                        write_negation(out, &self.guard, parameters, declaration, current)?;
                    } else {
                        self.guard
                            .write_at(out, boolean, parameters, declaration, current)?;
                    }
                    out.push_str(if and { " && " } else { " || " });
                    rhs.write_at(out, boolean, parameters, declaration, current + 1)?;
                    if binding > current {
                        out.push(')');
                    }
                    return Ok(());
                }
                _ => {}
            }
        }
        if binding > 0 {
            out.push('(');
        }
        out.push_str("if (");
        self.guard
            .write_at(out, boolean, parameters, declaration, 0)?;
        out.push_str(") ");
        self.yes
            .write_at(out, expected, parameters, declaration, 0)?;
        out.push_str(" else ");
        self.no
            .write_at(out, expected, parameters, declaration, 0)?;
        if binding > 0 {
            out.push(')');
        }
        Ok(())
    }
}

fn boolean_constant(expr: &Expr<'_>) -> Option<bool> {
    match expr.kind {
        ExprKind::Literal(Literal::Int(0)) => Some(false),
        ExprKind::Literal(Literal::Int(1)) => Some(true),
        _ => None,
    }
}

fn boolean_value(expr: &Expr<'_>, parameters: &[ValueParameter]) -> bool {
    if let ExprKind::Conditional(conditional) = &expr.kind {
        boolean_value(&conditional.yes, parameters) && boolean_value(&conditional.no, parameters)
    } else {
        boolean_constant(expr).is_some()
            || expr.primitive_hint(parameters) == Some(Primitive::Boolean)
    }
}

pub(super) fn require_boolean(
    expected: Expected<'_>,
    declaration: &str,
) -> Result<(), KotlinError> {
    if expected.primitive() != Some(Primitive::Boolean) {
        return Err(KotlinError::unsupported(
            declaration,
            "boolean expression in non-Boolean context",
        ));
    }
    Ok(())
}

pub(super) fn write_negation(
    out: &mut String,
    expr: &Expr<'_>,
    parameters: &[ValueParameter],
    declaration: &str,
    binding: u8,
) -> Result<(), KotlinError> {
    let boolean = Expected::Primitive(Primitive::Boolean);
    if let ExprKind::Not(inner) = &expr.kind {
        return inner.write_at(out, boolean, parameters, declaration, binding);
    }
    out.push('!');
    expr.write_at(out, boolean, parameters, declaration, UNARY)
}

pub(super) fn negate<'a>(mut expr: Expr<'a>, declaration: &str) -> Result<Expr<'a>, KotlinError> {
    match &mut expr.kind {
        ExprKind::Compare(compare) => {
            compare.relation = compare.relation.complement();
            Ok(expr)
        }
        ExprKind::TypeTest { negative, .. } => {
            *negative = !*negative;
            Ok(expr)
        }
        _ => {
            let depth = expr.depth + 1;
            Expr::new(ExprKind::Not(Box::new(expr)), depth, declaration)
        }
    }
}

pub(super) fn condition<'a>(
    opcode: u8,
    stack: &mut Vec<StackValue<'a>>,
    parameters: &[ValueParameter],
    declaration: &str,
) -> Result<Expr<'a>, KotlinError> {
    // Kotlin conventionally branches *around* the true arm. Recover the
    // fallthrough predicate; its negation selects the bytecode branch target.
    const RELATIONS: [Relation; 6] = [
        Relation::Ne,
        Relation::Eq,
        Relation::Ge,
        Relation::Lt,
        Relation::Le,
        Relation::Gt,
    ];
    match opcode {
        0x99..=0x9e => {
            let relation = RELATIONS[usize::from(opcode - 0x99)];
            match stack.pop() {
                Some(StackValue::LongOrder) => {
                    let right = pop_value(stack, declaration)?;
                    let left = pop_value(stack, declaration)?;
                    Comparison::new(
                        relation,
                        left,
                        right,
                        Expected::Primitive(Primitive::Long),
                        declaration,
                    )
                }
                Some(StackValue::Value(expr)) => {
                    let primitive = if relation.equality() && boolean_value(&expr, parameters) {
                        Primitive::Boolean
                    } else {
                        integer_kind(expr.primitive_hint(parameters), None, declaration)?
                    };
                    if primitive == Primitive::Boolean {
                        match relation {
                            Relation::Ne => Ok(expr),
                            Relation::Eq => negate(expr, declaration),
                            _ => Err(KotlinError::unsupported(
                                declaration,
                                "ordered Boolean branch",
                            )),
                        }
                    } else {
                        Comparison::new(
                            relation,
                            expr,
                            Expr::literal(Literal::Int(0)),
                            Expected::Primitive(primitive),
                            declaration,
                        )
                    }
                }
                _ => Err(KotlinError::unsupported(
                    declaration,
                    "missing branch operand",
                )),
            }
        }
        0x9f..=0xa4 => {
            let relation = RELATIONS[usize::from(opcode - 0x9f)];
            let right = pop_value(stack, declaration)?;
            let left = pop_value(stack, declaration)?;
            let primitive = integer_kind(
                left.primitive_hint(parameters),
                right.primitive_hint(parameters),
                declaration,
            )?;
            if primitive == Primitive::Boolean && !relation.equality() {
                return Err(KotlinError::unsupported(
                    declaration,
                    "ordered Boolean branch",
                ));
            }
            Comparison::new(
                relation,
                left,
                right,
                Expected::Primitive(primitive),
                declaration,
            )
        }
        0xa5..=0xa6 => {
            let right = pop_value(stack, declaration)?;
            let left = pop_value(stack, declaration)?;
            Comparison::reference(
                if opcode == 0xa5 {
                    Relation::Different
                } else {
                    Relation::Same
                },
                left,
                right,
                declaration,
            )
        }
        0xc6..=0xc7 => {
            let left = pop_value(stack, declaration)?;
            Comparison::reference(
                if opcode == 0xc6 {
                    Relation::Ne
                } else {
                    Relation::Eq
                },
                left,
                Expr::literal(Literal::Null),
                declaration,
            )
        }
        _ => Err(KotlinError::unsupported(
            declaration,
            "unsupported conditional transfer",
        )),
    }
}

fn integer_kind(
    left: Option<Primitive>,
    right: Option<Primitive>,
    declaration: &str,
) -> Result<Primitive, KotlinError> {
    let primitive = match (left, right) {
        (None, None) => Primitive::Int,
        _ => compatible_hint(left, right).ok_or_else(|| {
            KotlinError::unsupported(declaration, "incompatible comparison operands")
        })?,
    };
    match primitive {
        Primitive::Byte
        | Primitive::Short
        | Primitive::Char
        | Primitive::Int
        | Primitive::Boolean => Ok(primitive),
        _ => Err(KotlinError::unsupported(
            declaration,
            "invalid integer branch operands",
        )),
    }
}

fn compatible_hint(left: Option<Primitive>, right: Option<Primitive>) -> Option<Primitive> {
    match (left, right) {
        (Some(left), Some(right)) if left != right => None,
        _ => left.or(right),
    }
}

pub(super) fn primitive_type(ty: &Type) -> Option<Primitive> {
    if ty.nullable {
        return None;
    }
    match ty.class_id()? {
        "kotlin/Boolean" => Some(Primitive::Boolean),
        "kotlin/Byte" => Some(Primitive::Byte),
        "kotlin/Char" => Some(Primitive::Char),
        "kotlin/Short" => Some(Primitive::Short),
        "kotlin/Int" => Some(Primitive::Int),
        "kotlin/Long" => Some(Primitive::Long),
        "kotlin/Float" => Some(Primitive::Float),
        "kotlin/Double" => Some(Primitive::Double),
        _ => None,
    }
}
