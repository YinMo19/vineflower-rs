// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::borrow::Cow;

use crate::source_text::{Document, Infix};

use super::{Machine, expr::{BOOLEAN, Expr, PRIMARY, Source, TERNARY, UNARY}};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Atom {
    Other,
    Constant(bool),
    Local(u16),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct BooleanFact {
    atom: Atom,
    precedence: u8,
}

impl BooleanFact {
    fn expression(precedence: u8) -> Self {
        Self { atom: Atom::Other, precedence }
    }

    pub(super) fn constant(value: bool) -> Self {
        Self { atom: Atom::Constant(value), precedence: PRIMARY }
    }

    pub(super) fn operand(value: &Expr) -> Option<Self> {
        match value.source {
            Source::Integer(0) => Some(Self::constant(false)),
            Source::Integer(1) => Some(Self::constant(true)),
            Source::Local(slot) if value.ty == BOOLEAN && !value.observable => {
                Some(Self { atom: Atom::Local(slot), precedence: value.precedence })
            }
            _ if value.ty == BOOLEAN => Some(Self::expression(value.precedence)),
            _ => None,
        }
    }

    pub(super) fn precedence(self) -> u8 {
        self.precedence.max(TERNARY)
    }

    pub(super) fn literal(self) -> Option<bool> {
        match self.atom {
            Atom::Constant(value) => Some(value),
            _ => None,
        }
    }

    fn with_layout(self, text: &Document) -> Self {
        text.infix().map_or(self, |infix| Self::expression(infix.precedence))
    }
}

/// Facts about the branch and its inverse, in that order. Only a direct,
/// positively tested, non-observable JVM local may stand in for an arm.
#[derive(Clone, Copy, Debug)]
pub(crate) struct BooleanCondition([BooleanFact; 2]);

impl BooleanCondition {
    pub(crate) const UNKNOWN: Self = Self([BooleanFact { atom: Atom::Other, precedence: 0 }; 2]);

    pub(super) fn tested(value: &Expr, jumps_on_true: bool) -> Self {
        let value = BooleanFact::operand(value).expect("conditional on a boolean operand");
        let mut condition = Self([value, BooleanFact::expression(UNARY)]);
        if !jumps_on_true {
            condition.0.swap(0, 1);
        }
        condition
    }

    pub(super) fn comparison() -> Self {
        Self([BooleanFact::expression(super::expr::EQUALITY); 2])
    }

    pub(crate) fn orient(mut self, jumps_to_then: bool) -> Self {
        if !jumps_to_then {
            self.0.swap(0, 1);
        }
        self
    }
}

#[derive(Clone, Copy)]
pub(crate) enum BooleanSelection {
    Condition { inverse: bool },
    ShortCircuit { inverse: bool, and: bool, uses_true: bool },
    Ternary,
}

impl BooleanSelection {
    pub(crate) fn of(condition: BooleanCondition, yes: BooleanFact, no: BooleanFact, simplify: bool) -> Self {
        match (yes.atom, no.atom) {
            (Atom::Constant(true), Atom::Constant(false)) => Self::Condition { inverse: false },
            (Atom::Constant(false), Atom::Constant(true)) => Self::Condition { inverse: true },
            (Atom::Constant(value), _) if simplify => {
                Self::ShortCircuit { inverse: !value, and: !value, uses_true: false }
            }
            (_, Atom::Constant(value)) if simplify => {
                Self::ShortCircuit { inverse: value, and: !value, uses_true: true }
            }
            (Atom::Local(slot), _) if simplify && condition.0[0].atom == Atom::Local(slot) => {
                Self::ShortCircuit { inverse: false, and: false, uses_true: false }
            }
            (_, Atom::Local(slot)) if simplify && condition.0[0].atom == Atom::Local(slot) => {
                Self::ShortCircuit { inverse: false, and: true, uses_true: true }
            }
            _ => Self::Ternary,
        }
    }

    pub(crate) fn uses(self, true_arm: bool) -> bool {
        match self {
            Self::Condition { .. } => false,
            Self::ShortCircuit { uses_true, .. } => uses_true == true_arm,
            Self::Ternary => true,
        }
    }

    pub(crate) fn render<'d>(
        self,
        condition: (BooleanCondition, [Cow<'d, Document>; 2]),
        yes: (BooleanFact, Cow<'d, Document>),
        no: (BooleanFact, Cow<'d, Document>),
    ) -> (BooleanFact, Document) {
        let (BooleanCondition([direct, negated]), [expression, inverse]) = condition;
        match self {
            Self::Condition { inverse: false } => {
                (direct.with_layout(&expression), expression.into_owned())
            }
            Self::Condition { inverse: true } => {
                (negated.with_layout(&inverse), inverse.into_owned())
            }
            Self::ShortCircuit { inverse: negate, and, uses_true } => {
                let (left, left_text) = if negate { (negated, inverse) } else { (direct, expression) };
                let (right, right_text) = if uses_true { yes } else { no };
                let infix = if and { Infix::AND } else { Infix::OR };
                let text = Document::infix_expression(
                    infix,
                    [(left, &*left_text), (right, &*right_text)].map(|(fact, text)| {
                        (text, fact.with_layout(text).precedence < infix.precedence)
                    }),
                );
                (BooleanFact::expression(infix.precedence), text)
            }
            Self::Ternary => {
                let parens = direct.with_layout(&expression).precedence <= TERNARY;
                let text = Document::ternary_expression([&expression, &yes.1, &no.1], parens);
                (BooleanFact::expression(TERNARY), text)
            }
        }
    }
}

impl Machine<'_, '_> {
    pub(crate) fn simplify_boolean_ternaries(&self) -> bool {
        self.options.ternary_constant_simplification
    }

    pub(crate) fn simplify_boolean_returns(&self) -> bool {
        self.simplify_boolean_ternaries() && self.descriptor.return_type == BOOLEAN
    }

    pub(crate) fn last_boolean_condition(&self) -> BooleanCondition {
        self.boolean_condition
    }

    pub(crate) fn last_boolean_return(&self) -> Option<(BooleanFact, u32)> {
        self.boolean_return.map(|fact| (fact, self.offset))
    }
}
