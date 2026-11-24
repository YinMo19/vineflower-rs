// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::fmt::Write;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{OffsetTarget, TypeArgumentTarget, TypeTarget},
    descriptor::{Primitive, Type},
};

use super::{
    Effect, LiftError, Machine,
    expr::{
        ADDITIVE, BIT_AND, BIT_OR, BIT_XOR, BOOLEAN, Category, Comparison, Expr, INT,
        MULTIPLICATIVE, PRIMARY, RELATIONAL, Relation, SHIFT, Source, TERNARY, UNARY,
    },
    object_type,
};

impl Machine<'_, '_> {
    pub(super) fn arithmetic(&mut self, opcode: u8) -> Result<(), LiftError> {
        if (0x74..=0x77).contains(&opcode) {
            let category = Category::for_local(opcode - 0x74);
            let value = self.pop_category(category)?;
            let value = self.as_int(value);
            // At equal precedence a unary minus can become a prefix -- token.
            let text = format!("-{}", value.at(UNARY + 1));
            return self.push(self.expression(
                category.numeric_type(),
                text,
                UNARY,
                [&value],
                false,
            )?);
        }
        let (category, right_category, operator, precedence) = if opcode < 0x74 {
            let relative = opcode - 0x60;
            let category = Category::for_local(relative % 4);
            let (operator, precedence) = [
                ("+", ADDITIVE),
                ("-", ADDITIVE),
                ("*", MULTIPLICATIVE),
                ("/", MULTIPLICATIVE),
                ("%", MULTIPLICATIVE),
            ][usize::from(relative / 4)];
            (category, category, operator, precedence)
        } else {
            let relative = opcode - 0x78;
            let category = Category::for_local(relative % 2);
            let right_category = if relative < 6 {
                Category::Int
            } else {
                category
            };
            let (operator, precedence) = [
                ("<<", SHIFT),
                (">>", SHIFT),
                (">>>", SHIFT),
                ("&", BIT_AND),
                ("|", BIT_OR),
                ("^", BIT_XOR),
            ][usize::from(relative / 2)];
            (category, right_category, operator, precedence)
        };
        let right = self.pop_category(right_category)?;
        let left = self.pop_category(category)?;
        let boolean = opcode >= 0x7e
            && (left.ty == BOOLEAN || right.ty == BOOLEAN)
            && [&left, &right]
                .into_iter()
                .all(|value| value.ty == BOOLEAN || matches!(value.source, Source::Integer(0 | 1)));
        let (left, right, ty) = if boolean {
            (self.boolean_value(left), self.boolean_value(right), BOOLEAN)
        } else {
            (
                self.as_int(left),
                self.as_int(right),
                category.numeric_type(),
            )
        };
        let can_throw =
            matches!(category, Category::Int | Category::Long) && matches!(operator, "/" | "%");
        let text = format!(
            "{} {operator} {}",
            left.at(precedence),
            right.at(precedence + 1)
        );
        self.push(self.expression(ty, text, precedence, [&left, &right], can_throw)?)
    }

    pub(super) fn convert(&mut self, index: u8) -> Result<(), LiftError> {
        use Category::{Double as D, Float as F, Int as I, Long as J};
        use Primitive::{Byte, Char, Double, Float, Int, Long, Short};
        let (from, to) = [
            (I, Long),
            (I, Float),
            (I, Double),
            (J, Int),
            (J, Float),
            (J, Double),
            (F, Int),
            (F, Long),
            (F, Double),
            (D, Int),
            (D, Long),
            (D, Float),
            (I, Byte),
            (I, Char),
            (I, Short),
        ][usize::from(index)];
        let value = self.pop_category(from)?;
        self.push(self.cast(self.as_int(value), Type::Primitive(to), false)?)
    }

    pub(super) fn compare(&mut self, index: u8) -> Result<(), LiftError> {
        let category = [
            Category::Long,
            Category::Float,
            Category::Float,
            Category::Double,
            Category::Double,
        ][usize::from(index)];
        let right = self.pop_category(category)?;
        let left = self.pop_category(category)?;
        let order = self.order_of([&left, &right], false)?;
        let observable = left.observable || right.observable;
        let nan = match index {
            0 => None,
            1 | 3 => Some(-1),
            _ => Some(1),
        };
        self.push(Expr {
            source: Source::Comparison(Box::new(Comparison { left, right, nan })),
            order,
            observable,
            ..Expr::atom(INT, String::new())
        })
    }

    pub(super) fn lower_pending_comparison(&mut self) -> Result<(), LiftError> {
        if !matches!(
            self.stack.last().map(|value| &value.source),
            Some(Source::Comparison(_))
        ) {
            return Ok(());
        }
        let Source::Comparison(cmp) = self.pop_raw()?.source else {
            unreachable!()
        };
        let Comparison { left, right, nan } = *cmp;
        let mut values = [left, right];
        // A standalone comparison result requires two tests. Evaluate
        // nonconstant operands only once, in their original order.
        self.freeze_values(&mut values)?;
        let [left, right] = values;
        let fallback = nan.unwrap_or(-1);
        let relation = if fallback < 0 {
            Relation::Gt
        } else {
            Relation::Lt
        };
        let ordered = relation.against(&left, &right);
        let equal = Relation::Eq.against(&left, &right);
        self.push(self.expression(
            INT,
            format!("{ordered} ? {} : {equal} ? 0 : {fallback}", -fallback),
            TERNARY,
            [&left, &right],
            false,
        )?)
    }

    pub(super) fn conditional(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        let target = self.target(op)?;
        let (when_true, when_false) = match op.opcode {
            0x99..=0x9e => {
                let relation = Relation::opcode_index(op.opcode - 0x99);
                let value = self.pop_category(Category::Int)?;
                if let Source::Comparison(cmp) = value.source {
                    (
                        relation.against_cmp(&cmp),
                        relation.inverse().against_cmp(&cmp),
                    )
                } else if value.ty == BOOLEAN && relation.equality() {
                    let truth = value.text.clone();
                    let negation = format!("!{}", value.at(UNARY));
                    if matches!(relation, Relation::Eq) {
                        (negation, truth)
                    } else {
                        (truth, negation)
                    }
                } else {
                    let value = self.as_int(value);
                    let zero = Expr::integer(0);
                    (
                        relation.against(&value, &zero),
                        relation.inverse().against(&value, &zero),
                    )
                }
            }
            0x9f..=0xa4 => {
                let relation = Relation::opcode_index(op.opcode - 0x9f);
                let right = self.pop_category(Category::Int)?;
                let left = self.pop_category(Category::Int)?;
                if relation.equality()
                    && [&left, &right].into_iter().all(|value| {
                        value.ty == BOOLEAN || matches!(value.source, Source::Integer(0 | 1))
                    })
                    && (left.ty == BOOLEAN || right.ty == BOOLEAN)
                {
                    self.relations(
                        relation,
                        &self.boolean_value(left),
                        &self.boolean_value(right),
                    )?
                } else {
                    self.relations(relation, &self.as_int(left), &self.as_int(right))?
                }
            }
            0xa5..=0xa6 | 0xc6..=0xc7 => {
                let equality = matches!(op.opcode, 0xa5 | 0xc6);
                let (left, right) = if op.opcode < 0xc6 {
                    let right = self.pop_category(Category::Ref)?;
                    let mut left = self.pop_category(Category::Ref)?;
                    if !matches!(left.source, Source::Null)
                        && !matches!(right.source, Source::Null)
                        && !self.known_assignable(&left.ty, &right.ty)
                        && !self.known_assignable(&right.ty, &left.ty)
                    {
                        left = self.cast(left, object_type(), false)?;
                    }
                    (left, right)
                } else {
                    (
                        self.pop_category(Category::Ref)?,
                        Expr::atom(object_type(), "null".into()),
                    )
                };
                self.relations(
                    if equality { Relation::Eq } else { Relation::Ne },
                    &left,
                    &right,
                )?
            }
            _ => unreachable!(),
        };
        Ok(Effect::Branch {
            target,
            when_true,
            when_false,
        })
    }

    fn relations(
        &self,
        relation: Relation,
        left: &Expr,
        right: &Expr,
    ) -> Result<(String, String), LiftError> {
        self.order_of([left, right], false)?;
        Ok((
            relation.against(left, right),
            relation.inverse().against(left, right),
        ))
    }

    pub(super) fn array_load(&mut self, kind: u8) -> Result<(), LiftError> {
        let index = self.pop_category(Category::Int)?;
        let index = self.as_int(index);
        let (array, component) = self.array_operand(kind)?;
        let text = format!("{}[{}]", array.at(PRIMARY), index.text);
        self.push(self.expression(component, text, PRIMARY, [&array, &index], true)?)
    }

    pub(super) fn array_store(&mut self, kind: u8) -> Result<Effect, LiftError> {
        let category = if kind <= 4 {
            Category::for_local(kind)
        } else {
            Category::Int
        };
        let value = self.pop_category(category)?;
        let index = self.pop_category(Category::Int)?;
        let index = self.as_int(index);
        let (mut array, component) = self.array_operand(kind)?;
        let value = if kind == 4 {
            if !matches!(value.source, Source::Null)
                && !self.known_assignable(&value.ty, &component)
            {
                // aastore performs the runtime array store check even if the
                // statically known component is narrower than the stack value.
                // A cast on the value would throw ClassCastException instead.
                array = self.cast(array, Type::Array(Box::new(object_type())), false)?;
            }
            value
        } else {
            self.coerce(value, &component, false)?
        };
        let order = self.order_of([&array, &index, &value], true)?;
        self.before_statement(order)?;
        Ok(Effect::Statement(format!(
            "{}[{}] = {};",
            array.at(PRIMARY),
            index.text,
            value.text
        )))
    }

    fn array_operand(&mut self, kind: u8) -> Result<(Expr, Type), LiftError> {
        use Primitive::{Byte, Char, Double, Float, Int, Long, Short};
        let array = self.pop_category(Category::Ref)?;
        let nominal_component = if kind == 4 {
            object_type()
        } else {
            Type::Primitive([Int, Long, Float, Double, Int, Byte, Char, Short][usize::from(kind)])
        };
        if matches!(array.source, Source::Null) {
            let cast = self.cast(
                array,
                Type::Array(Box::new(nominal_component.clone())),
                false,
            )?;
            return Ok((cast, nominal_component));
        }
        let Type::Array(component) = &array.ty else {
            return Err(self.invalid_stack("array opcode requires an array reference"));
        };
        let component = component.as_ref().clone();
        let compatible = if kind == 4 {
            Category::of(&component) == Some(Category::Ref)
        } else {
            nominal_component == component || (kind == 5 && component == BOOLEAN)
        };
        if !compatible {
            return Err(self.invalid_stack("array opcode does not match the component type"));
        }
        Ok((array, component))
    }

    pub(super) fn array_length(&mut self) -> Result<(), LiftError> {
        let mut array = self.pop_category(Category::Ref)?;
        if matches!(array.source, Source::Null) {
            array = self.cast(array, Type::Array(Box::new(object_type())), false)?;
        }
        if !matches!(array.ty, Type::Array(_)) {
            return Err(self.invalid_stack("arraylength requires an array reference"));
        }
        let text = format!("{}.length", array.at(PRIMARY));
        self.push(self.expression(INT, text, PRIMARY, [&array], true)?)
    }

    pub(super) fn array_type(&self, op: &Instruction) -> Result<(Type, u8), LiftError> {
        Ok(match op.opcode {
            0xbc => {
                let Operand::NewArray(atype) = op.operand else {
                    return Err(self.invalid_operand("expected primitive array type"));
                };
                use Primitive::*;
                let primitive = match atype {
                    4 => Boolean,
                    5 => Char,
                    6 => Float,
                    7 => Double,
                    8 => Byte,
                    9 => Short,
                    10 => Int,
                    11 => Long,
                    _ => return Err(self.invalid_operand("unknown primitive array type")),
                };
                (Type::Array(Box::new(Type::Primitive(primitive))), 1)
            }
            0xbd => (
                Type::Array(Box::new(self.class_type(self.constant_index(op)?)?)),
                1,
            ),
            0xc5 => {
                let Operand::MultiANewArray { index, dimensions } = op.operand else {
                    return Err(self.invalid_operand("expected array type and dimensions"));
                };
                (self.class_type(index)?, dimensions)
            }
            _ => unreachable!(),
        })
    }

    pub(super) fn new_array(&mut self, op: &Instruction) -> Result<(), LiftError> {
        let (ty, dimensions) = self.array_type(op)?;
        let mut element = &ty;
        let mut rank = 0usize;
        while let Type::Array(component) = element {
            rank += 1;
            element = component;
        }
        let dimensions = usize::from(dimensions);
        if dimensions == 0 || dimensions > rank || rank > 255 {
            return Err(self.invalid_operand("allocated dimension count exceeds array rank"));
        }
        let mut counts = Vec::with_capacity(dimensions);
        for _ in 0..dimensions {
            let count = self.pop_category(Category::Int)?;
            counts.push(self.as_int(count));
        }
        counts.reverse();
        let mut text = format!("new {}", self.render_type(element));
        for count in &counts {
            let _ = write!(text, "[{}]", count.text);
        }
        for _ in dimensions..rank {
            text.push_str("[]");
        }
        // Parenthesize before [] access: otherwise a subsequent subscript
        // could be parsed as another dimension of the array creation.
        self.push(self.expression(ty, text, UNARY, &counts, true)?)
    }

    pub(super) fn type_test(&mut self, op: &Instruction) -> Result<(), LiftError> {
        let ty = self.class_type(self.constant_index(op)?)?;
        let value = self.pop_category(Category::Ref)?;
        if op.opcode == 0xc0 {
            let annotated = u16::try_from(self.debug_offset(op.offset))
                .ok()
                .map(|offset| {
                    self.render_code_type(
                        &ty,
                        TypeTarget::TypeArgument {
                            kind: TypeArgumentTarget::Cast,
                            offset,
                            argument: 0,
                        },
                    )
                })
                .transpose()?
                .flatten();
            if annotated.is_none() && value.ty == ty && !matches!(value.source, Source::Null) {
                return self.push(value);
            }
            let value = self.reference_cast_with_name(value, ty, true, annotated)?;
            self.push(value)
        } else {
            let value = if !matches!(value.source, Source::Null)
                && !self.known_assignable(&value.ty, &ty)
                && !self.known_assignable(&ty, &value.ty)
            {
                self.cast(value, object_type(), false)?
            } else {
                value
            };
            let name = u16::try_from(self.debug_offset(op.offset))
                .ok()
                .map(|offset| {
                    self.render_code_type(
                        &ty,
                        TypeTarget::Offset {
                            kind: OffsetTarget::InstanceOf,
                            offset,
                        },
                    )
                })
                .transpose()?
                .flatten()
                .unwrap_or_else(|| self.render_type(&ty));
            let text = format!("{} instanceof {}", value.at(RELATIONAL), name);
            self.push(self.expression(BOOLEAN, text, RELATIONAL, [&value], true)?)
        }
    }
}
