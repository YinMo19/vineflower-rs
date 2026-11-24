// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::fmt::Write;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{OffsetTarget, TypeArgumentTarget, TypeTarget},
    descriptor::{Primitive, Type},
    source_text::{Document, Infix},
};

use super::{
    Effect, LiftError, Machine,
    assignment_expr::{Access, AddressPart, Binary},
    expr::{
        BOOLEAN, Category, Comparison, Expr, INT, PRIMARY, RELATIONAL, Relation, Source, TERNARY, UNARY,
    },
    object_type,
};

impl Machine<'_, '_> {
    pub(super) fn arithmetic(&mut self, opcode: u8) -> Result<(), LiftError> {
        if (0x74..=0x77).contains(&opcode) {
            let category = Category::for_local(opcode - 0x74);
            let value = self.pop_category(category)?;
            let value = self.as_int(self.implicit_unboxing(value));
            // At equal precedence a unary minus can become a prefix -- token.
            let mut text = Document::from("-");
            value.append_at(UNARY + 1, &mut text);
            return self.push(self.expression(
                category.numeric_type(),
                text,
                UNARY,
                [&value],
                false,
            )?);
        }
        let Binary { left: category, right: right_category, operator, precedence, can_throw } =
            Binary::of(opcode).expect("binary arithmetic opcode");
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
        let left = self.implicit_unboxing(left);
        let right = self.implicit_unboxing(right);
        // Integral arithmetic at the same width is associative modulo that
        // width; do not regroup a narrower computation or a floating one.
        let reassociate = boolean
            || (matches!(category, Category::Int | Category::Long)
                && right.ty == ty
                && matches!(operator, "+" | "*" | "&" | "|" | "^"));
        let text = left.binary(Infix::new(operator, precedence), &right, reassociate);
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
        let value = self.as_int(value);
        let Type::Primitive(operand_type) = value.ty else {
            return Err(self.invalid_stack("numeric conversion requires a primitive operand"));
        };
        let operand_precedence = value.precedence;
        let mut converted = self.cast(value, Type::Primitive(to), false)?;
        if matches!(index, 0..=2 | 4..=5 | 8) {
            converted.source = Source::WidenedPrimitive { operand_type, operand_precedence };
        }
        self.push(converted)
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
        // The eventual consumer can compare for equality, so retain one
        // explicit accessor if both source operands are wrappers.
        let (left, right) = self.unbox_comparison(left, right, true);
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
            ..Expr::atom(INT, Document::new())
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
        let mut text = relation.against(&left, &right);
        let _ = write!(text, " ? {} : ", -fallback);
        text.append(Relation::Eq.against(&left, &right));
        let _ = write!(text, " ? 0 : {fallback}");
        self.push(self.expression(INT, text, TERNARY, [&left, &right], false)?)
    }

    pub(super) fn conditional(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        let target = self.target(op)?;
        self.boolean_condition = super::BooleanCondition::comparison();
        let (when_true, when_false) = match op.opcode {
            0x99..=0x9e => {
                let relation = Relation::opcode_index(op.opcode - 0x99);
                let value = self.pop_category(Category::Int)?;
                let value = self.implicit_unboxing(value);
                if let Source::Comparison(cmp) = value.source {
                    self.boolean_condition = super::BooleanCondition::UNKNOWN;
                    (
                        relation.against_cmp(&cmp),
                        relation.inverse().against_cmp(&cmp),
                    )
                } else if value.ty == BOOLEAN && relation.equality() {
                    self.boolean_condition = super::BooleanCondition::tested(
                        &value,
                        matches!(relation, Relation::Ne),
                    );
                    let mut negation = Document::from("!");
                    value.append_at(UNARY, &mut negation);
                    let local_load = match value.source {
                        Source::Local(_) if !value.observable => value
                            .deferred_operand_origin()
                            .map(|origin| origin.bytes())
                            .filter(|bytes| bytes.end == op.offset),
                        _ => None,
                    };
                    let mut truth = value.text;
                    if let Some(load) = local_load {
                        let branch = op.offset..op.offset + op.len;
                        truth.defer_local_predicate(load.clone(), branch.clone());
                        negation.defer_local_predicate(load, branch);
                    }
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
                    let (left, right) = self.unbox_comparison(
                        self.boolean_value(left),
                        self.boolean_value(right),
                        true,
                    );
                    self.relations(relation, &left, &right)?
                } else {
                    let (left, right) = self.unbox_comparison(
                        self.as_int(left),
                        self.as_int(right),
                        relation.equality(),
                    );
                    self.relations(relation, &left, &right)?
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
    ) -> Result<(Document, Document), LiftError> {
        self.order_of([left, right], false)?;
        Ok((
            relation.against(left, right),
            relation.inverse().against(left, right),
        ))
    }

    pub(super) fn array_load(&mut self, kind: u8) -> Result<(), LiftError> {
        let index = self.pop_category(Category::Int)?;
        let address_index = AddressPart::index(&index);
        let index = self.as_int(self.implicit_unboxing(index));
        let (array, component) = self.array_operand(kind)?;
        let mut text = Document::new();
        array.append_at(PRIMARY, &mut text);
        text.push('[');
        text.append_ref(&index.text);
        text.push(']');
        let address_array = AddressPart::receiver(&array);
        let mut value = self.expression(component, text, PRIMARY, [&array, &index], true)?;
        if let (Some(array), Some(index)) = (address_array, address_index) {
            value.source = Source::Access(Access::Array { store: 0x4f + kind, array, index });
        }
        self.push(value)
    }

    pub(super) fn array_store(&mut self, kind: u8) -> Result<Effect, LiftError> {
        let category = if kind <= 4 {
            Category::for_local(kind)
        } else {
            Category::Int
        };
        let value = self.pop_category(category)?;
        let index = self.pop_category(Category::Int)?;
        let index = self.as_int(self.implicit_unboxing(index));
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
            self.coerce_assignment(value, &component)?
        };
        let order = self.order_of([&array, &index, &value], true)?;
        self.before_statement(order)?;
        let mut text = array.into_at(PRIMARY);
        text.push('[');
        text.append(index.text);
        text.push_str("] = ");
        text.append(value.text);
        text.push(';');
        Ok(Effect::Statement(text))
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
        let mut text = Document::new();
        array.append_at(PRIMARY, &mut text);
        text.push_str(".length");
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
            counts.push(self.as_int(self.implicit_unboxing(count)));
        }
        counts.reverse();
        let mut text = Document::from("new ");
        text.append(self.type_document(element));
        for count in &counts {
            text.push('[');
            text.append_ref(&count.text);
            text.push(']');
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
                .unwrap_or_else(|| self.type_document(&ty));
            let mut text = Document::new();
            value.append_at(RELATIONAL, &mut text);
            text.push_str(" instanceof ");
            text.append(name);
            self.push(self.expression(BOOLEAN, text, RELATIONAL, [&value], true)?)
        }
    }
}
