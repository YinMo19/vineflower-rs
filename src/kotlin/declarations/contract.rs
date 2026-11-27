//! Kotlin contract effects and their conditional predicates.

use super::{KParameter, KType};
use crate::engine::{Cx, import_collector::get_short_name};
use crate::kotlin::{
    identifier,
    metadata::{NameResolver, flags, proto},
};
use crate::util::text_buffer::TextBuffer;
use arcstr::ArcStr;
use proto::{
    effect::{EffectType, InvocationKind},
    expression::ConstantValue,
};
use std::{borrow::Cow, io};

#[derive(Clone, Debug)]
pub struct KContract {
    effects: Vec<Effect>,
}

#[derive(Clone, Debug)]
struct Effect {
    kind: Option<EffectType>,
    arguments: Vec<Predicate>,
    conclusion: Option<Predicate>,
    invocation: Option<InvocationKind>,
}

#[derive(Clone, Debug)]
struct Predicate {
    flags: i32,
    parameter: Option<ParameterRef>,
    constant: Option<ConstantValue>,
    instance_type: Option<KType>,
    and: Vec<Predicate>,
    or: Vec<Predicate>,
}

/// The receiver is metadata index zero. The plugin treats its type as Nothing.
#[derive(Clone, Debug)]
enum ParameterRef {
    Receiver,
    Value {
        name: ArcStr,
        nullable: bool,
        boolean: bool,
    },
}

impl ParameterRef {
    fn raw_name(&self) -> &str {
        match self {
            Self::Receiver => "this",
            Self::Value { name, .. } => name,
        }
    }
    fn source_name(&self) -> Cow<'_, str> {
        match self {
            Self::Receiver => Cow::Borrowed("this"),
            Self::Value { name, .. } => identifier(name),
        }
    }
}

impl KContract {
    pub fn from_proto(
        proto: &proto::Contract,
        params: &[KParameter],
        names: &NameResolver,
        table: &proto::TypeTable,
    ) -> io::Result<Self> {
        let predicate =
            |expr: &proto::Expression| Predicate::from_proto(expr, params, names, table);
        let effects = proto
            .effect
            .iter()
            .map(|effect| {
                Ok(Effect {
                    kind: effect
                        .effect_type
                        .and_then(|n| EffectType::try_from(n).ok()),
                    arguments: effect
                        .effect_constructor_argument
                        .iter()
                        .map(predicate)
                        .collect::<io::Result<_>>()?,
                    conclusion: effect
                        .conclusion_of_conditional_effect
                        .as_ref()
                        .map(predicate)
                        .transpose()?,
                    invocation: effect.kind.and_then(|n| InvocationKind::try_from(n).ok()),
                })
            })
            .collect::<io::Result<_>>()?;
        Ok(Self { effects })
    }

    pub fn write(&self, cx: &mut Cx, buffer: &mut TextBuffer, indent: i32) -> io::Result<()> {
        buffer
            .append_indent(indent)
            .append("contract {")
            .append_line_separator();
        for effect in &self.effects {
            effect.write(cx, buffer, indent + 1)?;
        }
        buffer
            .append_indent(indent)
            .append_char('}')
            .append_line_separator();
        Ok(())
    }
}

impl Effect {
    fn write(&self, cx: &mut Cx, buf: &mut TextBuffer, indent: i32) -> io::Result<()> {
        let Some(kind) = self.kind else { return Ok(()) };
        buf.append_indent(indent);
        match kind {
            EffectType::ReturnsNotNull => {
                buf.append("returnsNotNull()");
            }
            EffectType::ReturnsConstant => {
                buf.append("returns(");
                if let Some(first) = self.arguments.first() {
                    first.write(cx, buf, indent, false)?;
                }
                buf.append_char(')');
            }
            EffectType::Calls => {
                let parameter = self
                    .arguments
                    .first()
                    .and_then(|arg| arg.parameter.as_ref())
                    .ok_or_else(|| {
                        io::Error::other(
                            "Kotlin callsInPlace effect is missing its function parameter",
                        )
                    })?;
                buf.append("callsInPlace(")
                    .append(&identifier(parameter.raw_name()));
                if let Some(invocation) = self.invocation {
                    buf.append(", ")
                        .append(&get_short_name(cx, "kotlin.contracts.InvocationKind"))
                        .append_char('.')
                        .append(invocation.as_str_name());
                }
                buf.append_char(')');
            }
        }
        if kind != EffectType::Calls
            && let Some(predicate) = &self.conclusion
        {
            buf.append(" implies (");
            predicate.write(cx, buf, indent, false)?;
            buf.append_char(')');
        }
        buf.append_line_separator();
        Ok(())
    }
}

impl Predicate {
    fn from_proto(
        proto: &proto::Expression,
        params: &[KParameter],
        names: &NameResolver,
        table: &proto::TypeTable,
    ) -> io::Result<Self> {
        let parameter = proto
            .value_parameter_reference
            .map(|index| -> io::Result<ParameterRef> {
                if index == 0 {
                    return Ok(ParameterRef::Receiver);
                }
                let param = index
                    .checked_sub(1)
                    .and_then(|i| params.get(i as usize))
                    .ok_or_else(|| {
                        io::Error::other(format!("Missing Kotlin contract parameter {index}"))
                    })?;
                Ok(ParameterRef::Value {
                    name: param.name.clone(),
                    nullable: param.ty.nullable,
                    boolean: param.ty.classifier == "kotlin/Boolean",
                })
            })
            .transpose()?;
        let instance_type = if let Some(ty) = &proto.is_instance_type {
            Some(KType::from_proto(Some(ty), names)?)
        } else {
            proto
                .is_instance_type_id
                .map(|index| KType::from_table(index, table, names))
                .transpose()?
        };
        let children = |items: &[proto::Expression]| {
            items
                .iter()
                .map(|item| Self::from_proto(item, params, names, table))
                .collect::<io::Result<_>>()
        };
        Ok(Self {
            flags: proto.flags(),
            parameter,
            constant: proto
                .constant_value
                .and_then(|v| ConstantValue::try_from(v).ok()),
            instance_type,
            and: children(&proto.and_argument)?,
            or: children(&proto.or_argument)?,
        })
    }

    fn write(
        &self,
        cx: &mut Cx,
        buf: &mut TextBuffer,
        indent: i32,
        part_of_or: bool,
    ) -> io::Result<()> {
        if !self.and.is_empty() && (!self.or.is_empty() || part_of_or) {
            buf.append_char('(');
        }
        let name = self
            .parameter
            .as_ref()
            .map_or(Cow::Borrowed("null"), ParameterRef::source_name);
        let negated = flags::IS_NEGATED.get(self.flags);
        let equality = if negated { " != " } else { " == " };
        let mut appended = true;
        if let Some(ty) = &self.instance_type {
            buf.append(&name)
                .append(if negated { " !is " } else { " is " });
            ty.write(cx, buf, indent)?;
        } else if flags::IS_NULL_CHECK_PREDICATE.get(self.flags) {
            buf.append(&name).append(equality).append("null");
        } else if let Some(value) = self.constant {
            let literal = match value {
                ConstantValue::True => "true",
                ConstantValue::False => "false",
                ConstantValue::Null => "null",
            };
            if matches!(
                self.parameter,
                Some(ParameterRef::Value { nullable: true, .. })
            ) {
                buf.append(&name).append(equality).append(literal);
            } else {
                if negated {
                    buf.append_char('!');
                }
                let boolean = matches!(
                    self.parameter,
                    Some(ParameterRef::Value { boolean: true, .. })
                );
                buf.append(if boolean { &name } else { literal });
            }
        } else if self.parameter.is_some() {
            if negated {
                buf.append_char('!');
            }
            buf.append(&name);
        } else {
            appended = false;
        }
        for child in &self.and {
            if appended {
                buf.append(" && ");
            }
            child.write(cx, buf, indent, false)?;
            appended = true;
        }
        if !self.or.is_empty() && (!self.and.is_empty() || part_of_or) {
            buf.append_char(')');
        }
        for child in &self.or {
            if appended {
                buf.append(" || ");
            }
            child.write(cx, buf, indent, true)?;
            appended = true;
        }
        Ok(())
    }
}
