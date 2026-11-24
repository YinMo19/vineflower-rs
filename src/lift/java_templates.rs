// Copyright 2000-2023 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use crate::{bytecode::Instruction, classfile::Constant, descriptor::{MethodDescriptor, Type}};

use super::{Effect, LiftError, Machine, expr::{Expr, PRIMARY, Source}, literal::write_string_contents};

pub(super) const RUNTIME: &str = "java/lang/runtime/TemplateRuntime";
const STRING_TEMPLATE: &str = "java/lang/StringTemplate";
const FMT_FIELD: (&str, &str, &str) = ("java/util/FormatProcessor", "FMT", "Ljava/util/FormatProcessor;");
const NEW: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/String;)Ljava/lang/invoke/CallSite;";
const PROCESS: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;[Ljava/lang/String;)Ljava/lang/invoke/CallSite;";

impl Machine<'_, '_> {
    pub(super) fn lower_string_template(
        &mut self,
        op: &Instruction,
        bootstrap_index: u16,
        bootstrap_ref: u16,
        bootstrap: (&str, &str),
        site: (&str, &str),
    ) -> Result<Effect, LiftError> {
        if (self.class.major_version, self.class.minor_version) != (65, u16::MAX) {
            return Err(self.unsupported("string templates require Java 21 preview"));
        }
        let class = self.class;
        let pool = &class.pool;
        if !matches!(pool.get(bootstrap_ref)?, Constant::Methodref { .. }) || site.0 != "process" {
            return Err(self.invalid_operand("invalid string template bootstrap or call-site name"));
        }
        let bootstraps = self.bootstrap.clone().expect("loaded bootstrap methods");
        let arguments = &bootstraps[usize::from(bootstrap_index)].arguments;
        let descriptor = MethodDescriptor::parse(site.1)?;
        let (has_processor, fragments) = match bootstrap {
            ("newStringTemplate", NEW) if object_is(&descriptor.return_type, STRING_TEMPLATE) => {
                (false, arguments.as_slice())
            }
            ("processStringTemplate", PROCESS)
                if object_is(&descriptor.return_type, "java/lang/String")
                    && descriptor.parameters.first().is_some_and(|ty| object_is(ty, FMT_FIELD.0)) =>
            {
                let (&getter, fragments) = arguments.split_first().ok_or_else(|| {
                    self.invalid_operand("missing string template processor getter")
                })?;
                let Constant::MethodHandle { reference_kind: 2, reference_index } = *pool.get(getter)? else {
                    return Err(self.unsupported("unrecognized string template processor getter"));
                };
                if !matches!(pool.get(reference_index)?, Constant::Fieldref { .. })
                    || pool.member_ref(reference_index)? != FMT_FIELD
                {
                    return Err(self.unsupported("unrecognized string template processor getter"));
                }
                (true, fragments)
            }
            _ => return Err(self.unsupported("unrecognized string template bootstrap or descriptor")),
        };
        let insertions = &descriptor.parameters[usize::from(has_processor)..];
        // javac switches to its array-based template lowering above this limit.
        if insertions.iter().map(|ty| usize::from(ty.slots())).sum::<usize>() > 200
            || fragments.len() != insertions.len() + 1
        {
            return Err(self.invalid_operand("string template fragments do not match the call-site arguments"));
        }

        let args = self.arguments(&descriptor, None)?;
        if has_processor {
            self.prove_format_processor(&args[0])?;
        }
        let mut value = self.expression(descriptor.return_type, Default::default(), PRIMARY, &args, true)?;
        let mut values = args.into_iter();
        let mut text = if has_processor {
            values.next().expect("verified processor parameter").text
        } else {
            let mut raw = self.class_reference(STRING_TEMPLATE);
            raw.push('.');
            self.append_field_reference(
                &mut raw, "RAW", STRING_TEMPLATE, "RAW", "Ljava/lang/StringTemplate$Processor;",
            );
            raw
        };
        if self.options.include_line_mappings && self.normalized.is_none() {
            text.anchor(op.offset..op.offset + op.len);
        }
        text.push_str(".\"");
        for &fragment in fragments {
            let Constant::String(utf8) = *pool.get(fragment)? else {
                return Err(self.invalid_operand("string template fragment is not a String"));
            };
            write_string_contents(&pool.utf16(utf8)?, self.options.ascii_strings, &mut text);
            if let Some(value) = values.next() {
                text.push_str("\\{");
                text.append(value.text);
                text.push('}');
            }
        }
        text.push('"');
        value.text = text;
        self.push(value)?;
        Ok(Effect::None)
    }

    fn prove_format_processor(&self, value: &Expr) -> Result<(), LiftError> {
        // The linked target ignores its first argument, but the bytecode still
        // evaluates it before the insertions. Only fold the direct field read,
        // not a spill or another expression evaluated for its side effects.
        let invalid = || self.unsupported("linked string template processor is not a direct FMT field read");
        let order = value.order.filter(|order| order.first == order.last).ok_or_else(invalid)?;
        if self.normalized.is_some() || value.precedence != PRIMARY || !matches!(value.source, Source::Plain) {
            return Err(invalid());
        }
        let Some([0xb2, high, low, ..]) = self.code.bytes.get(order.first as usize..) else {
            return Err(invalid());
        };
        let index = u16::from_be_bytes([*high, *low]);
        let pool = &self.class.pool;
        if !matches!(pool.get(index)?, Constant::Fieldref { .. }) || pool.member_ref(index)? != FMT_FIELD {
            return Err(invalid());
        }
        Ok(())
    }
}

fn object_is(ty: &Type, expected: &str) -> bool {
    matches!(ty, Type::Object(name) if name == expected)
}
