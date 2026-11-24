// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::HashSet;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::Constant,
    descriptor::{MethodDescriptor, Primitive, Type},
    source_text::Document,
};

use super::{Effect, LiftError, Machine, expr::{Category, Expr, INT, Source}};

const BOOTSTRAP_DESCRIPTOR: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";

pub(crate) struct PatternDispatch {
    pub(crate) selector: Type,
    pub(crate) labels: Vec<PatternLabel>,
}

#[derive(Eq, Hash, PartialEq)]
pub(crate) enum PatternLabel {
    Type(Type),
    Constant(String),
}

impl Machine<'_, '_> {
    pub(crate) fn read_pattern_dispatch(&mut self, op: &Instruction) -> Result<Option<PatternDispatch>, LiftError> {
        if op.opcode != 0xba {
            return Ok(None);
        }
        let Operand::Constant(index) = op.operand else { return Ok(None); };
        let pool = &self.class.pool;
        let Constant::InvokeDynamic { bootstrap_index, name_and_type_index } = *pool.get(index)? else {
            return Ok(None);
        };
        if self.bootstrap.is_none() {
            self.bootstrap = Some(self.class.bootstrap_methods()?.into());
        }
        let Some(method) = self.bootstrap.as_ref().and_then(|table| table.get(usize::from(bootstrap_index))) else {
            return Ok(None);
        };
        let Constant::MethodHandle { reference_kind: 6, reference_index } = *pool.get(method.method_ref)? else {
            return Ok(None);
        };
        if !matches!(pool.get(reference_index)?, Constant::Methodref { .. }) {
            return Ok(None);
        }
        let (owner, name, signature) = pool.member_ref(reference_index)?;
        if owner != "java/lang/runtime/SwitchBootstraps" || signature != BOOTSTRAP_DESCRIPTOR {
            return Ok(None);
        }
        let enum_switch = match name {
            "typeSwitch" => false,
            "enumSwitch" => true,
            _ => return Ok(None),
        };
        let (_, descriptor) = pool.name_and_type(name_and_type_index)?;
        let descriptor = MethodDescriptor::parse(descriptor)?;
        let [selector, restart] = descriptor.parameters.as_slice() else { return Ok(None); };
        if *restart != INT || descriptor.return_type != INT || Category::of(selector) != Some(Category::Ref) {
            return Ok(None);
        }
        if enum_switch {
            let Type::Object(owner) = selector else { return Ok(None); };
            if !self.pattern_is_enum(owner) {
                return Ok(None);
            }
        }
        let mut labels = Vec::with_capacity(method.arguments.len());
        for &index in &method.arguments {
            let label = match *pool.get(index)? {
                Constant::Class(_) => {
                    let ty = self.class_type(index)?;
                    if (enum_switch && ty != *selector) || !self.pattern_type_compatible(selector, &ty) {
                        return Ok(None);
                    }
                    PatternLabel::Type(ty)
                }
                Constant::String(name) if enum_switch => {
                    let name = pool.utf8(name)?;
                    if !crate::naming::is_valid_local_identifier(name, self.class.major_version) {
                        return Ok(None);
                    }
                    PatternLabel::Constant(name.into())
                }
                Constant::String(text) if matches!(selector, Type::Object(name) if name == "java/lang/String") => {
                    PatternLabel::Constant(super::string_literal(&pool.utf16(text)?, self.options.ascii_strings))
                }
                Constant::Integer(value) => {
                    let Type::Object(name) = selector else { return Ok(None); };
                    let primitive = match name.as_str() {
                        "java/lang/Integer" => Primitive::Int,
                        "java/lang/Byte" if i8::try_from(value).is_ok() => Primitive::Byte,
                        "java/lang/Short" if i16::try_from(value).is_ok() => Primitive::Short,
                        "java/lang/Character" if u16::try_from(value).is_ok() => Primitive::Char,
                        _ => return Ok(None),
                    };
                    PatternLabel::Constant(super::literal::integer_literal(value, Some(&Type::Primitive(primitive)), self.options.ascii_strings))
                }
                _ => return Ok(None),
            };
            labels.push(label);
        }
        if labels.iter().collect::<HashSet<_>>().len() != labels.len() {
            // Repeated labels normally need guards and a restart edge.
            return Ok(None);
        }
        Ok(Some(PatternDispatch { selector: selector.clone(), labels }))
    }

    fn pattern_is_enum(&self, owner: &str) -> bool {
        if let Some(class) = self.group.and_then(|group| group.get(owner)).or_else(|| (owner == self.owner).then_some(self.class)) {
            return class.access_flags & 0x4000 != 0;
        }
        [self.options.library_classpath.as_deref(), self.options.runtime_classpath.as_deref()]
            .into_iter().flatten()
            .find_map(|path| path.metadata(owner).ok().flatten())
            .is_some_and(|class| class.access_flags & 0x4000 != 0)
    }

    fn pattern_type_compatible(&self, selector: &Type, pattern: &Type) -> bool {
        self.known_assignable(pattern, selector)
            || self.known_assignable(selector, pattern)
            || matches!((selector, pattern), (Type::Object(a), Type::Object(b))
                if self.group.is_some_and(|group| group.get(a).is_some_and(|c| c.access_flags & 0x0200 != 0)
                    && group.get(b).is_some_and(|c| c.access_flags & 0x0200 != 0)))
    }

    pub(crate) fn pattern_class(&self, index: u16) -> Result<Type, LiftError> {
        self.class_type(index)
    }

    pub(crate) fn pattern_covers(&self, prior: &Type, later: &Type) -> bool {
        self.known_assignable(later, prior)
    }

    pub(crate) fn take_pattern_selector(
        &mut self,
        op: &Instruction,
        selector: &Type,
        has_type_labels: bool,
        null_check: bool,
    ) -> Result<Document, LiftError> {
        let mut value = self.take_region_reference(op)?;
        if !has_type_labels {
            // A traditional enum/String/integral switch has its own null
            // check. A default-only reference switch needs an explicit one.
            let traditional = matches!(selector, Type::Object(name) if matches!(name.as_str(),
                "java/lang/String" | "java/lang/Integer" | "java/lang/Byte" | "java/lang/Short" | "java/lang/Character")
                || self.pattern_is_enum(name));
            if null_check && !traditional {
                let objects = (self.class_name)("java/util/Objects");
                value.text.surround(&format!("{objects}.requireNonNull("), ")");
                return Ok(value.text);
            }
            return Ok(if matches!(value.source, Source::Null) {
                self.cast(value, selector.clone(), false)?.text
            } else {
                self.coerce(value, selector, false)?.text
            });
        }
        // For pattern labels, use the descriptor type, rather than a narrower
        // local type that could make a legal case unconditional or disjoint.
        Ok(if value.ty != *selector || matches!(value.source, Source::Null) {
            self.reference_cast(value, selector.clone(), false)?.text
        } else {
            value.text
        })
    }

    pub(crate) fn pattern_binding(&mut self, ty: &Type, store: Option<(&Instruction, u16)>, offset: u32) -> Result<String, LiftError> {
        let display = self.render_type(ty);
        let name = if let Some((store, slot)) = store {
            self.offset = store.offset;
            self.opcode = store.opcode;
            // Reuse the ordinary local binding rules without evaluating any
            // cast: selection has already established the pattern type.
            const PLACEHOLDER: &str = "$pattern";
            self.push(Expr::atom(ty.clone(), PLACEHOLDER.into()))?;
            let Effect::Statement(declaration) = self.store(store, slot, Category::Ref)? else {
                return Err(self.invalid_operand("invalid pattern binding store"));
            };
            declaration.strip_prefix(&display)
                .and_then(|rest| rest.strip_prefix(' '))
                .and_then(|rest| rest.strip_suffix(" = $pattern;"))
                .filter(|name| crate::naming::is_valid_local_identifier(name, self.class.major_version))
                .ok_or_else(|| self.unsupported("pattern store does not declare a fresh local of the tested type"))?
                .to_owned()
        } else {
            self.locals.temporary(offset)
        };
        Ok(format!("{display} {name}"))
    }
}
