// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::ops::RangeInclusive;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{Constant, TypeArgumentTarget, TypeTarget},
    descriptor::{MethodDescriptor, Primitive, Type},
    source_text::Document,
};

use super::{
    LiftError, Machine,
    assignment_expr::LocalWrite,
    expr::{Category, Expr, INT, Source},
};

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
    pub(crate) fn read_pattern_dispatch(
        &mut self,
        op: &Instruction,
    ) -> Result<Option<PatternDispatch>, LiftError> {
        if op.opcode != 0xba || !self.supports_pattern_switch() {
            return Ok(None);
        }
        let Operand::Constant(index) = op.operand else {
            return Ok(None);
        };
        let pool = &self.class.pool;
        let Constant::InvokeDynamic {
            bootstrap_index,
            name_and_type_index,
        } = *pool.get(index)?
        else {
            return Ok(None);
        };
        if self.bootstrap.is_none() {
            self.bootstrap = Some(self.class.bootstrap_methods()?.into());
        }
        let Some(method) = self
            .bootstrap
            .as_ref()
            .and_then(|table| table.get(usize::from(bootstrap_index)))
        else {
            return Ok(None);
        };
        let Constant::MethodHandle {
            reference_kind: 6,
            reference_index,
        } = *pool.get(method.method_ref)?
        else {
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
        let (call_name, descriptor) = pool.name_and_type(name_and_type_index)?;
        if call_name != name {
            return Ok(None);
        }
        let descriptor = MethodDescriptor::parse(descriptor)?;
        let [selector, restart] = descriptor.parameters.as_slice() else {
            return Ok(None);
        };
        if *restart != INT
            || descriptor.return_type != INT
            || Category::of(selector) != Some(Category::Ref)
        {
            return Ok(None);
        }
        if enum_switch {
            let Type::Object(owner) = selector else {
                return Ok(None);
            };
            if !self.pattern_is_enum(owner) {
                return Ok(None);
            }
        }
        let mut labels = Vec::with_capacity(method.arguments.len());
        for &index in &method.arguments {
            let label = match *pool.get(index)? {
                Constant::Class(_) => {
                    let ty = self.class_type(index)?;
                    if (enum_switch && ty != *selector)
                        || !self.pattern_type_compatible(selector, &ty)
                    {
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
                    PatternLabel::Constant(super::string_literal(
                        &pool.utf16(text)?,
                        self.options.ascii_strings,
                    ))
                }
                Constant::Integer(value) => {
                    let Type::Object(name) = selector else {
                        return Ok(None);
                    };
                    let primitive = match name.as_str() {
                        "java/lang/Integer" => Primitive::Int,
                        "java/lang/Byte" if i8::try_from(value).is_ok() => Primitive::Byte,
                        "java/lang/Short" if i16::try_from(value).is_ok() => Primitive::Short,
                        "java/lang/Character" if u16::try_from(value).is_ok() => Primitive::Char,
                        _ => return Ok(None),
                    };
                    PatternLabel::Constant(super::literal::integer_literal(
                        value,
                        Some(&Type::Primitive(primitive)),
                        self.options.ascii_strings,
                    ))
                }
                _ => return Ok(None),
            };
            labels.push(label);
        }
        Ok(Some(PatternDispatch {
            selector: selector.clone(),
            labels,
        }))
    }

    fn pattern_is_enum(&self, owner: &str) -> bool {
        if let Some(class) = self
            .group
            .and_then(|group| group.get(owner))
            .or_else(|| (owner == self.owner).then_some(self.class))
        {
            return class.access_flags & 0x4000 != 0;
        }
        [
            self.options.library_classpath.as_deref(),
            self.options.runtime_classpath.as_deref(),
        ]
        .into_iter()
        .flatten()
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

    fn supports_pattern_switch(&self) -> bool {
        self.class.major_version >= 65
            || (61..=64).contains(&self.class.major_version) && self.class.minor_version == u16::MAX
    }

    pub(crate) fn supports_null_default(&self) -> bool {
        self.class.major_version >= 65
    }

    pub(crate) fn can_project_record_patterns(&self) -> bool {
        // A projected prologue retains no bytecode position for an annotated
        // backing cast. Leave it to the ordinary handler layer for now.
        self.supports_null_default() && self.normalized.is_none() && self.code_type_renderer.is_none()
    }

    pub(crate) fn pattern_record_components<'c>(
        &'c self,
        ty: &Type,
    ) -> Option<Vec<(&'c str, Type)>> {
        let Type::Object(name) = ty else { return None };
        let class = self.group.and_then(|group| group.get(name))
            .or_else(|| (name == self.owner).then_some(self.class))?;
        let pool = &class.pool;
        if class.access_flags & 0x0010 == 0
            || pool.class_name(class.super_class).ok()? != "java/lang/Record"
            || class.signature().ok()?.is_some_and(|sig| sig.starts_with('<'))
        {
            return None;
        }
        class.record_components().ok()??.into_iter().map(|component| {
            if component.signature(pool).ok()?.is_some() {
                return None;
            }
            let name = pool.utf8(component.name_index).ok()?;
            let desc = pool.utf8(component.descriptor_index).ok()?;
            class.methods.iter().find(|method| {
                method.access_flags & (0x0001 | 0x0008) == 0x0001
                    && pool.utf8(method.name_index).ok() == Some(name)
                    && pool.utf8(method.descriptor_index).ok().and_then(|s| s.strip_prefix("()")) == Some(desc)
            })?;
            Some((name, Type::parse(desc).ok()?))
        }).collect()
    }

    pub(crate) fn pattern_record_type(&self, ty: &Type) -> String {
        self.render_type(ty)
    }

    pub(crate) fn pattern_raw_parameter_slots(&self) -> u16 {
        u16::from(self.method.access_flags & 0x0008 == 0)
            + self.descriptor.parameters.iter().map(Type::slots).sum::<u16>()
    }

    pub(crate) fn pattern_guard_keyword(&self) -> Option<&'static str> {
        self.supports_pattern_switch().then_some(if self.class.major_version <= 62 { " && " } else { " when " })
    }

    pub(crate) fn pattern_guard_switch_type(&self, instruction: &Instruction) -> Option<Type> {
        if !matches!(instruction.operand, Operand::Switch { .. }) {
            return None;
        }
        let Type::Primitive(ty @ (Primitive::Byte | Primitive::Short | Primitive::Char | Primitive::Int)) = &self.stack.last()?.ty
        else { return None };
        Some(Type::Primitive(*ty))
    }

    pub(crate) fn pattern_guard_case(&self, key: i32, ty: &Type) -> Option<String> {
        match ty {
            Type::Primitive(Primitive::Int) => {}
            Type::Primitive(Primitive::Byte) if i8::try_from(key).is_ok() => {}
            Type::Primitive(Primitive::Short) if i16::try_from(key).is_ok() => {}
            Type::Primitive(Primitive::Char) if u16::try_from(key).is_ok() => {}
            _ => return None,
        }
        Some(super::literal::integer_literal(key, Some(ty), self.options.ascii_strings))
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
        end: u32,
    ) -> Result<(Document, RangeInclusive<u32>), LiftError> {
        self.offset = op.offset;
        self.opcode = op.opcode;
        self.lower_pending_comparison()?;
        let value = self.pop_category(Category::Ref)?;
        let control = value.order.map_or(op.offset, |order| order.first)..=end;
        if !has_type_labels {
            let text = if matches!(value.source, Source::Null) {
                self.cast(value, selector.clone(), false)?.text
            } else {
                self.coerce(value, selector, false)?.text
            };
            return Ok((text, control));
        }
        // For pattern labels, use the descriptor type, rather than a narrower
        // local type that could make a legal case unconditional or disjoint.
        let text = if value.ty != *selector || matches!(value.source, Source::Null) {
            self.reference_cast(value, selector.clone(), false)?.text
        } else {
            value.text
        };
        Ok((text, control))
    }

    pub(crate) fn pattern_binding(
        &mut self,
        ty: &Type,
        store: Option<(&Instruction, Option<&Instruction>, u16)>,
        offset: u32,
    ) -> Result<Document, LiftError> {
        if let Some((store, cast, slot)) = store {
            self.offset = store.offset;
            self.opcode = store.opcode;
            if let Some(cast) = cast
                && let Ok(offset) = u16::try_from(self.debug_offset(cast.offset))
                && self.render_code_type(ty, TypeTarget::TypeArgument {
                    kind: TypeArgumentTarget::Cast, offset, argument: 0,
                })?.is_some()
            {
                return Err(self.unsupported("annotated pattern backing cast"));
            }
            let category = Category::of(ty).ok_or_else(|| self.unsupported("invalid pattern binding type"))?;
            let target = LocalWrite { index: slot, category };
            let value = Expr::atom(ty.clone(), Document::new());
            if self.assignment_local_destination(store, target, &value) != Some(true) {
                return Err(self.unsupported("pattern store does not declare a fresh local of the tested type"));
            }
            let (_, declaration) = self.commit_assignment_local(store, target, ty, true);
            let mut declaration = declaration.expect("a fresh local has a declaration");
            declaration.pop();
            Ok(declaration)
        } else {
            Ok(format!("{} {}", self.render_type(ty), self.locals.temporary(offset)).into())
        }
    }
}
