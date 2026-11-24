// Based on Vineflower ClassWriter (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{mem, rc::Rc};

use crate::{
    classfile::{Constant, Member, RecordComponent, find_attribute},
    context::{NestedClass, NestedKind},
    lift::DynamicHelper,
};

use super::initializers::FieldInitializers;
use super::type_annotations::TypeNesting;
use super::{DecompileError, Enumeration, INTERFACE, PUBLIC, STATIC, SYNTHETIC, SourceMap, Writer};

#[path = "local.rs"]
mod local;

impl<'a, 'c> Writer<'a, 'c> {
    pub(super) fn has_lexical_owner(&self) -> bool {
        self.depth != 0 && self.options.decompile_inner && self.group.is_attached(self.owner)
    }

    pub(super) fn member_classes(&mut self, mut needs_gap: bool) -> Result<(), DecompileError> {
        if !self.options.decompile_inner {
            return Ok(());
        }
        for (name, node) in self.group.children(self.owner) {
            let Some(member) = self.group.member_class(name) else {
                continue;
            };
            let auxiliary = matches!(node.kind, NestedKind::Anonymous)
                .then(|| self.group.enum_switches().auxiliary_visibility(name))
                .flatten();
            let class = self.group.get(name).expect("source member is registered");
            if !self.matches_member_class(name)
                || auxiliary.unwrap_or(
                    self.options.method_to_decompile.is_empty()
                        && self.options.remove_synthetic
                        && ((class.access_flags | node.access_flags) & SYNTHETIC != 0
                            || find_attribute(&class.attributes, &class.pool, "Synthetic")?
                                .is_some()),
                )
            {
                continue;
            }
            if needs_gap {
                self.line(0, "");
            }
            self.write_nested(name, node, member.simple_name, self.depth + 1)?;
            needs_gap = true;
        }
        Ok(())
    }

    fn write_nested(
        &mut self,
        name: &str,
        node: &NestedClass,
        simple: &str,
        depth: usize,
    ) -> Result<(), DecompileError> {
        let simple = self
            .names
            .renames()
            .simple_class_alias(name)
            .unwrap_or(simple);
        self.with_nested(name, node, depth, |writer| writer.class(simple))
    }

    pub(super) fn with_nested(
        &mut self,
        name: &str,
        node: &NestedClass,
        depth: usize,
        write: impl FnOnce(&mut Self) -> Result<(), DecompileError>,
    ) -> Result<(), DecompileError> {
        if depth > 128 {
            return Err(DecompileError::Unsupported {
                feature: "excessive class nesting",
            });
        }
        let class = self
            .group
            .get(name)
            .expect("nested source class is registered");
        let name = class.pool.class_name(class.this_class)?;
        let type_nesting = Rc::new(TypeNesting::new(class)?);
        let member = self.group.member_class(name);
        let mut flags = member
            .as_ref()
            .map_or(node.access_flags, |member| member.access_flags);
        if member.is_some() && self.flags & INTERFACE != 0 {
            // A type declared in an interface is implicitly public and static.
            flags &= !(PUBLIC | STATIC);
        } else if matches!(node.kind, NestedKind::Local(_)) {
            flags &= !(super::VISIBILITY | STATIC);
        }
        let previous_class = mem::replace(&mut self.class, class);
        let previous_owner = mem::replace(&mut self.owner, name);
        let previous_flags = mem::replace(&mut self.flags, flags);
        let previous_depth = mem::replace(&mut self.depth, depth);
        let previous_nesting = mem::replace(&mut self.type_nesting, type_nesting);
        let previous_helpers = mem::take(&mut self.dynamic_helpers);
        let result = write(self);
        self.class = previous_class;
        self.owner = previous_owner;
        self.flags = previous_flags;
        self.depth = previous_depth;
        self.type_nesting = previous_nesting;
        self.dynamic_helpers = previous_helpers;
        result
    }

    pub(super) fn write_methods(
        &mut self,
        name: &str,
        components: Option<&[RecordComponent<'a>]>,
        enumeration: Option<&Enumeration<'_>>,
        constructors: usize,
        needs_gap: &mut bool,
        initializers: &FieldInitializers<'_>,
    ) -> Result<(), DecompileError> {
        let class = self.class;
        let pool = &class.pool;
        let explicitly_selected = !self.options.method_to_decompile.is_empty()
            && !self.group.nested_class(self.owner).is_some_and(|node| {
                matches!(node.kind, NestedKind::Anonymous | NestedKind::Local(_))
            });
        // Lambda recovery marks any synthetic methods still referenced by its
        // emitted expression. Stage only classes which may need that pass:
        // ordinary class methods stream directly in class-file order.
        let stage = !explicitly_selected
            && self.options.remove_synthetic
            && class
                .methods
                .iter()
                .any(|method| method.access_flags & SYNTHETIC != 0)
            && pool.iter().any(|constant| {
                matches!(constant, Constant::Class(index)
                    if pool.utf8(*index).ok() == Some("java/lang/invoke/LambdaMetafactory"))
            });
        if !stage {
            for method in &class.methods {
                if self.should_write_method(method, explicitly_selected)?
                    && self.method(
                        name,
                        method,
                        components,
                        enumeration,
                        constructors,
                        *needs_gap,
                        initializers,
                    )?
                {
                    *needs_gap = true;
                }
            }
            return self.write_source_helpers(needs_gap);
        }

        let mut staged: Vec<Option<MethodOutput>> =
            (0..class.methods.len()).map(|_| None).collect();
        let mut buffer = Writer {
            class,
            group: self.group,
            assertion_guards: self.assertion_guards,
            owner: self.owner,
            flags: self.flags,
            depth: self.depth,
            names: self.names,
            type_nesting: Rc::clone(&self.type_nesting),
            options: self.options,
            dynamic_helpers: Rc::clone(&self.dynamic_helpers),
            anonymous_bindings: self.anonymous_bindings.clone(),
            body: String::new(),
            lines: 0,
            tokens: Vec::new(),
            mapping: self.mapping.as_ref().map(|_| SourceMap::default()),
        };
        loop {
            let mut changed = false;
            for (method, output) in class.methods.iter().zip(&mut staged) {
                if output.is_some() || !self.should_write_method(method, false)? {
                    continue;
                }
                buffer.method(
                    name,
                    method,
                    components,
                    enumeration,
                    constructors,
                    false,
                    initializers,
                )?;
                *output = Some(MethodOutput {
                    body: mem::take(&mut buffer.body),
                    lines: mem::take(&mut buffer.lines),
                    tokens: mem::take(&mut buffer.tokens),
                    mapping: buffer.mapping.as_mut().map(mem::take),
                });
                changed = true;
            }
            if !changed {
                break;
            }
        }
        for output in staged
            .into_iter()
            .flatten()
            .filter(|method| method.lines != 0)
        {
            if *needs_gap {
                self.line(0, "");
            }
            self.body.push_str(&output.body);
            if let (Some(mapping), Some(method_mapping)) = (&mut self.mapping, output.mapping) {
                mapping.append(method_mapping, self.lines);
            }
            self.tokens
                .extend(output.tokens.into_iter().map(|(token, mut range)| {
                    range.shift_lines(self.lines);
                    (token, range)
                }));
            self.lines += output.lines;
            *needs_gap = true;
        }
        self.write_source_helpers(needs_gap)
    }

    fn should_write_method(
        &self,
        method: &Member<'a>,
        explicitly_selected: bool,
    ) -> Result<bool, DecompileError> {
        let name = self.class.pool.utf8(method.name_index)?;
        if name == "<init>"
            && self.has_lexical_owner()
            && self
                .group
                .nested_class(self.owner)
                .is_some_and(|node| matches!(node.kind, NestedKind::Anonymous))
        {
            return Ok(false);
        }
        if self.flags & INTERFACE != 0 && name == "<clinit>" && !explicitly_selected {
            return Ok(false);
        }
        if explicitly_selected {
            let descriptor = self.class.pool.utf8(method.descriptor_index)?;
            return Ok(self.matches_method(name, descriptor));
        }
        if self.options.remove_bridge && method.access_flags & super::BRIDGE != 0 {
            return Ok(false);
        }
        Ok(!self.hidden(method)?
            || crate::lift::scala_trait::keep_synthetic_bridge(self.class, method)?
            || self
                .dynamic_helpers
                .borrow()
                .contains(&DynamicHelper::Synthetic(method.name_index, method.descriptor_index)))
    }
}

struct MethodOutput {
    body: String,
    lines: usize,
    tokens: Vec<(Rc<super::Token>, super::TokenRange)>,
    mapping: Option<SourceMap>,
}
