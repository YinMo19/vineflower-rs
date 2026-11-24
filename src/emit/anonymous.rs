// Based on Vineflower ClassWriter and NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::rc::Rc;

use crate::{
    cfg::ControlFlowGraph,
    context::NestedKind,
    descriptor::MethodDescriptor,
    lift::{AnonymousSite, AnonymousSites, Machine},
    source_text::Document,
    structure::{assertions::Sites, structure_with_assertions},
};

use super::{DecompileError, Writer, parse};

impl<'a, 'c> Writer<'a, 'c> {
    pub(super) fn anonymous_sites(&self) -> Option<AnonymousSites> {
        (self.options.decompile_inner
            && self
                .group
                .children(self.owner)
                .any(|(_, class)| matches!(class.kind, NestedKind::Anonymous)))
        .then(AnonymousSites::default)
    }

    pub(super) fn line_with_anonymous(
        &mut self,
        depth: usize,
        doc: &Document,
        sites: Option<&AnonymousSites>,
    ) -> Result<(), DecompileError> {
        let text = doc.as_str();
        if !text.contains('\0') {
            self.document_line(depth, doc);
            return Ok(());
        }
        let invalid = || DecompileError::InvalidAttribute("anonymous class expression");
        let sites = sites.ok_or_else(invalid)?.borrow();
        let mut fragments = text.split('\0');
        let depth = self.depth + depth;
        self.indent_anonymous(depth);
        self.body
            .push_str(fragments.next().expect("split yields initial fragment"));
        while let Some(id) = fragments.next() {
            let id = id.parse::<usize>().map_err(|_| invalid())?;
            let site = sites.get(id).ok_or_else(invalid)?;
            let tail = fragments.next().ok_or_else(invalid)?;
            let node = self.group.nested_class(&site.class).ok_or_else(invalid)?;
            self.body.push_str(" {");
            let opening = self.body.len();
            self.body.push('\n');
            self.lines += 1;
            let bindings = site.capture_bindings(self.anonymous_bindings.clone());
            let previous = std::mem::replace(&mut self.anonymous_bindings, bindings);
            let result = self.with_nested(&site.class, node, depth, |writer| {
                writer.anonymous_members(site)
            });
            self.anonymous_bindings = previous;
            result?;
            if self.body.len() == opening + 1 {
                // An empty anonymous class is printed as a single-line `{}`.
                self.body.pop();
                self.lines -= 1;
            } else {
                self.indent_anonymous(depth);
            }
            self.body.push('}');
            self.body.push_str(tail);
        }
        self.body.push('\n');
        self.lines += 1;
        Ok(())
    }

    fn indent_anonymous(&mut self, depth: usize) {
        for _ in 0..depth {
            self.body.push_str(&self.options.indent);
        }
    }

    fn anonymous_members(&mut self, site: &AnonymousSite) -> Result<(), DecompileError> {
        let pool = &self.class.pool;
        let mut needs_gap = false;
        if self.options.method_to_decompile.is_empty() {
            for field in &self.class.fields {
                let name = pool.utf8(field.name_index)?;
                let descriptor = pool.utf8(field.descriptor_index)?;
                if !site.captures_field(name, descriptor)
                    && self
                        .group
                        .outer_field(self.owner, name, descriptor)
                        .is_none()
                    && !self.hidden_field(field)?
                {
                    self.field(field, false, None)?;
                    needs_gap = true;
                }
            }
        }
        if self.anonymous_initializer(site, needs_gap)? {
            needs_gap = true;
        }
        self.write_methods(
            "",
            None,
            None,
            0,
            &mut needs_gap,
            &super::initializers::FieldInitializers::default(),
        )?;
        self.member_classes(needs_gap)
    }

    fn anonymous_initializer(
        &mut self,
        site: &AnonymousSite,
        needs_gap: bool,
    ) -> Result<bool, DecompileError> {
        let tail = &site.instructions[site.initializer_start..];
        if matches!(tail, [ret] if ret.opcode == 0xb1) {
            return Ok(false);
        }
        let pool = &self.class.pool;
        let mut constructor = None;
        for method in &self.class.methods {
            if pool.utf8(method.name_index)? == "<init>"
                && pool.utf8(method.descriptor_index)? == site.descriptor
            {
                constructor = Some(method);
                break;
            }
        }
        let invalid = || DecompileError::InvalidAttribute("anonymous constructor");
        let method = constructor.ok_or_else(invalid)?;
        let code = method.code(pool)?.ok_or_else(invalid)?;
        let wrap = |source: Box<dyn std::error::Error + Send + Sync>| DecompileError::Method {
            name: "<init>".into(),
            descriptor: site.descriptor.clone(),
            source,
        };
        let desc = parse(&site.descriptor, MethodDescriptor::parse)?;
        let graph = ControlFlowGraph::build(tail, &code.exceptions)
            .map_err(|error| wrap(Box::new(error)))?;
        let assertions = self
            .assertion_guard()
            .map(|guard| Sites::for_method(self.class, method, guard, tail, &graph))
            .transpose()
            .map_err(|error| wrap(Box::new(error)))?
            .flatten();
        let names = self.names;
        let map = |name: &str| names.render(name);
        let mut machine = Machine::new(self.class, method, &code, &desc, self.options, &map)
            .map_err(|error| wrap(Box::new(error)))?
            .with_group(self.group);
        machine.mark_initialized_this();
        machine.set_member_renames(self.names.renames());
        machine.set_dynamic_helpers(Rc::clone(&self.dynamic_helpers));
        machine.set_anonymous_bindings(self.anonymous_bindings.clone());
        let sites = self.anonymous_sites();
        if let Some(sites) = &sites {
            machine.set_anonymous_sites(Rc::clone(sites));
            machine.set_anonymous_source(tail);
        }
        let mut lines =
            structure_with_assertions(tail, &graph, machine, &code.exceptions, assertions.as_ref())
                .map_err(|error| wrap(Box::new(error)))?;
        let closing = if lines
            .last()
            .is_some_and(|line| line.depth == 0 && line.text.as_str() == "return;")
        {
            lines.pop().map(|line| line.offsets)
        } else {
            None
        };
        if lines.iter().any(|line| line.text.as_str() == "return;") {
            return Err(DecompileError::Unsupported {
                feature: "nonlocal return from anonymous initializer",
            });
        }
        if lines.is_empty() {
            return Ok(false);
        }
        if needs_gap {
            self.line(0, "");
        }
        self.line(1, "{");
        self.method_body(
            "<init>",
            &site.descriptor,
            &code,
            lines,
            closing,
            sites.as_ref(),
        )?;
        Ok(true)
    }
}
