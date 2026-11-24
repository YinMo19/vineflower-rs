// Based on Vineflower ClassWriter and NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{iter::Peekable, ops::Range, rc::Rc};

use crate::{
    cfg::ControlFlowGraph,
    context::NestedKind,
    descriptor::MethodDescriptor,
    lift::{AnonymousSite, AnonymousSites, Machine},
    source_text::{
        Document,
        tokens::{Token, TokenPosition, TokenRange},
    },
    structure::{assertions::Sites, structure_with_assertions},
};

use super::{DecompileError, Writer, parse};

impl<'a, 'c> Writer<'a, 'c> {
    pub(super) fn anonymous_sites(&self) -> Option<AnonymousSites> {
        (self.options.decompile_inner
            && self.group.children(self.owner).any(|(_, class)| {
                matches!(class.kind, NestedKind::Anonymous | NestedKind::Local(_))
            }))
        .then(AnonymousSites::default)
    }

    pub(super) fn line_with_anonymous(
        &mut self,
        depth: usize,
        doc: &Document,
        sites: Option<&AnonymousSites>,
    ) -> Result<(), DecompileError> {
        self.line_with_anonymous_anchors(depth, doc, sites, None)
    }

    pub(super) fn line_with_anonymous_anchors(
        &mut self,
        depth: usize,
        doc: &Document,
        sites: Option<&AnonymousSites>,
        mut on_anchor: Option<&mut dyn FnMut(Range<u32>, usize)>,
    ) -> Result<(), DecompileError> {
        let text = doc.as_str();
        if !text.contains('\0') {
            if let Some(on_anchor) = on_anchor {
                let first = self.lines;
                self.document_line_with_anchors(depth, doc, |bytes, line| on_anchor(bytes, first + line));
            } else {
                self.document_line(depth, doc);
            }
            return Ok(());
        }
        let invalid = || DecompileError::InvalidAttribute("anonymous class expression");
        let sites = sites.ok_or_else(invalid)?.borrow();
        let mut fragments = text.split('\0');
        let depth = self.depth + depth;
        self.indent_anonymous(depth);
        let first = fragments.next().expect("split yields initial fragment");
        let mut tokens = doc.flat_tokens().peekable();
        let mut anchors = doc.flat_anchors().peekable();
        let mut record_anchors = |fragment: &str, start, mut line| {
            let Some(on_anchor) = on_anchor.as_deref_mut() else { return };
            let mut previous = 0;
            while let Some((at, bytes)) = anchors.next_if(|(at, _)| *at <= start + fragment.len()) {
                if at < start {
                    continue;
                }
                let offset = at - start;
                line += fragment.as_bytes()[previous..offset].iter().filter(|&&byte| byte == b'\n').count();
                on_anchor(bytes, line);
                previous = offset;
            }
        };
        record_anchors(first, 0, self.lines);
        self.append_anonymous_fragment(first, 0, &mut tokens);
        let mut fragment_start = first.len() + 1;
        while let Some(id) = fragments.next() {
            fragment_start += id.len() + 1;
            let id = id.parse::<usize>().map_err(|_| invalid())?;
            let site = sites.get(id).ok_or_else(invalid)?;
            let tail = fragments.next().ok_or_else(invalid)?;
            let node = self.group.nested_class(&site.class).ok_or_else(invalid)?;
            self.append_anonymous_synthetic_mark(&site.class);
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
            record_anchors(tail, fragment_start, self.lines);
            self.append_anonymous_fragment(tail, fragment_start, &mut tokens);
            fragment_start += tail.len() + 1;
        }
        self.body.push('\n');
        self.lines += 1;
        Ok(())
    }

    fn append_anonymous_fragment<'t>(
        &mut self,
        fragment: &str,
        start: usize,
        tokens: &mut Peekable<impl Iterator<Item = (Range<usize>, &'t Rc<Token>)>>,
    ) {
        if self.options.dump_text_tokens {
            let mut position = TokenPosition {
                line: self.lines,
                column: self
                    .body
                    .rsplit('\n')
                    .next()
                    .unwrap_or_default()
                    .encode_utf16()
                    .count(),
            };
            let mut previous = 0;
            let end = start + fragment.len();
            while tokens.peek().is_some_and(|(span, _)| span.start < end) {
                let (span, token) = tokens.next().expect("peeked token");
                if span.start < start || span.end > end {
                    continue;
                }
                let offset = span.start - start;
                let width = fragment[offset..span.end - start].encode_utf16().count();
                for ch in fragment[previous..offset].chars() {
                    if ch == '\n' {
                        position.line += 1;
                        position.column = 0;
                    } else {
                        position.column += ch.len_utf16();
                    }
                }
                previous = offset;
                self.tokens.push((
                    Rc::clone(token),
                    TokenRange {
                        start: position,
                        end: TokenPosition {
                            column: position.column + width,
                            ..position
                        },
                    },
                ));
            }
        }
        self.lines += fragment.bytes().filter(|&byte| byte == b'\n').count();
        self.body.push_str(fragment);
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
