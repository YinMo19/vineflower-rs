//! The per-root name resolution used while rendering Java types.

use std::collections::VecDeque;

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use super::Cx;
use super::class_nodes::{ClassKind, ClassNode, ClassNodes};
use crate::structs::{StructClass, StructContext, struct_context::ClassResolver};
use crate::util::text_buffer::TextBuffer;

type InnerNames = FxHashMap<ArcStr, String>;

#[derive(Clone, Default)]
pub struct ImportCollector {
    package: String,
    package_prefix: String,
    simple_names: FxHashMap<String, String>,
    implicit_names: FxHashSet<String>,
    field_names: FxHashSet<ArcStr>,
    inner_names: FxHashMap<ArcStr, InnerNames>,
    write_locked: bool,
}

impl ImportCollector {
    pub fn for_class(context: &StructContext, class: &StructClass) -> Self {
        Self::for_class_resolved(context.resolver(), class)
    }

    fn for_class_resolved(context: ClassResolver<'_>, class: &StructClass) -> Self {
        let package = class.qualified_name.rsplit_once('/').map(|(pkg, _)| pkg);
        let mut collector = Self {
            package: package.unwrap_or("").replace('/', "."),
            package_prefix: package.map_or_else(String::new, |p| format!("{p}/")),
            ..Self::default()
        };
        let mut visited = FxHashSet::default();
        let mut current = class;
        let mut ancestor;
        loop {
            if !visited.insert(current.qualified_name.clone()) {
                break;
            }
            collector
                .field_names
                .extend(current.fields.iter().map(|f| f.name.clone()));
            ancestor = current
                .super_class
                .as_ref()
                .and_then(|s| context.get_class(s.get_string()));
            let Some(superclass) = &ancestor else { break };
            current = superclass;
        }
        collector.inner_names.insert(
            class.qualified_name.clone(),
            inherited_names(context, class, InnerNames::default()),
        );
        collector
    }

    pub fn for_root(context: &StructContext, nodes: &ClassNodes, root: &ClassNode) -> Self {
        Self::for_root_resolved(context.resolver(), nodes, root)
    }

    pub(super) fn for_root_resolved(
        context: ClassResolver<'_>,
        nodes: &ClassNodes,
        root: &ClassNode,
    ) -> Self {
        let mut collector = Self::for_class_resolved(context, &root.class);
        let root_names = &collector.inner_names[&root.class.qualified_name];
        let mut pending: Vec<_> = root
            .nested
            .iter()
            .rev()
            .map(|&child| (child, root_names.clone()))
            .collect();
        while let Some((id, inherited)) = pending.pop() {
            let node = &nodes[id];
            let names = inherited_names(context, &node.class, inherited);
            pending.extend(
                node.nested
                    .iter()
                    .rev()
                    .map(|&child| (child, names.clone())),
            );
            collector
                .inner_names
                .insert(node.class.qualified_name.clone(), names);
        }
        collector
    }

    pub(crate) fn reserve_name(&mut self, simple: &str, package: &str) {
        self.simple_names
            .entry(simple.to_owned())
            .or_insert_with(|| package.to_owned());
    }

    pub fn imports(&self) -> Vec<String> {
        self.imports_matching(|_| true)
    }

    pub(crate) fn imports_matching(&self, keep_package: impl Fn(&str) -> bool) -> Vec<String> {
        let mut entries: Vec<_> = self
            .simple_names
            .iter()
            .filter(|(name, package)| {
                !self.implicit_names.contains(*name)
                    && !package.is_empty()
                    && *package != "java.lang"
                    && **package != self.package
                    && keep_package(package)
            })
            .collect();
        entries.sort_unstable_by(|(a, ap), (b, bp)| {
            ap.encode_utf16()
                .cmp(bp.encode_utf16())
                .then_with(|| a.encode_utf16().cmp(b.encode_utf16()))
        });
        entries
            .into_iter()
            .map(|(name, pkg)| format!("{pkg}.{name}"))
            .collect()
    }

    fn resolve(
        &mut self,
        context: ClassResolver<'_>,
        nodes: &ClassNodes,
        current: Option<&str>,
        input: &str,
        imported: bool,
    ) -> Option<String> {
        let mut member = None;
        let full = if let Some(mut node) = nodes
            .get(input.replace('.', "/").as_str())
            .filter(|n| n.class.own)
        {
            member = node.simple_name.as_ref().map(ToString::to_string);
            while node.kind == ClassKind::Member {
                let Some(parent) = node.parent.map(|id| &nodes[id]) else {
                    break;
                };
                let Some(name) = &parent.simple_name else {
                    break;
                };
                member = Some(format!("{name}.{}", member.as_deref().unwrap_or("null")));
                node = parent;
            }
            if node.kind != ClassKind::Root {
                return member.or_else(|| {
                    (node.kind == ClassKind::Anonymous).then(|| "<unrepresentable>".to_owned())
                });
            }
            node.class.qualified_name.replace('/', ".")
        } else {
            input.replace('$', ".")
        };

        let (mut package, mut short) = full.rsplit_once('.').unwrap_or(("", &full));
        let mut shadowed = (context
            .get_class(&format!("{}{short}", self.package_prefix))
            .is_some()
            && package != self.package)
            || (!self.package.is_empty() && context.get_class(short).is_some());

        if !shadowed
            && let Some(names) = self.inner_names.get(current.unwrap_or(""))
            && names.get(short).is_some_and(|other| other != &full)
        {
            if context
                .get_class(&format!("{}${short}", package.replace('.', "/")))
                .is_none()
            {
                shadowed = true;
            } else if let Some((enclosing_pkg, enclosing_name)) = package.rsplit_once('.') {
                member = Some(format!("{enclosing_name}.{short}"));
                short = enclosing_name;
                package = enclosing_pkg;
                if names
                    .get(short)
                    .is_some_and(|other| other != &format!("{package}.{short}"))
                {
                    shadowed = true;
                    member = None;
                }
            }
        }

        if shadowed
            || self
                .simple_names
                .get(short)
                .is_some_and(|existing| existing != package)
        {
            return Some(match member {
                Some(name) if !package.is_empty() => format!("{package}.{name}"),
                Some(name) => name,
                None => full,
            });
        }
        if !self.write_locked && !self.simple_names.contains_key(short) {
            self.simple_names
                .insert(short.to_owned(), package.to_owned());
            if !imported {
                self.implicit_names.insert(short.to_owned());
            }
        }
        Some(member.unwrap_or_else(|| short.to_owned()))
    }

    /// ImportCollector.lock during speculative rendering. The caller restores
    /// the former lock state, including when nesting locks.
    pub fn set_write_locked(&mut self, locked: bool) -> bool {
        std::mem::replace(&mut self.write_locked, locked)
    }
}

fn inherited_names(
    context: ClassResolver<'_>,
    class: &StructClass,
    mut names: InnerNames,
) -> InnerNames {
    let mut visited = FxHashSet::default();
    let mut queue = VecDeque::new();
    let mut current = class;
    let mut ancestor;
    loop {
        if visited.insert(current.qualified_name.clone()) {
            queue.extend(current.super_class.iter().map(|s| s.get_string().clone()));
            queue.extend(current.interface_names.iter().cloned());
            if let Some(attr) = &current.attributes.inner_classes {
                names.extend(
                    attr.entries
                        .iter()
                        .filter(|entry| {
                            entry.enclosing_name.as_ref() == Some(&current.qualified_name)
                        })
                        .filter_map(|entry| {
                            Some((
                                entry.simple_name.clone()?,
                                entry.inner_name.replace(['/', '$'], "."),
                            ))
                        }),
                );
            }
        }
        ancestor = std::iter::from_fn(|| queue.pop_front()).find_map(|name| {
            (!visited.contains(&name))
                .then(|| context.get_class(&name))
                .flatten()
        });
        let Some(next) = &ancestor else { break };
        current = next;
    }
    names
}

/// ExprProcessor.buildJavaClassName preserves the binary name of an own class.
pub fn java_class_name(cx: &Cx, internal: &str) -> String {
    let name = internal.replace('/', ".");
    if internal.contains('$')
        && !cx
            .classes()
            .get_class(internal)
            .is_some_and(|class| class.own)
    {
        name.replace('$', ".")
    } else {
        name
    }
}

pub fn short_name(cx: &mut Cx, full_name: &str, imported: bool) -> Option<String> {
    cx.class_nodes.require_class_session();
    let current = cx.current_class_node.as_deref().map(|name| {
        cx.class_nodes
            .get(name)
            .map_or(name, |node| node.class.qualified_name.as_str())
    });
    cx.imports.resolve(
        cx.struct_context.resolving_with(&cx.expression_ids),
        &cx.class_nodes,
        current,
        full_name,
        imported,
    )
}

pub fn get_short_name(cx: &mut Cx, full_name: &str) -> String {
    short_name(cx, full_name, true).unwrap_or_else(|| "<undefinedtype>".to_owned())
}

pub(crate) fn write_imports(cx: &Cx, buffer: &mut TextBuffer, separator: bool) {
    if cx.options.remove_imports {
        return;
    }
    let imports = cx.imports.imports();
    for name in &imports {
        buffer
            .append("import ")
            .append(name)
            .append_char(';')
            .append_line_separator();
    }
    if separator && !imports.is_empty() {
        buffer.append_line_separator();
    }
}

pub fn get_short_name_in_class_context(cx: &mut Cx, full_name: &str) -> String {
    match short_name(cx, full_name, true) {
        Some(name) if cx.imports.field_names.contains(name.as_str()) => full_name.to_owned(),
        Some(name) => name,
        None => "<unknownclass>".to_owned(),
    }
}
