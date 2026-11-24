// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::{
    ClassGroup, Options,
    classfile::{ClassError, ClassFile, Constant, Member},
    context::NestedKind,
};

use super::{IdentifierKind, MemberRenamer};

const PUBLIC: u16 = 0x0001;
const PRIVATE: u16 = 0x0002;
const PROTECTED: u16 = 0x0004;
const STATIC: u16 = 0x0008;
const NATIVE: u16 = 0x0100;
const INTERFACE: u16 = 0x0200;

/// Session-wide Java names keyed by original JVM owners and descriptors.
/// Class-file metadata itself stays unchanged, including all bytecode offsets.
#[derive(Debug, Default)]
pub struct MemberRenames {
    classes: HashMap<String, ClassAlias>,
    hierarchy: Hierarchy,
    aliases: Vec<String>,
}

#[derive(Debug)]
struct ClassAlias {
    binary: String,
    simple: Option<String>,
}

impl MemberRenames {
    /// Builds one deterministic allocation over the whole source group. Both
    /// explicit library classes and available classpath ancestors keep their names.
    pub fn build(group: &ClassGroup<'_>, options: &Options) -> Result<Self, ClassError> {
        if !options.rename_members {
            return Ok(Self::default());
        }
        let mut renamer = MemberRenamer::default();
        let hierarchy = Hierarchy::build(group, options)?;
        let order = hierarchy.parent_first();
        let classes = class_aliases(group, options, &mut renamer)?;
        let mut result = Self {
            classes,
            hierarchy,
            aliases: Vec::new(),
        };
        result.assign_methods(&order, &mut renamer);
        result.assign_fields(&order, &mut renamer);
        Ok(result)
    }

    /// Effective internal binary name, including a renamed enclosing class.
    pub fn class_name<'a>(&'a self, original: &'a str) -> &'a str {
        self.classes
            .get(original)
            .map_or(original, |alias| &alias.binary)
    }

    /// The changed simple name in a class declaration, if any.
    pub fn simple_class_alias(&self, original: &str) -> Option<&str> {
        self.classes.get(original)?.simple.as_deref()
    }

    pub fn field_alias(&self, owner: &str, name: &str, descriptor: &str) -> Option<&str> {
        let index = *self.hierarchy.indices.get(owner)?;
        let declaration = find(&self.hierarchy.entries[index].fields, name, descriptor)?;
        self.alias(declaration)
    }

    pub fn method_alias(&self, owner: &str, name: &str, descriptor: &str) -> Option<&str> {
        let index = *self.hierarchy.indices.get(owner)?;
        self.alias(find(
            &self.hierarchy.entries[index].methods,
            name,
            descriptor,
        )?)
    }

    /// Name of a typed field reference. The constant-pool owner can inherit the
    /// field instead of declaring it; JVM field lookup visits interfaces first.
    pub fn field_name<'a>(&'a self, owner: &str, name: &'a str, descriptor: &str) -> &'a str {
        let Some(&owner) = self.hierarchy.indices.get(owner) else {
            return name;
        };
        self.hierarchy
            .resolve_field(owner, name, descriptor)
            .and_then(|member| self.alias(member))
            .unwrap_or(name)
    }

    /// Name of a typed method reference. Direct declarations and superclasses
    /// take precedence over inherited interface methods.
    pub fn method_name<'a>(&'a self, owner: &str, name: &'a str, descriptor: &str) -> &'a str {
        let Some(&owner) = self.hierarchy.indices.get(owner) else {
            return name;
        };
        self.hierarchy
            .resolve_method(owner, name, descriptor)
            .and_then(|member| self.alias(member))
            .unwrap_or(name)
    }

    fn alias(&self, declaration: &Declaration) -> Option<&str> {
        Some(self.aliases[declaration.alias?].as_str())
    }

    fn assign_methods(&mut self, order: &[usize], renamer: &mut MemberRenamer) {
        let entries = &self.hierarchy.entries;
        let mut declarations = Vec::new();
        let mut starts = Vec::with_capacity(entries.len());
        for (class, entry) in entries.iter().enumerate() {
            starts.push(declarations.len());
            declarations.extend(entry.methods.iter().map(|method| (class, method)));
        }
        let mut families = Families::new(declarations.len());
        let mut inherited: Vec<HashMap<(&str, &str, bool), usize>> =
            vec![HashMap::new(); entries.len()];
        let eligible: Vec<_> = declarations
            .iter()
            .map(|(_, method)| {
                MemberRenamer::to_be_renamed(IdentifierKind::Method, Some(&method.name))
            })
            .collect();
        for &class in order {
            let entry = &entries[class];
            let mut scope = HashMap::new();
            for parent in entry.parents() {
                for (&key, &method) in &inherited[parent] {
                    let (owner, declaration): (usize, &Declaration) = declarations[method];
                    if !visible_in(declaration.flags, entries[owner].package == entry.package) {
                        continue;
                    }
                    if let Some(existing) = scope.insert(key, method) {
                        families.join(existing, method);
                    }
                }
            }
            for (offset, method) in entry.methods.iter().enumerate() {
                if method.flags & PRIVATE != 0 || method.name.starts_with('<') {
                    continue;
                }
                if entry.flags & INTERFACE != 0 && method.flags & STATIC != 0 {
                    continue;
                }
                let id = starts[class] + offset;
                if !eligible[id] && !method.name.starts_with("method_") {
                    continue;
                }
                if let Some(parent) = scope.insert(method.signature(), id) {
                    families.join(parent, id);
                }
            }
            inherited[class] = scope;
        }

        let mut preserved = vec![false; declarations.len()];
        for (id, &(owner, method)) in declarations.iter().enumerate() {
            if !entries[owner].source || method.flags & NATIVE != 0 {
                preserved[families.root(id)] = true;
            }
        }
        // Candidate names need not be unique across unrelated types. Reserve
        // existing spellings in every scope where the renamed family is visible.
        let mut occupied: HashMap<&str, Vec<usize>> = HashMap::new();
        for (owner, entry) in entries.iter().enumerate() {
            let mut names = HashSet::new();
            names.extend(
                entry
                    .methods
                    .iter()
                    .map(|m| m.name.as_str())
                    .filter(|n| n.starts_with("method_")),
            );
            names.extend(
                inherited[owner]
                    .keys()
                    .map(|&(name, _, _)| name)
                    .filter(|n| n.starts_with("method_")),
            );
            for name in names {
                occupied.entry(name).or_default().push(owner);
            }
        }
        let mut assigned = vec![None; declarations.len()];
        let mut aliases = vec![None; declarations.len()];
        for &owner in order {
            let entry = &entries[owner];
            if !entry.source {
                continue;
            }
            for (offset, method) in entry.methods.iter().enumerate() {
                let id = starts[owner] + offset;
                if !eligible[id] {
                    continue;
                }
                let family = families.root(id);
                if preserved[family] {
                    continue;
                }
                let index = *assigned[family].get_or_insert_with(|| {
                    let name = renamer.next_available(IdentifierKind::Method, None, |candidate| {
                        occupied.get(candidate).is_some_and(|scopes| {
                            scopes.iter().any(|&scope| {
                                scope == owner
                                    || inherited[scope]
                                        .get(&method.signature())
                                        .is_some_and(|&id| families.root(id) == family)
                            })
                        })
                    });
                    let index = self.aliases.len();
                    self.aliases.push(name);
                    index
                });
                aliases[id] = Some(index);
            }
        }
        for (owner, entry) in self.hierarchy.entries.iter_mut().enumerate() {
            for (offset, method) in entry.methods.iter_mut().enumerate() {
                method.alias = aliases[starts[owner] + offset];
            }
        }
    }

    fn assign_fields(&mut self, order: &[usize], renamer: &mut MemberRenamer) {
        let hierarchy = &self.hierarchy;
        let mut occupied: HashMap<&str, Vec<usize>> = HashMap::new();
        for (owner, entry) in hierarchy.entries.iter().enumerate() {
            for field in entry.fields.iter().filter(|f| f.name.starts_with("field_")) {
                occupied.entry(&field.name).or_default().push(owner);
            }
        }
        let assigned: Vec<_> = order
            .iter()
            .filter_map(|&owner| {
                let entry = &hierarchy.entries[owner];
                entry.source.then(|| {
                    (
                        owner,
                        entry
                            .fields
                            .iter()
                            .map(|field| {
                                if !MemberRenamer::to_be_renamed(
                                    IdentifierKind::Field,
                                    Some(&field.name),
                                ) {
                                    return None;
                                }
                                let name = renamer.next_available(
                                    IdentifierKind::Field,
                                    None,
                                    |candidate| {
                                        occupied.get(candidate).is_some_and(|scopes| {
                                            scopes.iter().any(|&scope| {
                                                hierarchy.reaches(owner, scope)
                                                    || hierarchy.reaches(scope, owner)
                                            })
                                        })
                                    },
                                );
                                let index = self.aliases.len();
                                self.aliases.push(name);
                                Some(index)
                            })
                            .collect::<Vec<_>>(),
                    )
                })
            })
            .collect();
        for (owner, aliases) in assigned {
            for (field, alias) in self.hierarchy.entries[owner].fields.iter_mut().zip(aliases) {
                field.alias = alias;
            }
        }
    }
}

fn visible_in(flags: u16, same_package: bool) -> bool {
    flags & PRIVATE == 0 && (flags & (PUBLIC | PROTECTED) != 0 || same_package)
}

#[derive(Debug)]
struct Declaration {
    name: String,
    descriptor: String,
    flags: u16,
    alias: Option<usize>,
}

impl Declaration {
    fn new(name: &str, descriptor: &str, flags: u16) -> Self {
        Self {
            name: name.into(),
            descriptor: descriptor.into(),
            flags,
            alias: None,
        }
    }

    fn signature(&self) -> (&str, &str, bool) {
        (&self.name, &self.descriptor, self.flags & STATIC != 0)
    }
}

fn find<'a>(
    declarations: &'a [Declaration],
    name: &str,
    descriptor: &str,
) -> Option<&'a Declaration> {
    declarations
        .iter()
        .find(|member| member.name == name && member.descriptor == descriptor)
}

#[derive(Debug, Default)]
struct Hierarchy {
    entries: Vec<Entry>,
    indices: HashMap<String, usize>,
}

#[derive(Debug, Default)]
struct Entry {
    source: bool,
    flags: u16,
    package: usize,
    parent: Option<usize>,
    interfaces: Vec<usize>,
    fields: Vec<Declaration>,
    methods: Vec<Declaration>,
}

impl Entry {
    fn parents(&self) -> impl DoubleEndedIterator<Item = usize> + '_ {
        self.parent
            .into_iter()
            .chain(self.interfaces.iter().copied())
    }
}

impl Hierarchy {
    fn build(group: &ClassGroup<'_>, options: &Options) -> Result<Self, ClassError> {
        let mut graph = Self::default();
        let mut pending = Vec::new();
        let mut packages = HashMap::new();
        let sources: HashSet<_> = group.sources().map(|(name, _)| name).collect();
        for (name, _) in group.classes() {
            graph.enqueue(name, &mut pending);
        }
        // External owners in references can themselves inherit a source member.
        for (_, class) in group.sources() {
            for constant in class.pool.iter() {
                if let Constant::Fieldref { class_index, .. }
                | Constant::Methodref { class_index, .. }
                | Constant::InterfaceMethodref { class_index, .. } = constant
                {
                    let owner = class.pool.class_name(*class_index)?;
                    if !owner.starts_with('[') {
                        graph.enqueue(owner, &mut pending);
                    }
                }
            }
        }
        let mut i = 0;
        while i < pending.len() {
            // Enqueueing parents can reallocate pending, so take the name.
            let name = std::mem::take(&mut pending[i]);
            let next_package = packages.len();
            let package = *packages
                .entry(package(&name).to_owned())
                .or_insert(next_package);
            let mut entry = Entry {
                package,
                ..Entry::default()
            };
            if let Some(class) = group.get(&name) {
                entry.source = sources.contains(name.as_str());
                entry.flags = class.access_flags;
                if class.super_class != 0 {
                    entry.parent = Some(
                        graph.enqueue(class.pool.class_name(class.super_class)?, &mut pending),
                    );
                }
                for &interface in &class.interfaces {
                    entry
                        .interfaces
                        .push(graph.enqueue(class.pool.class_name(interface)?, &mut pending));
                }
                entry.fields = read_members(class, &class.fields)?;
                entry.methods = read_members(class, &class.methods)?;
            } else {
                let external = [
                    options.library_classpath.as_deref(),
                    options.runtime_classpath.as_deref(),
                ];
                if let Some(metadata) = external
                    .into_iter()
                    .flatten()
                    .find_map(|path| path.metadata(&name).ok().flatten())
                {
                    entry.flags = metadata.access_flags;
                    entry.parent = metadata
                        .super_name
                        .as_deref()
                        .map(|name| graph.enqueue(name, &mut pending));
                    entry.interfaces.extend(
                        metadata
                            .interfaces
                            .iter()
                            .map(|name| graph.enqueue(name, &mut pending)),
                    );
                    entry.fields.extend(
                        metadata
                            .fields
                            .iter()
                            .map(|m| Declaration::new(&m.name, &m.descriptor, m.access_flags)),
                    );
                    entry.methods.extend(
                        metadata
                            .methods
                            .iter()
                            .map(|m| Declaration::new(&m.name, &m.descriptor, m.access_flags)),
                    );
                }
            }
            graph.entries.push(entry);
            i += 1;
        }
        Ok(graph)
    }

    fn enqueue(&mut self, name: &str, pending: &mut Vec<String>) -> usize {
        if let Some(&index) = self.indices.get(name) {
            return index;
        }
        let index = pending.len();
        self.indices.insert(name.into(), index);
        pending.push(name.into());
        index
    }

    fn parent_first(&self) -> Vec<usize> {
        let mut children = vec![Vec::new(); self.entries.len()];
        let mut need = vec![0; self.entries.len()];
        let mut ready = BTreeSet::new();
        let key = |i: usize| (self.entries[i].flags & INTERFACE == 0, i);
        for (child, entry) in self.entries.iter().enumerate() {
            for parent in entry.parents() {
                need[child] += 1;
                children[parent].push(child);
            }
            if need[child] == 0 {
                ready.insert(key(child));
            }
        }
        let mut order = Vec::with_capacity(self.entries.len());
        while let Some((_, owner)) = ready.pop_first() {
            order.push(owner);
            for &child in &children[owner] {
                need[child] -= 1;
                if need[child] == 0 {
                    ready.insert(key(child));
                }
            }
        }
        // A malformed cyclic hierarchy has no topological ordering. Keep all
        // declarations addressable; reference and namespace walks are bounded.
        order.extend((0..self.entries.len()).filter(|&i| need[i] != 0));
        order
    }

    fn reaches(&self, from: usize, target: usize) -> bool {
        if from == target {
            return true;
        }
        let mut visited = HashSet::new();
        let mut pending = vec![from];
        while let Some(index) = pending.pop() {
            if index == target {
                return true;
            }
            if visited.insert(index) {
                pending.extend(self.entries[index].parents());
            }
        }
        false
    }

    fn resolve_field(&self, owner: usize, name: &str, descriptor: &str) -> Option<&Declaration> {
        let entry = &self.entries[owner];
        let direct = find(&entry.fields, name, descriptor);
        if direct.is_some() {
            return direct;
        }
        let mut pending = Vec::new();
        let mut visited = HashSet::new();
        visited.insert(owner);
        // Push superclasses first, then interfaces in reverse declaration order.
        pending.extend(entry.parent);
        pending.extend(entry.interfaces.iter().rev().copied());
        while let Some(index) = pending.pop() {
            if !visited.insert(index) {
                continue;
            }
            let entry = &self.entries[index];
            if let Some(field) = find(&entry.fields, name, descriptor) {
                return Some(field);
            }
            pending.extend(entry.parent);
            pending.extend(entry.interfaces.iter().rev().copied());
        }
        None
    }

    fn resolve_method(&self, owner: usize, name: &str, descriptor: &str) -> Option<&Declaration> {
        if let Some(method) = find(&self.entries[owner].methods, name, descriptor) {
            return Some(method);
        }
        if name.starts_with('<') {
            return None;
        }
        let mut interfaces = Vec::new();
        let mut class = owner;
        for _ in 0..self.entries.len() {
            let entry = &self.entries[class];
            interfaces.extend(entry.interfaces.iter().rev().copied());
            let Some(parent) = entry.parent else { break };
            if let Some(method) = find(&self.entries[parent].methods, name, descriptor) {
                return Some(method);
            }
            class = parent;
        }
        let mut visited = HashSet::new();
        while let Some(index) = interfaces.pop() {
            if !visited.insert(index) {
                continue;
            }
            let entry = &self.entries[index];
            if let Some(method) = find(&entry.methods, name, descriptor)
                && method.flags & (PRIVATE | STATIC) == 0
            {
                return Some(method);
            }
            interfaces.extend(entry.interfaces.iter().rev().copied());
        }
        None
    }
}

fn read_members(
    class: &ClassFile<'_>,
    members: &[Member<'_>],
) -> Result<Vec<Declaration>, ClassError> {
    members
        .iter()
        .map(|member| {
            Ok(Declaration::new(
                class.pool.utf8(member.name_index)?,
                class.pool.utf8(member.descriptor_index)?,
                member.access_flags,
            ))
        })
        .collect()
}

struct Families(Vec<usize>);

impl Families {
    fn new(len: usize) -> Self {
        Self((0..len).collect())
    }

    fn root(&mut self, mut x: usize) -> usize {
        while self.0[x] != x {
            self.0[x] = self.0[self.0[x]];
            x = self.0[x];
        }
        x
    }

    fn join(&mut self, first: usize, second: usize) {
        let first = self.root(first);
        let second = self.root(second);
        self.0[first.max(second)] = first.min(second);
    }
}

fn package(name: &str) -> &str {
    name.rsplit_once('/').map_or("", |(package, _)| package)
}

fn class_aliases(
    group: &ClassGroup<'_>,
    options: &Options,
    renamer: &mut MemberRenamer,
) -> Result<HashMap<String, ClassAlias>, ClassError> {
    let attached = |name: &str| options.decompile_inner && group.is_attached(name);
    let exists = |candidate: &str| {
        group.get(candidate).is_some()
            || [
                options.library_classpath.as_deref(),
                options.runtime_classpath.as_deref(),
            ]
            .into_iter()
            .flatten()
            .any(|path| path.metadata(candidate).is_ok_and(|class| class.is_some()))
    };
    let mut simple = HashMap::new();
    let mut allocated = HashSet::new();
    for (name, _) in group.sources().filter(|(name, _)| !attached(name)) {
        let (prefix, leaf) = name.split_at(name.rfind('/').map_or(0, |slash| slash + 1));
        if MemberRenamer::to_be_renamed(IdentifierKind::Class, Some(leaf)) {
            let alias = renamer.next_available(IdentifierKind::Class, Some(leaf), |candidate| {
                let candidate = format!("{prefix}{candidate}");
                exists(&candidate) || allocated.contains(&candidate)
            });
            allocated.insert(format!("{prefix}{alias}"));
            simple.insert(name, alias);
        }
    }

    if options.decompile_inner {
        let owned: HashSet<_> = group.sources().map(|(name, _)| name).collect();
        for (_, class) in group.sources() {
            // ClassesProcessor allocates source-level inner names in InnerClasses
            // attribute order, which need not be member or lexical name order.
            for row in class.inner_classes()? {
                let name = class.pool.class_name(row.inner_class)?;
                if !owned.contains(name) || !attached(name) || simple.contains_key(name) {
                    continue;
                }
                let Some(node) = group.nested_class(name) else {
                    continue;
                };
                let leaf = match &node.kind {
                    NestedKind::Member(leaf) | NestedKind::Local(leaf) => leaf,
                    NestedKind::Anonymous => continue,
                };
                if !MemberRenamer::to_be_renamed(IdentifierKind::Class, Some(leaf)) {
                    continue;
                }
                let local_prefix = if matches!(&node.kind, NestedKind::Local(_)) {
                    name.strip_prefix(node.outer.as_str())
                        .and_then(|suffix| suffix.strip_prefix('$'))
                        .and_then(|suffix| suffix.strip_suffix(leaf.as_str()))
                        .unwrap_or("")
                } else {
                    ""
                };
                let alias =
                    renamer.next_available(IdentifierKind::Class, Some(leaf), |candidate| {
                        exists(&format!("{}${local_prefix}{candidate}", node.outer))
                            || group.children(&node.outer).any(|(sibling, declaration)| {
                                simple
                                    .get(sibling)
                                    .is_some_and(|simple| simple == candidate)
                                    || match &declaration.kind {
                                        NestedKind::Member(name) | NestedKind::Local(name) => {
                                            name == candidate
                                        }
                                        NestedKind::Anonymous => false,
                                    }
                            })
                    });
                simple.insert(name, alias);
            }
        }
    }
    if simple.is_empty() {
        return Ok(HashMap::new());
    }

    let mut result = HashMap::new();
    for (name, _) in group.sources() {
        let mut path = vec![(name, simple.get(name))];
        let mut owner = name;
        while attached(owner)
            && let Some(nested) = group.nested_class(owner)
        {
            owner = &nested.outer;
            if path.iter().any(|(seen, _)| *seen == owner) {
                break;
            }
            path.push((owner, simple.get(owner)));
        }
        if !path.iter().any(|(_, alias)| alias.is_some()) {
            continue;
        }
        let (root, alias) = path.pop().expect("the root is part of its own path");
        let mut binary = root.to_owned();
        if let Some(alias) = alias {
            binary.truncate(root.rfind('/').map_or(0, |index| index + 1));
            binary.push_str(alias);
        }
        let mut outer = root;
        for (nested, alias) in path.into_iter().rev() {
            binary.push('$');
            let suffix = nested
                .strip_prefix(outer)
                .and_then(|suffix| suffix.strip_prefix('$'))
                .unwrap_or_else(|| nested.rsplit('/').next().unwrap_or(nested));
            if let Some(alias) = alias {
                if let Some(NestedKind::Local(leaf)) =
                    group.nested_class(nested).map(|node| &node.kind)
                {
                    binary.push_str(suffix.strip_suffix(leaf.as_str()).unwrap_or(""));
                }
                binary.push_str(alias);
            } else {
                binary.push_str(suffix);
            }
            outer = nested;
        }
        result.insert(
            name.into(),
            ClassAlias {
                binary,
                simple: None,
            },
        );
    }
    for (name, alias) in simple {
        result
            .get_mut(name)
            .expect("each renamed class has a binary alias")
            .simple = Some(alias);
    }
    Ok(result)
}
