// Based on Vineflower ClassesProcessor and StructContext (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::OnceLock,
};

use crate::{
    Options,
    classfile::{ClassError, ClassFile, find_attribute},
    emit::{self, DecompileError, Source},
    lift::enum_switch,
    naming::MemberRenames,
};

const STATIC: u16 = 0x0008;
const FINAL: u16 = 0x0010;
const SYNTHETIC: u16 = 0x1000;

struct Entry<'a> {
    class: ClassFile<'a>,
    source: bool,
}

/// Collect class files, using their internal JVM names rather than file paths.
#[derive(Default)]
pub struct ClassGroupBuilder<'a> {
    entries: BTreeMap<String, Entry<'a>>,
}

impl<'a> ClassGroupBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a class eligible for source emission; the first source definition wins.
    pub fn add(&mut self, bytes: &'a [u8]) -> Result<String, ClassError> {
        self.add_with_source_filter(bytes, |_| true)
    }

    /// Add classpath metadata without making the class eligible for emission.
    pub fn add_library(&mut self, bytes: &'a [u8]) -> Result<String, ClassError> {
        self.add_with_source_filter(bytes, |_| false)
    }

    /// Select source eligibility from the parsed class name without reading the class twice.
    pub fn add_with_source_filter(
        &mut self,
        bytes: &'a [u8],
        source: impl FnOnce(&str) -> bool,
    ) -> Result<String, ClassError> {
        let class = ClassFile::parse(bytes)?;
        let name = class.pool.class_name(class.this_class)?.to_owned();
        let source = source(&name);
        if self
            .entries
            .get(&name)
            .is_none_or(|old| source && !old.source)
        {
            self.entries.insert(name.clone(), Entry { class, source });
        }
        Ok(name)
    }

    pub fn build(self) -> Result<ClassGroup<'a>, ClassError> {
        let mut claims = BTreeMap::new();
        let mut enclosing = BTreeMap::new();
        for (name, entry) in &self.entries {
            let class = &entry.class;
            let pool = &class.pool;
            if let Some(owner) = enclosing_method(class)? {
                enclosing.insert(name.clone(), owner);
            }
            for row in class.inner_classes()? {
                let inner = pool.class_name(row.inner_class)?;
                let outer = (row.outer_class != 0)
                    .then(|| pool.class_name(row.outer_class))
                    .transpose()?;
                let simple = (row.inner_name != 0)
                    .then(|| pool.utf8(row.inner_name))
                    .transpose()?;
                let priority = (name == inner, outer == Some(name.as_str()), entry.source);
                if claims.get(inner).is_none_or(|(old, _)| priority > *old) {
                    claims.insert(
                        inner.to_owned(),
                        (priority, (outer, simple, row.access_flags)),
                    );
                }
            }
        }
        let mut nesting = BTreeMap::new();
        for (name, (_, (outer, simple, access_flags))) in claims {
            let node = if let Some(enclosing) = enclosing.remove(&name) {
                NestedClass {
                    outer: enclosing.owner,
                    kind: match simple {
                        Some(simple) => NestedKind::Local(simple.into()),
                        None => NestedKind::Anonymous,
                    },
                    access_flags,
                    method: enclosing.method,
                }
            } else if let Some(outer) = outer {
                NestedClass {
                    outer: outer.into(),
                    kind: simple.map_or(NestedKind::Anonymous, |simple| {
                        NestedKind::Member(simple.into())
                    }),
                    access_flags,
                    method: None,
                }
            } else {
                continue;
            };
            if node.outer != name {
                nesting.insert(name, node);
            }
        }
        // EnclosingMethod is authoritative even if an emitter omitted InnerClasses.
        for (name, enclosing) in enclosing {
            if name != enclosing.owner {
                nesting.insert(
                    name,
                    NestedClass {
                        outer: enclosing.owner,
                        kind: NestedKind::Anonymous,
                        access_flags: 0,
                        method: enclosing.method,
                    },
                );
            }
        }
        // Malformed ownership cycles must not hide all source files in the cycle.
        let mut cyclic = BTreeSet::new();
        for name in nesting.keys() {
            let mut path = BTreeSet::new();
            let mut cursor = name.as_str();
            while let Some(node) = nesting.get(cursor) {
                if !path.insert(cursor) {
                    let mut current = cursor;
                    loop {
                        cyclic.insert(current);
                        current = &nesting[current].outer;
                        if current == cursor {
                            break;
                        }
                    }
                    break;
                }
                cursor = &node.outer;
            }
        }
        let cyclic: Vec<_> = cyclic.into_iter().map(str::to_owned).collect();
        for name in cyclic {
            nesting.remove(&name);
        }
        let mut children: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut outer_fields = BTreeMap::new();
        let mut local_instances = BTreeSet::new();
        for (name, node) in &nesting {
            let Some(entry) = self.entries.get(name) else {
                continue;
            };
            if entry.source
                && self
                    .entries
                    .get(&node.outer)
                    .is_some_and(|parent| parent.source)
            {
                // BTreeMap iteration matches Vineflower's qualified-name ordering.
                children
                    .entry(node.outer.clone())
                    .or_default()
                    .push(name.clone());
            }
            if node.access_flags & (STATIC | 0x0200 | 0x4000) != 0 {
                continue;
            }
            let class = &entry.class;
            let mut field_name = None;
            let mut candidates = 0;
            let mut canonical_count = 0;
            let mut canonical_name = None;
            for field in &class.fields {
                if field.access_flags & (STATIC | FINAL) != FINAL {
                    continue;
                }
                let descriptor = class.pool.utf8(field.descriptor_index)?;
                if object_name(descriptor) == Some(node.outer.as_str())
                    && (field.access_flags & SYNTHETIC != 0
                        || find_attribute(&field.attributes, &class.pool, "Synthetic")?.is_some())
                {
                    let name = class.pool.utf8(field.name_index)?;
                    candidates += 1;
                    field_name = Some(name);
                    if Self::outer_field_name(name) {
                        canonical_name = Some(name);
                        canonical_count += 1;
                    }
                }
            }
            let field_name = if canonical_count == 1 {
                canonical_name
            } else if candidates == 1 {
                field_name
            } else {
                None
            };
            if !matches!(node.kind, NestedKind::Member(_)) {
                if let Some((method_name, descriptor)) = &node.method {
                    let Some(parent) = self.entries.get(&node.outer) else {
                        continue;
                    };
                    let mut instance = false;
                    for method in &parent.class.methods {
                        let pool = &parent.class.pool;
                        if pool.utf8(method.name_index)? == method_name
                            && pool.utf8(method.descriptor_index)? == descriptor
                        {
                            instance = method.access_flags & STATIC == 0;
                            break;
                        }
                    }
                    if !instance {
                        continue;
                    }
                } else if !field_name.is_some_and(Self::outer_field_name) {
                    // Initializers have no EnclosingMethod name, so the
                    // synthetic enclosing-instance field is the discriminator.
                    continue;
                }
                local_instances.insert(name.clone());
            }
            if let Some(field) = field_name {
                outer_fields.insert(name.clone(), field.to_owned());
            }
        }
        Ok(ClassGroup {
            entries: self.entries,
            nesting,
            children,
            outer_fields,
            local_instances,
            enum_switches: OnceLock::new(),
        })
    }

    fn outer_field_name(name: &str) -> bool {
        name.strip_prefix("this$").is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
    }
}

/// A parsed class provider. Each source root renders a separate compilation unit.
pub struct ClassGroup<'a> {
    entries: BTreeMap<String, Entry<'a>>,
    nesting: BTreeMap<String, NestedClass>,
    children: BTreeMap<String, Vec<String>>,
    outer_fields: BTreeMap<String, String>,
    local_instances: BTreeSet<String>,
    enum_switches: OnceLock<enum_switch::Plan>,
}

impl<'a> ClassGroup<'a> {
    pub fn new(classes: impl IntoIterator<Item = &'a [u8]>) -> Result<Self, ClassError> {
        let mut builder = ClassGroupBuilder::new();
        for bytes in classes {
            builder.add(bytes)?;
        }
        builder.build()
    }

    /// Whether this source class is not attached to another supplied source class.
    pub fn is_root(&self, name: &str) -> bool {
        self.entries.get(name).is_some_and(|entry| entry.source) && !self.is_attached(name)
    }

    /// Look up a source or library class by its internal JVM name.
    pub fn get(&self, name: &str) -> Option<&ClassFile<'a>> {
        self.entries.get(name).map(|entry| &entry.class)
    }

    pub(crate) fn enum_switches(&self) -> &enum_switch::Plan {
        self.enum_switches
            .get_or_init(|| enum_switch::Plan::build(self))
    }

    /// All source and library entries in internal JVM name order.
    pub(crate) fn classes(&self) -> impl Iterator<Item = (&str, &ClassFile<'a>)> {
        self.entries
            .iter()
            .map(|(name, entry)| (name.as_str(), &entry.class))
    }

    /// Source entries in internal JVM name order.
    pub(crate) fn sources(&self) -> impl Iterator<Item = (&str, &ClassFile<'a>)> {
        self.entries
            .iter()
            .filter_map(|(name, entry)| entry.source.then_some((name.as_str(), &entry.class)))
    }

    /// Determine the source file extension without decompiling the class.
    pub fn file_extension(
        &self,
        name: &str,
        options: &Options,
    ) -> Result<&'static str, DecompileError> {
        self.output_file_parts(name, options).map(|(extension, _)| extension)
    }

    pub(crate) fn output_file_parts(
        &self,
        name: &str,
        options: &Options,
    ) -> Result<(&'static str, Option<&str>), DecompileError> {
        let name = if options.decompile_inner {
            self.compilation_root(name)
        } else {
            name
        };
        let class = self
            .entries
            .get(name)
            .filter(|entry| entry.source)
            .ok_or_else(|| DecompileError::MissingClass(name.into()))?;
        let kind = if options.decompile_kotlin {
            crate::kotlin::metadata_kind(&class.class)?
        } else {
            None
        };
        let Some(kind) = kind else { return Ok(("java", None)); };
        // K2 derives a file facade or multifile part's JVM name from the
        // source basename. Writing FacadeKt.kt would change it to FacadeKtKt.
        let basename = if matches!(kind, 2 | 5) {
            class.class.source_file()?
                .and_then(|name| name.strip_suffix(".kt"))
                .filter(|name| !matches!(*name, "" | "." | "..") && !name.contains(['/', '\\', ':', '\0']))
        } else {
            None
        };
        Ok(("kt", basename))
    }

    /// Render one compilation unit in the context of all registered classes.
    /// An attached class selects the enclosing compilation unit unless inner-class
    /// reconstruction is disabled.
    pub fn decompile(&self, name: &str, options: &Options) -> Result<Source, DecompileError> {
        let renames = MemberRenames::build(self, options)?;
        self.decompile_with_renames(name, options, &renames)
    }

    pub(crate) fn decompile_with_renames(
        &self,
        name: &str,
        options: &Options,
        renames: &MemberRenames,
    ) -> Result<Source, DecompileError> {
        if !self.entries.get(name).is_some_and(|entry| entry.source) {
            return Err(DecompileError::MissingClass(name.into()));
        }
        let name = if options.decompile_inner {
            self.compilation_root(name)
        } else {
            name
        };
        emit::decompile_class(self, name, options, renames)
    }

    pub(crate) fn nested_class(&self, name: &str) -> Option<&NestedClass> {
        self.nesting.get(name)
    }

    pub(crate) fn children(&self, name: &str) -> impl Iterator<Item = (&str, &NestedClass)> {
        self.children
            .get(name)
            .into_iter()
            .flatten()
            .map(|child| (child.as_str(), &self.nesting[child]))
    }

    pub(crate) fn is_attached(&self, name: &str) -> bool {
        self.nesting.get(name).is_some_and(|node| {
            self.children.get(&node.outer).is_some_and(|children| {
                children
                    .binary_search_by(|child| child.as_str().cmp(name))
                    .is_ok()
            })
        })
    }

    pub(crate) fn compilation_root<'g>(&'g self, mut name: &'g str) -> &'g str {
        while self.is_attached(name) {
            name = &self.nesting[name].outer;
        }
        name
    }

    pub(crate) fn member_class(&self, name: &str) -> Option<MemberClass<'_>> {
        let node = self.nesting.get(name)?;
        let (simple_name, access_flags) = match &node.kind {
            NestedKind::Member(name) => (name.as_str(), node.access_flags),
            NestedKind::Anonymous
                if self.enum_switches().auxiliary_visibility(name) == Some(false) =>
            {
                (
                    self.entries.get_key_value(name)?.0.rsplit('/').next()?,
                    node.access_flags | STATIC,
                )
            }
            _ => return None,
        };
        Some(MemberClass {
            outer: &node.outer,
            simple_name,
            access_flags,
        })
    }

    pub(crate) fn constructor_outer(&self, owner: &str, descriptor: &str) -> Option<&str> {
        let outer = self.enclosing_instance(owner)?;
        let first_parameter = descriptor.strip_prefix("(L")?.split_once(';')?.0;
        (first_parameter == outer).then_some(outer)
    }

    pub(crate) fn enclosing_instance(&self, owner: &str) -> Option<&str> {
        if let Some(member) = self.member_class(owner) {
            return (member.access_flags & STATIC == 0).then_some(member.outer);
        }
        self.local_instances
            .contains(owner)
            .then(|| self.nesting[owner].outer.as_str())
    }

    pub(crate) fn outer_field(&self, owner: &str, field: &str, descriptor: &str) -> Option<&str> {
        let enclosing = self.enclosing_instance(owner)?;
        (self
            .outer_fields
            .get(owner)
            .is_some_and(|name| name == field)
            && object_name(descriptor) == Some(enclosing))
        .then_some(enclosing)
    }

    /// Test ancestry using the available hierarchy; absent class files are not guessed.
    pub(crate) fn is_assignable(&self, from: &str, to: &str) -> bool {
        if from == to || to == "java/lang/Object" {
            return true;
        }
        if self.get(from).is_none() {
            return false;
        }
        let mut visited = BTreeSet::new();
        let mut pending = vec![from];
        while let Some(name) = pending.pop() {
            if !visited.insert(name) {
                continue;
            }
            let Some(class) = self.get(name) else {
                continue;
            };
            for index in std::iter::once(class.super_class).chain(class.interfaces.iter().copied())
            {
                if index != 0
                    && let Ok(parent) = class.pool.class_name(index)
                {
                    if parent == to {
                        return true;
                    }
                    pending.push(parent);
                }
            }
        }
        false
    }
}

pub(crate) struct NestedClass {
    pub outer: String,
    pub kind: NestedKind,
    pub access_flags: u16,
    pub method: Option<(String, String)>,
}

pub(crate) enum NestedKind {
    Member(String),
    Local(String),
    Anonymous,
}

pub(crate) struct MemberClass<'a> {
    pub outer: &'a str,
    pub simple_name: &'a str,
    pub access_flags: u16,
}

struct EnclosingMethod {
    owner: String,
    method: Option<(String, String)>,
}

fn enclosing_method(class: &ClassFile<'_>) -> Result<Option<EnclosingMethod>, ClassError> {
    let Some(data) = find_attribute(&class.attributes, &class.pool, "EnclosingMethod")? else {
        return Ok(None);
    };
    let [a, b, c, d] = *data else {
        return Err(if data.len() < 4 {
            ClassError::UnexpectedEof {
                offset: 0,
                needed: 4,
                remaining: data.len(),
            }
        } else {
            ClassError::TrailingBytes {
                context: "EnclosingMethod",
                offset: 4,
                remaining: data.len() - 4,
            }
        });
    };
    let owner = class.pool.class_name(u16::from_be_bytes([a, b]))?.into();
    let method = u16::from_be_bytes([c, d]);
    let method = (method != 0)
        .then(|| class.pool.name_and_type(method))
        .transpose()?
        .map(|(name, descriptor)| (name.into(), descriptor.into()));
    Ok(Some(EnclosingMethod { owner, method }))
}

fn object_name(descriptor: &str) -> Option<&str> {
    descriptor.strip_prefix('L')?.strip_suffix(';')
}
