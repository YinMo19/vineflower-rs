// Based on Vineflower ClassWriter and ClassesProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
mod annotation;
mod anonymous;
mod enumeration;
mod initializers;
mod mapping;
mod module;
mod names;
mod nested;
mod options_support;
mod record;
pub(crate) mod symbols;
pub(crate) mod synthetic_marks;
pub(crate) mod type_annotations;

pub use mapping::{MethodMap, SourceMap};

use std::{collections::BTreeMap, fmt::Write, rc::Rc};

use thiserror::Error;

use crate::{
    Options, bytecode,
    cfg::ControlFlowGraph,
    classfile::{
        ClassError, ClassFile, Code, Member, RecordComponent, Supertype, TypeTarget, find_attribute,
    },
    context::{ClassGroup, ClassGroupBuilder},
    descriptor::{
        ClassSignature, DescriptorError, FieldSignature, MethodDescriptor, MethodSignature, Type,
    },
    javadoc::JavadocTarget,
    lift::{DynamicHelpers, Machine, constant_literal_with_options},
    naming::MemberRenames,
    source_text::{
        Document,
        tokens::{self, Token, TokenKind, TokenRange},
    },
    structure::{
        Line, StructureError,
        assertions::{Guard, Sites, interface_guards, is_guard_field},
        structure_with_assertions,
    },
};
use enumeration::Enumeration;
use names::{Names, simple};
use type_annotations::TypeNesting;

const PUBLIC: u16 = 0x0001;
const PRIVATE: u16 = 0x0002;
const PROTECTED: u16 = 0x0004;
const STATIC: u16 = 0x0008;
const FINAL: u16 = 0x0010;
const SYNCHRONIZED: u16 = 0x0020;
const BRIDGE: u16 = 0x0040;
const VARARGS: u16 = 0x0080;
const NATIVE: u16 = 0x0100;
const INTERFACE: u16 = 0x0200;
const ABSTRACT: u16 = 0x0400;
const STRICT: u16 = 0x0800;
const SYNTHETIC: u16 = 0x1000;
const ANNOTATION: u16 = 0x2000;
const ENUM: u16 = 0x4000;
const MODULE: u16 = 0x8000;
const VISIBILITY: u16 = PUBLIC | PRIVATE | PROTECTED;

/// A Java compilation unit recovered from a class file.
#[derive(Debug)]
pub struct Source {
    /// Original internal JVM name, e.g. `example/Counter`.
    pub class_name: String,
    renamed_name: Option<String>,
    pub text: String,
    /// Source filename extension without a leading dot.
    pub file_extension: &'static str,
    pub map: Option<SourceMap>,
}

impl Source {
    /// Internal binary name under which the emitted source should be saved.
    pub fn output_class_name(&self) -> &str {
        self.renamed_name.as_deref().unwrap_or(&self.class_name)
    }
}

#[derive(Debug, Error)]
pub enum DecompileError {
    #[error(transparent)]
    ClassFile(#[from] ClassError),
    #[error("invalid JVM descriptor or signature {input:?}: {source}")]
    Descriptor {
        input: String,
        #[source]
        source: DescriptorError,
    },
    #[error("source class {0:?} does not exist in the class group")]
    MissingClass(String),
    #[error(transparent)]
    Kotlin(#[from] crate::kotlin::KotlinError),
    #[error("malformed {0} attribute")]
    InvalidAttribute(&'static str),
    #[error("unsupported Java recovery: {feature}")]
    Unsupported { feature: &'static str },
    #[error("cannot recover {name}{descriptor}: {source}")]
    Method {
        name: String,
        descriptor: String,
        #[source]
        source: Box<dyn std::error::Error + Send + Sync>,
    },
    #[error("cannot render {context}: {source}")]
    Render {
        context: &'static str,
        #[source]
        source: Box<dyn std::error::Error + Send + Sync>,
    },
}

/// Recover a compilation unit without running a JVM or delegating to a Java decompiler.
pub fn decompile(bytes: &[u8], options: &Options) -> Result<Source, DecompileError> {
    decompile_group(bytes, std::iter::empty(), options)
}

/// Recover the primary compilation unit with class metadata from companion files.
pub fn decompile_group<'a>(
    primary: &'a [u8],
    companions: impl IntoIterator<Item = &'a [u8]>,
    options: &Options,
) -> Result<Source, DecompileError> {
    let mut builder = ClassGroupBuilder::new();
    let primary = builder.add(primary)?;
    for bytes in companions {
        builder.add(bytes)?;
    }
    builder.build()?.decompile(&primary, options)
}

pub(crate) fn decompile_class(
    group: &ClassGroup<'_>,
    class_name: &str,
    options: &Options,
    renames: &MemberRenames,
) -> Result<Source, DecompileError> {
    let class = group.get(class_name).expect("source class is registered");
    let class_name = class.pool.class_name(class.this_class)?;
    if options.decompile_kotlin
        && let Some((source, mut map)) =
            crate::kotlin::decompile_with_options(class, group, options)?
    {
        let text = finish_source(
            class_name,
            options.banner.clone(),
            &source,
            map.as_mut(),
            &mut [],
            options,
        );
        return Ok(Source {
            class_name: class_name.into(),
            renamed_name: None,
            text,
            file_extension: "kt",
            map,
        });
    }
    let mut guards = BTreeMap::new();
    if options.decompile_assert {
        let mut pending = vec![class_name];
        while let Some(owner) = pending.pop() {
            if let Some(class) = group.get(owner)
                && let Some(guard) = Guard::prove(group, class, class_name)
            {
                guards.insert(owner, guard);
            }
            if options.decompile_inner {
                pending.extend(group.children(owner).map(|(child, _)| child));
            }
        }
        if options.decompile_inner {
            guards.extend(interface_guards(group, class_name));
        }
    }
    let source = decompile_java(group, class, class_name, options, renames, &guards);
    if matches!(&source, Err(DecompileError::Method { source, .. })
        if matches!(source.downcast_ref::<StructureError>(), Some(StructureError::Assertion)))
    {
        // A raw CFG proof may still fail expression lifting. Start a fresh
        // compilation unit so the original field and initializer remain.
        return decompile_java(group, class, class_name, options, renames, &BTreeMap::new());
    }
    source
}

fn decompile_java<'a>(
    group: &ClassGroup<'a>,
    class: &ClassFile<'a>,
    class_name: &str,
    options: &Options,
    renames: &MemberRenames,
    guards: &BTreeMap<&str, Guard<'_>>,
) -> Result<Source, DecompileError> {
    let source_name = renames.class_name(class_name);
    let names = Names::new(group, class_name, options, renames);
    let mut writer = Writer {
        class,
        owner: class_name,
        flags: class.access_flags,
        depth: 0,
        group,
        assertion_guards: guards,
        dynamic_helpers: DynamicHelpers::default(),
        anonymous_bindings: None,
        names: &names,
        type_nesting: Rc::new(TypeNesting::new(class)?),
        options,
        body: String::new(),
        lines: 0,
        tokens: Vec::new(),
        mapping: options.include_line_mappings.then(SourceMap::default),
    };
    let package = source_name
        .rsplit_once('/')
        .map(|(package, _)| package.replace('/', "."));
    let mut prefix = options.banner.clone();
    let mut token_prefix = None;
    match simple(source_name) {
        "module-info" if class.access_flags & MODULE != 0 => {
            writer.module()?;
            let import_start = prefix.len();
            names.imports(&mut prefix, &writer.body);
            if prefix.len() != import_start {
                prefix.push('\n');
            }
        }
        "package-info" => {
            writer.class_annotations(0)?;
            token_prefix = Some(prefix.len());
            prefix.push_str(&writer.body);
            if let Some(package) = &package {
                let _ = writeln!(prefix, "package {package};\n");
            }
            names.imports(&mut prefix, &writer.body);
            writer.body.clear();
        }
        simple_name => {
            writer.class(simple_name)?;
            if let Some(package) = &package {
                let _ = writeln!(prefix, "package {package};\n");
            }
            let import_start = prefix.len();
            names.imports(&mut prefix, &writer.body);
            if prefix.len() != import_start {
                prefix.push('\n');
            }
        }
    }
    if !writer.tokens.is_empty() {
        let token_prefix = &prefix[..token_prefix.unwrap_or(prefix.len())];
        let newlines = token_prefix.bytes().filter(|&byte| byte == b'\n').count();
        let first_column = token_prefix
            .rsplit('\n')
            .next()
            .unwrap_or("")
            .encode_utf16()
            .count();
        for (_, range) in &mut writer.tokens {
            if range.start.line == 0 {
                range.start.column += first_column;
            }
            if range.end.line == 0 {
                range.end.column += first_column;
            }
            range.shift_lines(newlines);
        }
    }
    let text = finish_source(
        class_name,
        prefix,
        &writer.body,
        writer.mapping.as_mut(),
        &mut writer.tokens,
        options,
    );
    Ok(Source {
        class_name: class_name.into(),
        renamed_name: (source_name != class_name).then(|| source_name.into()),
        text,
        file_extension: "java",
        map: writer.mapping,
    })
}

fn finish_source(
    class_name: &str,
    mut prefix: String,
    body: &str,
    mapping: Option<&mut SourceMap>,
    source_tokens: &mut [(Rc<Token>, TokenRange)],
    options: &Options,
) -> String {
    if let Some(mapping) = mapping {
        mapping.shift(prefix.bytes().filter(|&byte| byte == b'\n').count());
        prefix.push_str(body);
        if options.dump_original_lines && !mapping.original_lines.is_empty() {
            let mut annotated = String::with_capacity(prefix.len());
            mapping.annotate(&prefix, &mut annotated);
            prefix = annotated;
        }
        if options.unit_test_mode {
            mapping.dump(class_name, &options.indent, &mut prefix);
        }
    } else {
        prefix.push_str(body);
    }
    if options.dump_text_tokens {
        tokens::dump(&mut prefix, source_tokens);
    }
    if options.crlf {
        prefix.replace('\n', "\r\n")
    } else {
        prefix
    }
}

struct Writer<'a, 'c> {
    class: &'c ClassFile<'a>,
    group: &'c ClassGroup<'a>,
    assertion_guards: &'c BTreeMap<&'c str, Guard<'c>>,
    owner: &'c str,
    flags: u16,
    depth: usize,
    names: &'c Names<'a, 'c>,
    type_nesting: Rc<TypeNesting<'c>>,
    dynamic_helpers: DynamicHelpers,
    anonymous_bindings: Option<crate::lift::AnonymousBindings>,
    options: &'c Options,
    body: String,
    lines: usize,
    tokens: Vec<(Rc<Token>, TokenRange)>,
    mapping: Option<SourceMap>,
}

impl<'a, 'c> Writer<'a, 'c> {
    fn line(&mut self, depth: usize, text: &str) {
        for line in text.split('\n') {
            if !line.is_empty() {
                for _ in 0..self.depth + depth {
                    self.body.push_str(&self.options.indent);
                }
                self.body.push_str(line);
            }
            self.body.push('\n');
            self.lines += 1;
        }
    }

    fn document_line(&mut self, depth: usize, doc: &Document) {
        self.document_line_with_anchors(depth, doc, |_, _| {});
    }

    fn document_line_with_anchors(
        &mut self,
        depth: usize,
        doc: &Document,
        on_anchor: impl FnMut(std::ops::Range<u32>, usize),
    ) {
        if !doc.has_layout() && !(self.options.dump_text_tokens && doc.has_tokens()) {
            self.line(depth, doc.as_str());
            return;
        }
        let depth = self.depth + depth;
        for _ in 0..depth {
            self.body.push_str(&self.options.indent);
        }
        let width = self.options.preferred_line_length;
        let indent = &self.options.indent;
        let crlf = self.options.crlf;
        self.lines += if self.options.dump_text_tokens {
            let first_line = self.lines;
            let tokens = &mut self.tokens;
            doc.render_with_tokens_at(
                &mut self.body,
                width,
                indent,
                crlf,
                depth,
                on_anchor,
                |token, mut range| {
                    range.shift_lines(first_line);
                    tokens.push((Rc::clone(token), range));
                },
            )
        } else {
            doc.render_at(&mut self.body, width, indent, crlf, depth, on_anchor)
        };
        self.body.push('\n');
        self.lines += 1;
    }

    fn class(&mut self, name: &str) -> Result<(), DecompileError> {
        let flags = self.flags;
        let is_enum = flags & ENUM != 0;
        let mut enumeration = is_enum.then(|| Enumeration::recover(self)).transpose()?;
        let is_interface = flags & INTERFACE != 0;
        let is_annotation = flags & ANNOTATION != 0;
        let components = self.class.record_components()?;
        let permitted = self.class.permitted_subclasses()?;
        self.class_deprecation(0)?;
        if self.depth == 0
            && self
                .names
                .renames()
                .simple_class_alias(self.owner)
                .is_some()
        {
            self.line(
                0,
                &format!("// $VF: renamed from: {}", self.owner.replace('/', ".")),
            );
        }
        self.sourcefile_comment()?;
        self.javadoc(0, JavadocTarget::Class(self.class));
        self.class_annotations(0)?;

        let mut head = Document::new();
        visibility(&mut head, flags);
        if !is_enum && !is_interface && components.is_none() {
            modifier(&mut head, flags, ABSTRACT, "abstract ");
        }
        if self.depth != 0 && !is_enum && !is_interface && components.is_none() {
            modifier(&mut head, flags, STATIC, "static ");
        }
        if !is_enum && !is_interface && components.is_none() {
            modifier(&mut head, flags, FINAL, "final ");
        }
        modifier(&mut head, flags, STRICT, "strictfp ");
        if !is_enum && !permitted.is_empty() {
            head.push_str("sealed ");
        } else if !is_enum
            && flags & FINAL == 0
            && components.is_none()
            && crate::hierarchy::is_permitted_subclass(
                self.group,
                self.options,
                self.class,
                self.owner,
            )?
        {
            head.push_str("non-sealed ");
        }
        head.push_str(
            match (is_enum, is_annotation, is_interface, components.is_some()) {
                (true, _, _, _) => "enum ",
                (_, true, _, _) => "@interface ",
                (_, _, true, _) => "interface ",
                (_, _, _, true) => "record ",
                _ => "class ",
            },
        );
        if self.options.dump_text_tokens {
            head.token(
                name,
                Token {
                    declaration: true,
                    kind: TokenKind::Class {
                        name: self.owner.into(),
                    },
                },
            );
        } else {
            head.push_str(name);
        }
        let sig = if self.options.decompile_generics {
            self.class
                .signature()?
                .map(|sig| parse(sig, ClassSignature::parse))
                .transpose()?
        } else {
            None
        };
        let pool = &self.class.pool;
        let mut annotations = self.class.type_annotations(true)?;
        annotations.extend(self.class.type_annotations(false)?);
        if let Some(sig) = &sig {
            self.type_parameters(
                &mut head,
                &sig.type_parameters,
                &annotations,
                TypeTarget::ClassTypeParameter,
            )?;
        }
        if let Some(components) = &components {
            head.append(Document::record(
                self.depth,
                self.record_components_source(components)?,
            ));
        }
        if components.is_none()
            && !is_enum
            && !is_interface
            && self.class.super_class != 0
            && self.class.pool.class_name(self.class.super_class)? != "java/lang/Object"
        {
            head.push_str(" extends ");
            let target = TypeTarget::Supertype(Supertype::Superclass);
            let ty = if let Some(sig) = &sig {
                self.render_type_target(&sig.superclass, &annotations, target, &[], false)?
            } else {
                let ty = Type::Object(pool.class_name(self.class.super_class)?.into());
                self.render_type_target(&ty, &annotations, target, &[], false)?
            };
            head.append(ty);
        }
        if !is_annotation && !self.class.interfaces.is_empty() {
            head.push_str(if is_interface {
                " extends "
            } else {
                " implements "
            });
            for (index, &interface) in self.class.interfaces.iter().enumerate() {
                if index != 0 {
                    head.push_str(", ");
                }
                let target = TypeTarget::Supertype(Supertype::Interface(index as u16));
                let ty = if let Some(interface) =
                    sig.as_ref().and_then(|sig| sig.interfaces.get(index))
                {
                    self.render_type_target(interface, &annotations, target, &[], false)?
                } else {
                    let ty = Type::Object(pool.class_name(interface)?.into());
                    self.render_type_target(&ty, &annotations, target, &[], false)?
                };
                head.append(ty);
            }
        }
        if !is_enum && !permitted.is_empty() {
            head.push_str(" permits ");
            for (index, &class) in permitted.iter().enumerate() {
                if index != 0 {
                    head.push_str(", ");
                }
                let name = pool.class_name(class)?;
                symbols::append_class(
                    &mut head,
                    &self.names.render(name),
                    name,
                    self.options.dump_text_tokens,
                );
            }
        }
        self.append_local_synthetic_mark(&mut head);
        head.push_str(" {");
        self.document_line(0, &head);

        let mut needs_gap = false;
        let emit_fields = self.options.method_to_decompile.is_empty();
        let enum_offsets = if let Some(info) = enumeration.as_mut().filter(|_| emit_fields) {
            needs_gap = true;
            self.emit_enum_constants(info)?
        } else {
            BTreeMap::new()
        };
        let mut wrote_field = false;
        let mut initializers =
            self.field_initializers(emit_fields, is_enum || components.is_some())?;
        for field in self.class.fields.iter().filter(|_| emit_fields) {
            let pool = &self.class.pool;
            if self.has_lexical_owner() {
                let name = pool.utf8(field.name_index)?;
                let descriptor = pool.utf8(field.descriptor_index)?;
                if self
                    .group
                    .outer_field(self.owner, name, descriptor)
                    .is_some()
                    || self.anonymous_bindings.as_deref().is_some_and(|bindings| {
                        bindings.captures_field(self.owner, name, descriptor)
                    })
                {
                    continue;
                }
            }
            if let Some(info) = &enumeration {
                let name = self.class.pool.utf8(field.name_index)?;
                if info.hides_field(field, name) {
                    continue;
                }
            }
            if !self.hidden_field(field)?
                && !self.is_component_field(field, components.as_deref())?
            {
                if is_enum && !wrote_field {
                    self.line(0, "");
                }
                let source_line =
                    self.field(field, is_interface, initializers.expression(field))?;
                initializers.record_line(field, source_line);
                wrote_field = true;
                needs_gap = true;
            }
        }
        let mut constructors = 0;
        for method in &self.class.methods {
            let pool = &self.class.pool;
            if pool.utf8(method.name_index)? == "<init>"
                && !enumeration.as_ref().is_some_and(|enumeration| {
                    pool.utf8(method.descriptor_index).is_ok_and(|descriptor| {
                        enumeration.hides_method(self.owner, "<init>", descriptor, method)
                    })
                })
            {
                constructors += 1;
            }
        }
        self.write_methods(
            name,
            components.as_deref(),
            enumeration.as_ref(),
            constructors,
            &mut needs_gap,
            &initializers,
        )?;
        initializers.finish(self)?;
        if let Some(info) = enumeration {
            self.finish_enum_initializer_map(info, enum_offsets);
        }
        self.member_classes(needs_gap)?;
        self.line(0, "}");
        Ok(())
    }

    fn assertion_guard(&self) -> Option<&'c Guard<'c>> {
        self.assertion_guards.get(self.owner)
    }

    fn hidden_field(&self, field: &Member<'a>) -> Result<bool, DecompileError> {
        if is_guard_field(self.class, field) {
            let pool = &self.class.pool;
            let name = pool.utf8(field.name_index)?;
            let descriptor = pool.utf8(field.descriptor_index)?;
            Ok(self
                .assertion_guard()
                .is_some_and(|guard| guard.hides_field(name, descriptor)))
        } else {
            self.hidden(field)
        }
    }

    fn hidden(&self, member: &Member<'a>) -> Result<bool, DecompileError> {
        let pool = &self.class.pool;
        let name = pool.utf8(member.name_index)?;
        if name.starts_with("$SWITCH_TABLE$") || name.starts_with("$SwitchMap$") {
            let descriptor = pool.utf8(member.descriptor_index)?;
            if let Some(consumed) = self
                .group
                .enum_switches()
                .member_visibility(self.owner, name, descriptor)
            {
                return Ok(consumed
                    && (self.options.decompile_inner || name.starts_with("$SWITCH_TABLE$")));
            }
        }
        Ok(self.options.remove_synthetic
            && (member.access_flags & SYNTHETIC != 0
                || find_attribute(&member.attributes, &self.class.pool, "Synthetic")?.is_some()))
    }

    fn field(
        &mut self,
        field: &Member<'a>,
        is_interface: bool,
        initializer: Option<&Document>,
    ) -> Result<usize, DecompileError> {
        let pool = &self.class.pool;
        let descriptor = pool.utf8(field.descriptor_index)?;
        let ty = parse(descriptor, Type::parse)?;
        let map_name = |name: &str| self.names.render(name);
        let mut out = Document::new();
        let flags = field.access_flags;
        if !is_interface {
            visibility(&mut out, flags);
            modifier(&mut out, flags, STATIC, "static ");
            modifier(&mut out, flags, FINAL, "final ");
        }
        modifier(&mut out, flags, 0x0080, "transient ");
        modifier(&mut out, flags, 0x0040, "volatile ");
        let mut annotations = field.field_type_annotations(pool, true)?;
        annotations.extend(field.field_type_annotations(pool, false)?);
        let mut declarations = field.annotations(pool, true)?;
        declarations.extend(field.annotations(pool, false)?);
        if let Some(signature) = self.member_signature(field)? {
            let ty = parse(signature, FieldSignature::parse)?;
            out.append(self.render_type_target(
                &ty.field_type,
                &annotations,
                TypeTarget::Field,
                &declarations,
                false,
            )?);
        } else {
            out.append(self.render_type_target(
                &ty,
                &annotations,
                TypeTarget::Field,
                &declarations,
                false,
            )?);
        }
        out.push(' ');
        let name = pool.utf8(field.name_index)?;
        let renamed = self
            .names
            .renames()
            .field_alias(self.owner, name, descriptor);
        self.field_symbol(&mut out, renamed.unwrap_or(name), name, descriptor);
        if let Some(value) = find_attribute(&field.attributes, pool, "ConstantValue")? {
            let index = u16::from_be_bytes(
                value
                    .try_into()
                    .map_err(|_| DecompileError::InvalidAttribute("ConstantValue"))?,
            );
            out.push_str(" = ");
            out.push_str(
                &constant_literal_with_options(pool, index, Some(&ty), self.options, map_name)
                    .map_err(|source| DecompileError::Render {
                        context: "constant field initializer",
                        source: Box::new(source),
                    })?,
            );
        } else if let Some(initializer) = initializer {
            out.push_str(" = ");
            out.append_ref(initializer);
        }
        out.push(';');
        self.member_deprecation(1, &field.attributes, &declarations)?;
        if renamed.is_some() {
            let ty = ty.render(|name| name.replace('/', "."));
            self.line(1, &format!("// $VF: renamed from: {name} {ty}"));
        }
        self.javadoc(1, JavadocTarget::Field(self.class, field));
        for annotation in &declarations {
            self.write_annotation(1, annotation)?;
        }
        let source_line = self.lines;
        self.line_with_anonymous(1, &out, None)?;
        Ok(source_line)
    }

    fn member_signature(&self, member: &Member<'a>) -> Result<Option<&str>, ClassError> {
        if self.options.decompile_generics {
            member.signature(&self.class.pool)
        } else {
            Ok(None)
        }
    }

    fn method(
        &mut self,
        class_name: &str,
        method: &Member<'a>,
        components: Option<&[RecordComponent<'a>]>,
        enumeration: Option<&Enumeration<'_>>,
        constructors: usize,
        needs_gap: bool,
        initializers: &initializers::FieldInitializers<'_>,
    ) -> Result<bool, DecompileError> {
        let pool = &self.class.pool;
        let name = pool.utf8(method.name_index)?;
        let descriptor = pool.utf8(method.descriptor_index)?;
        if let Some(info) = enumeration
            && info.hides_method(
                pool.class_name(self.class.this_class)?,
                name,
                descriptor,
                method,
            )
        {
            return Ok(false);
        }
        let ty = parse(descriptor, MethodDescriptor::parse)?;
        let renamed = self
            .names
            .renames()
            .method_alias(self.owner, name, descriptor);
        let code = method.code(pool)?;
        let anonymous_sites = code.as_ref().and_then(|_| self.anonymous_sites());
        let constructor = name == "<init>";
        let initializer = name == "<clinit>";
        let implicit_parameters = if constructor && enumeration.is_some() {
            2
        } else {
            usize::from(
                constructor
                    && self.has_lexical_owner()
                    && self
                        .group
                        .constructor_outer(self.owner, descriptor)
                        .is_some(),
            )
        };
        let captured_parameters = if constructor {
            self.anonymous_bindings.as_deref().map_or(0, |bindings| {
                bindings.local_constructor_capture_count(self.owner, descriptor)
            })
        } else {
            0
        };
        let parameter_end = ty
            .parameters
            .len()
            .checked_sub(captured_parameters)
            .filter(|&end| end >= implicit_parameters)
            .ok_or(DecompileError::InvalidAttribute(
                "captured constructor parameters",
            ))?;
        let visible_parameters = parameter_end - implicit_parameters;
        let names = self.names;
        let map_name = |name: &str| names.render(name);
        let exceptions = method.exceptions(pool)?;
        let flags = method.access_flags;
        let mut compact = false;

        let (parameters, mut lines) = if let Some(code) = &code {
            if flags & (ABSTRACT | NATIVE) != 0 {
                return Err(DecompileError::InvalidAttribute(
                    "Code on abstract or native method",
                ));
            }
            let method_error =
                |source: Box<dyn std::error::Error + Send + Sync>| DecompileError::Method {
                    name: name.into(),
                    descriptor: descriptor.into(),
                    source,
                };
            let mut instructions =
                bytecode::decode(code.bytes).map_err(|source| method_error(Box::new(source)))?;
            if let Some(components) = components
                && record::is_generated(
                    self.class,
                    components,
                    name,
                    descriptor,
                    method,
                    &instructions,
                )?
            {
                return Ok(false);
            }
            let mut machine = Machine::new(self.class, method, code, &ty, self.options, &map_name)
                .map_err(|source| method_error(Box::new(source)))?
                .with_group(self.group);
            if constructor
                && let Some(components) = components
                && let Some(tail) = record::compact_tail(
                    self.class,
                    components,
                    &ty,
                    method,
                    code,
                    &instructions,
                    machine.parameter_names(),
                )?
            {
                compact = true;
                for instruction in &mut instructions[tail] {
                    instruction.opcode = 0x00;
                    instruction.operand = bytecode::Operand::None;
                }
            }
            let guard = self.assertion_guard();
            let prefix = enumeration
                .map(|info| info.method_prefix(self.class, name, descriptor, &instructions))
                .transpose()?
                .unwrap_or(0);
            let implicit_enum_super = constructor && prefix != 0;
            if self.options.idea_notnull {
                crate::idea_notnull::strip_guards(
                    self.class,
                    method,
                    code,
                    &ty,
                    &mut instructions,
                )?;
            }
            let prefix = if initializer {
                prefix + guard.map_or(0, |guard| guard.initializer_prefix(name, descriptor))
            } else {
                prefix
            };
            initializers.strip(name, descriptor, &mut instructions);
            if self.options.decompile_inner {
                crate::lift::qualified_new::mask_guards(
                    self.class, method, self.group, &mut instructions, &code.exceptions,
                )?;
            }
            let uses_subroutines = instructions[prefix..]
                .iter()
                .any(|op| matches!(op.opcode, 0xa8 | 0xa9 | 0xc9));
            if self.options.ignore_invalid_bytecode
                && ty.return_type == Type::Void
                && !uses_subroutines
                && code.exceptions.is_empty()
            {
                ControlFlowGraph::complete_void_tail(&mut instructions);
            }
            let normalized;
            let (instructions, handlers) = if self.options.force_jsr_inline || uses_subroutines {
                if prefix != 0 {
                    instructions.drain(..prefix);
                }
                normalized = Some(
                    crate::legacy::normalize(instructions, code.exceptions.clone(), pool)
                        .map_err(|source| method_error(Box::new(source)))?,
                );
                let code = normalized.as_ref().expect("code was normalized");
                (&code.instructions[..], &code.handlers[..])
            } else {
                normalized = None;
                (&instructions[prefix..], &code.exceptions[..])
            };
            let graph = ControlFlowGraph::build(instructions, handlers)
                .map_err(|source| method_error(Box::new(source)))?;
            if implicit_enum_super {
                machine.mark_initialized_this();
            }
            if uses_subroutines && let Some(normalized) = &normalized {
                machine = machine.with_normalized_offsets(normalized);
            }
            let mut code_annotations = code.type_annotations(pool, true)?;
            code_annotations.extend(code.type_annotations(pool, false)?);
            let render_code_annotation = |ty: type_annotations::RenderType<'_>, site: crate::lift::CodeTypeSite| {
                let mut matching = code_annotations
                    .iter()
                    .filter(|entry| site.matches(&entry.target))
                    .peekable();
                if matching.peek().is_none() {
                    return Ok(None);
                }
                type_annotations::render(
                    &self.type_nesting,
                    ty,
                    matching,
                    |name| self.names.render(name),
                    |annotation| self.annotation_document(annotation, None),
                    false,
                    self.options.dump_text_tokens,
                )
                .map(Some)
                .map_err(|error| crate::lift::LiftError::TypeAnnotation(Box::new(error)))
            };
            if !code_annotations.is_empty() {
                machine.set_code_type_renderer(&render_code_annotation);
            }
            machine.set_member_renames(self.names.renames());
            machine.set_dynamic_helpers(Rc::clone(&self.dynamic_helpers));
            if self.anonymous_bindings.is_some() {
                machine.set_anonymous_bindings(self.anonymous_bindings.clone());
            }
            if let Some(sites) = &anonymous_sites {
                machine.set_anonymous_sites(Rc::clone(sites));
                machine.set_anonymous_source(instructions);
            }
            let parameters = machine.parameter_names().to_vec();
            let assertions = guard
                .map(|guard| Sites::for_method(self.class, method, guard, instructions, &graph))
                .transpose()
                .map_err(|source| method_error(Box::new(source)))?
                .flatten();
            let mut lines = structure_with_assertions(
                instructions,
                &graph,
                machine,
                handlers,
                assertions.as_ref(),
            )
            .map_err(|source| method_error(Box::new(source)))?;
            if uses_subroutines && let Some(code) = normalized {
                for line in &mut lines {
                    line.offsets.retain_mut(|offset| {
                        if let Some(source) = code.source_offset(*offset) {
                            *offset = source;
                            true
                        } else {
                            false
                        }
                    });
                }
            }
            (parameters, lines)
        } else {
            if flags & (ABSTRACT | NATIVE) == 0 {
                return Err(DecompileError::InvalidAttribute(
                    "missing Code on concrete method",
                ));
            }
            (self.parameter_names_without_code(method, &ty)?, Vec::new())
        };
        if parameters.len() != ty.parameters.len() || parameters.len() < implicit_parameters {
            return Err(DecompileError::InvalidAttribute("method parameters"));
        }
        // A no-argument superclass call after prologue statements is the
        // explicit delimiter: dropping it would execute those statements late.
        if constructor
            && enumeration.is_none()
            && (self.options.hide_empty_super || components.is_some())
            && lines
                .first()
                .is_some_and(|line| line.depth == 0 && line.text == "super();")
        {
            lines.remove(0);
        }
        let closing = if lines
            .last()
            .is_some_and(|line| line.depth == 0 && line.text == "return;")
        {
            lines.pop().map(|line| line.offsets)
        } else {
            None
        };
        if initializer {
            if closing.is_none() || lines.iter().any(|line| line.text == "return;") {
                return Err(DecompileError::Unsupported {
                    feature: "static initializer with nonlocal exit",
                });
            }
            if lines.is_empty() {
                return Ok(false);
            }
        }
        let is_interface = self.class.access_flags & INTERFACE != 0;
        let mut head = Document::new();
        if initializer {
            head.push_str("static");
        } else {
            let annotations = self.annotations_of(method)?;
            if constructor
                && self.options.hide_default_constructor
                && constructors == 1
                && visible_parameters == 0
                && exceptions.is_empty()
                && annotations.is_empty()
                && (enumeration.is_some() || flags & VISIBILITY == self.flags & VISIBILITY)
                && lines.is_empty()
            {
                return Ok(false);
            }
            if needs_gap {
                self.line(0, "");
            }
            self.member_deprecation(1, &method.attributes, &annotations)?;
            if renamed.is_some() {
                let java_name = |name: &str| name.replace('/', ".");
                let args = ty
                    .parameters
                    .iter()
                    .map(|param| param.render(java_name))
                    .collect::<Vec<_>>()
                    .join(", ");
                let result = ty.return_type.render(java_name);
                self.line(
                    1,
                    &format!("// $VF: renamed from: {name} ({args}) {result}"),
                );
            }
            self.javadoc(1, JavadocTarget::Method(self.class, method));
            for annotation in &annotations {
                self.write_annotation(1, annotation)?;
            }
            if self.options.override_annotation
                && self.class.major_version >= 49
                && !constructor
                && flags & (PRIVATE | STATIC) == 0
                && !annotations.iter().any(|annotation| {
                    pool.utf8(annotation.type_index).ok() == Some("Ljava/lang/Override;")
                })
                && crate::hierarchy::overrides(
                    self.group,
                    self.options,
                    self.class,
                    self.owner,
                    name,
                    descriptor,
                )?
            {
                self.line(1, "@Override");
            }
            let implicit_private = constructor && enumeration.is_some() && flags & VISIBILITY == PRIVATE;
            if !implicit_private && (!is_interface || flags & PUBLIC == 0) {
                visibility(&mut head, flags);
            }
            if !is_interface {
                modifier(&mut head, flags, ABSTRACT, "abstract ");
            } else if flags & (ABSTRACT | STATIC | PRIVATE) == 0 {
                head.push_str("default ");
            }
            modifier(&mut head, flags, STATIC, "static ");
            modifier(&mut head, flags, FINAL, "final ");
            modifier(&mut head, flags, SYNCHRONIZED, "synchronized ");
            modifier(&mut head, flags, NATIVE, "native ");
            modifier(&mut head, flags, STRICT, "strictfp ");
            // The JVM descriptor was parsed and used to lift the body.
            // An invalid optional Signature supplies no trustworthy type
            // arguments; render the verified erased declaration instead.
            let signature = self
                .member_signature(method)?
                .and_then(|signature| MethodSignature::parse(signature).ok());
            let signature = signature.as_ref().filter(|sig| {
                sig.parameters.len() == parameters.len()
                    || sig.parameters.len() == visible_parameters
            });
            let mut type_annotations = method.method_type_annotations(pool, true)?;
            type_annotations.extend(method.method_type_annotations(pool, false)?);
            if let Some(sig) = signature
                && !sig.type_parameters.is_empty()
            {
                self.type_parameters(
                    &mut head,
                    &sig.type_parameters,
                    &type_annotations,
                    TypeTarget::MethodTypeParameter,
                )?;
                head.push(' ');
            }
            let name_at;
            if constructor {
                name_at = head.len();
                head.push_str(class_name);
            } else {
                let declarations = &annotations;
                let result = if let Some(sig) = signature {
                    self.render_type_target(
                        &sig.return_type,
                        &type_annotations,
                        TypeTarget::MethodReturn,
                        declarations,
                        false,
                    )?
                } else {
                    self.render_type_target(
                        &ty.return_type,
                        &type_annotations,
                        TypeTarget::MethodReturn,
                        declarations,
                        false,
                    )?
                };
                head.append(result);
                head.push(' ');
                name_at = head.len();
                if let Some(renamed) = renamed {
                    head.push_str(renamed);
                } else {
                    head.push_str(&crate::lift::source_method_name(
                        self.class, name, descriptor,
                    ));
                }
            }
            if self.options.dump_text_tokens {
                head.token_at(
                    name_at..head.len(),
                    Token {
                        declaration: true,
                        kind: TokenKind::Method {
                            owner: self.owner.into(),
                            name: name.into(),
                            descriptor: descriptor.into(),
                        },
                    },
                );
            }
            if !compact {
                let mut args = Vec::with_capacity(ty.parameters.len());
                if let Some(receiver) = self.annotated_receiver(&type_annotations, constructor)? {
                    args.push(receiver);
                }
                let annot_visible = method.parameter_annotations(pool, true)?;
                let annot_invisible = method.parameter_annotations(pool, false)?;
                let method_parameters = if self.options.use_method_parameters {
                    method.method_parameters(pool)?
                } else {
                    Vec::new()
                };
                let method_name = name;
                for (index, ((param, slot), parameter_name)) in ty
                    .parameters
                    .iter()
                    .scan(u32::from(flags & STATIC == 0), |slot, param| {
                        let current = *slot;
                        *slot += u32::from(param.slots());
                        Some((param, current))
                    })
                    .zip(parameters)
                    .enumerate()
                    .skip(implicit_parameters)
                    .take(visible_parameters)
                {
                    let mut parameter = Document::new();
                    let mut declarations = Vec::new();
                    for group in [&annot_visible, &annot_invisible] {
                        let selected = if group.len() == visible_parameters {
                            index
                                .checked_sub(implicit_parameters)
                                .and_then(|i| group.get(i))
                        } else {
                            let skip = ty.parameters.len().saturating_sub(group.len());
                            index.checked_sub(skip).and_then(|i| group.get(i))
                        };
                        if let Some(annotations) = selected {
                            for annotation in annotations {
                                parameter.append(self.annotation_document(annotation, None)?);
                                parameter.push_str(" ");
                                declarations.push(annotation.clone());
                            }
                        }
                    }
                    if method_parameters
                        .get(index)
                        .is_some_and(|entry| entry.access_flags & FINAL != 0)
                    {
                        parameter.push_str("final ");
                    }
                    let target = TypeTarget::MethodParameter((index - implicit_parameters) as u8);
                    let varargs = flags & VARARGS != 0 && index + 1 == parameter_end;
                    let rendered = if let Some(sig) = signature {
                        let skip = if sig.parameters.len() == ty.parameters.len() {
                            0
                        } else {
                            implicit_parameters
                        };
                        self.render_type_target(
                            &sig.parameters[index - skip],
                            &type_annotations,
                            target,
                            &declarations,
                            varargs,
                        )?
                    } else {
                        self.render_type_target(
                            param,
                            &type_annotations,
                            target,
                            &declarations,
                            varargs,
                        )?
                    };
                    parameter.append(rendered);
                    parameter.push_str(" ");
                    let start = parameter.len();
                    parameter.push_str(&parameter_name);
                    if self.options.dump_text_tokens {
                        parameter.token_at(
                            start..parameter.len(),
                            Token {
                                declaration: true,
                                kind: TokenKind::Variable {
                                    owner: self.owner.into(),
                                    method: method_name.into(),
                                    descriptor: descriptor.into(),
                                    index: slot,
                                    name: parameter_name,
                                    parameter: true,
                                },
                            },
                        );
                    }
                    args.push(parameter);
                }
                head.append(Document::delimited(self.depth + 1, args));
            }
            let generic_throws = signature.filter(|sig| !sig.throws.is_empty());
            if generic_throws.is_some() || !exceptions.is_empty() {
                head.push_str(" throws ");
                let count = generic_throws.map_or(exceptions.len(), |sig| sig.throws.len());
                for index in 0..count {
                    if index != 0 {
                        head.push_str(", ");
                    }
                    let target = TypeTarget::Throws(index as u16);
                    let rendered = if let Some(sig) = generic_throws {
                        self.render_type_target(
                            &sig.throws[index],
                            &type_annotations,
                            target,
                            &[],
                            false,
                        )?
                    } else {
                        let ty = Type::Object(pool.class_name(exceptions[index])?.into());
                        self.render_type_target(&ty, &type_annotations, target, &[], false)?
                    };
                    head.append(rendered);
                }
            }
            if let Some(default) = method.annotation_default(pool)? {
                head.push_str(" default ");
                head.append(self.annotation_value(&default)?);
            }
        }
        if code.is_some() && initializer && needs_gap {
            self.line(0, "");
        }
        head.push_str(if code.is_some() { " {" } else { ";" });
        self.document_line(1, &head);
        if let Some(code) = &code {
            self.method_body(
                name,
                descriptor,
                code,
                lines,
                closing,
                anonymous_sites.as_ref(),
            )?;
        }
        Ok(true)
    }

    fn method_body(
        &mut self,
        name: &str,
        descriptor: &str,
        code: &Code<'a>,
        lines: Vec<Line>,
        closing: Option<Vec<u32>>,
        anonymous_sites: Option<&crate::lift::AnonymousSites>,
    ) -> Result<(), DecompileError> {
        let line_count = lines.len();
        let mut declarations = self
            .local_declarations(name, descriptor, code, &lines, anonymous_sites)?
            .into_iter()
            .peekable();
        let mapping = self.mapping.is_some();
        let mut offsets = BTreeMap::new();
        let mut closed_block = None;
        let mut previous_depth = None;
        let mut scope_end = None;
        for (index, line) in lines.into_iter().enumerate() {
            if (closed_block == Some(line.depth) && !line.text.starts_with('}'))
                || (line.sequence_boundary && previous_depth == Some(line.depth))
            {
                self.line(0, "");
            }
            if let Some(end) = declarations
                .peek()
                .and_then(|declaration| declaration.scope_at(index))
            {
                self.line(2 + line.depth, "{");
                scope_end = Some(end);
            }
            let depth = line.depth + usize::from(scope_end.is_some());
            self.write_local_declarations(index, depth, true, &mut declarations)?;
            closed_block =
                (line.text == "}" || line.text.starts_with("} while ")).then_some(line.depth);
            previous_depth = Some(line.depth);
            let start = self.lines;
            let depth = 2 + depth;
            if line.text.contains('\0') {
                self.line_with_anonymous(depth, &line.text, anonymous_sites)?;
            } else {
                self.document_line_with_anchors(depth, &line.text, |range, line| {
                    if mapping {
                        for offset in range {
                            offsets.entry(offset).or_insert(start + line);
                        }
                    }
                });
            }
            if mapping {
                for offset in line.offsets {
                    offsets.entry(offset).or_insert(start);
                }
                for offset in line.text.omitted_bytecode().flatten() {
                    offsets.remove(&offset);
                }
            }
            if scope_end == Some(index + 1) {
                self.line(2 + line.depth, "}");
                closed_block = Some(line.depth);
                scope_end = None;
            }
        }
        self.write_local_declarations(line_count, 0, false, &mut declarations)?;
        let source_free = line_count == 0 && closing.as_ref().is_some_and(Vec::is_empty);
        if mapping && let Some(closing) = closing {
            for offset in closing {
                offsets.entry(offset).or_insert(self.lines);
            }
        }
        self.line(1, "}");
        if !source_free && let Some(mapping) = &mut self.mapping {
            let original = code.line_numbers(&self.class.pool)?;
            mapping.add(
                MethodMap {
                    class_name: self.owner.into(),
                    name: self
                        .names
                        .renames()
                        .method_alias(self.owner, name, descriptor)
                        .unwrap_or(name)
                        .into(),
                    descriptor: descriptor.into(),
                    offsets,
                },
                original,
            );
        }
        Ok(())
    }

    fn parameter_names_without_code(
        &self,
        method: &Member<'a>,
        desc: &MethodDescriptor,
    ) -> Result<Vec<String>, DecompileError> {
        let params = if self.options.use_method_parameters {
            method.method_parameters(&self.class.pool)?
        } else {
            Vec::new()
        };
        let mut slot = u16::from(method.access_flags & STATIC == 0);
        desc.parameters
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                let name = match params.get(index) {
                    Some(param) if param.name_index != 0 => {
                        self.class.pool.utf8(param.name_index)?.into()
                    }
                    _ => format!("var{slot}"),
                };
                slot += ty.slots();
                Ok(name)
            })
            .collect()
    }
}

fn parse<T>(
    input: &str,
    parser: impl FnOnce(&str) -> Result<T, DescriptorError>,
) -> Result<T, DecompileError> {
    parser(input).map_err(|source| DecompileError::Descriptor {
        input: input.into(),
        source,
    })
}

fn visibility(out: &mut Document, flags: u16) {
    out.push_str(match flags & VISIBILITY {
        PUBLIC => "public ",
        PRIVATE => "private ",
        PROTECTED => "protected ",
        _ => "",
    });
}

fn modifier(out: &mut Document, flags: u16, mask: u16, text: &'static str) {
    if flags & mask != 0 {
        out.push_str(text);
    }
}
