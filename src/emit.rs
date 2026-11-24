// Based on Vineflower ClassWriter and ClassesProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
mod annotation;
mod enumeration;
mod initializers;
mod mapping;
mod module;
mod names;
mod record;

pub use mapping::{MethodMap, SourceMap};

use std::{collections::BTreeMap, fmt::Write};

use thiserror::Error;

use crate::{
    Options, bytecode,
    cfg::ControlFlowGraph,
    classfile::{ClassError, ClassFile, Code, Member, RecordComponent, find_attribute},
    descriptor::{
        ClassSignature, DescriptorError, FieldSignature, MethodDescriptor, MethodSignature, Type,
        render_type_parameters,
    },
    lift::{Machine, constant_literal},
    structure::{Line, structure_with_handlers},
};
use enumeration::Enumeration;
use names::{Names, simple};

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
    pub text: String,
    pub map: Option<SourceMap>,
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
    let class = ClassFile::parse(bytes)?;
    let class_name = class.pool.class_name(class.this_class)?;
    let names = Names::new(&class, class_name, options.remove_imports)?;
    let mut writer = Writer {
        class: &class,
        names: &names,
        options,
        body: String::new(),
        lines: 0,
        mapping: options.include_line_mappings.then(SourceMap::default),
    };
    let package = class_name
        .rsplit_once('/')
        .map(|(package, _)| package.replace('/', "."));
    let mut prefix = options.banner.clone();
    match simple(class_name) {
        "module-info" if class.access_flags & MODULE != 0 => {
            writer.module()?;
            let import_start = prefix.len();
            names.imports(&mut prefix);
            if prefix.len() != import_start {
                prefix.push('\n');
            }
        }
        "package-info" => {
            writer.class_annotations(0)?;
            prefix.push_str(&writer.body);
            writer.body.clear();
            if let Some(package) = &package {
                let _ = writeln!(prefix, "package {package};\n");
            }
            names.imports(&mut prefix);
        }
        simple_name => {
            writer.class(simple_name)?;
            if let Some(package) = &package {
                let _ = writeln!(prefix, "package {package};\n");
            }
            let import_start = prefix.len();
            names.imports(&mut prefix);
            if prefix.len() != import_start {
                prefix.push('\n');
            }
        }
    }
    if let Some(mapping) = &mut writer.mapping {
        mapping.shift(prefix.bytes().filter(|&byte| byte == b'\n').count());
    }
    prefix.push_str(&writer.body);
    let mut text = if let Some(mapping) = &writer.mapping
        && options.dump_original_lines
        && !mapping.original_lines.is_empty()
    {
        let mut annotated = String::with_capacity(prefix.len());
        mapping.annotate(&prefix, &mut annotated);
        annotated
    } else {
        prefix
    };
    if let Some(mapping) = &writer.mapping
        && options.unit_test_mode
    {
        mapping.dump(class_name, &options.indent, &mut text);
    }
    if options.crlf {
        text = text.replace('\n', "\r\n");
    }
    Ok(Source {
        class_name: class_name.into(),
        text,
        map: writer.mapping,
    })
}

struct Writer<'a, 'c> {
    class: &'c ClassFile<'a>,
    names: &'c Names<'c>,
    options: &'c Options,
    body: String,
    lines: usize,
    mapping: Option<SourceMap>,
}

impl<'a, 'c> Writer<'a, 'c> {
    fn line(&mut self, depth: usize, text: &str) {
        if !text.is_empty() {
            for _ in 0..depth {
                self.body.push_str(&self.options.indent);
            }
            self.body.push_str(text);
        }
        self.body.push('\n');
        self.lines += 1;
    }

    fn class(&mut self, name: &str) -> Result<(), DecompileError> {
        let flags = self.class.access_flags;
        let is_enum = flags & ENUM != 0;
        let enumeration = is_enum
            .then(|| Enumeration::recover(self.class, self.options.ascii_strings))
            .transpose()?;
        let is_interface = flags & INTERFACE != 0;
        let is_annotation = flags & ANNOTATION != 0;
        let components = self.class.record_components()?;
        let permitted = self.class.permitted_subclasses()?;
        self.class_annotations(0)?;

        let mut head = String::new();
        visibility(&mut head, flags);
        if !is_enum && !is_interface && components.is_none() {
            modifier(&mut head, flags, ABSTRACT, "abstract ");
            modifier(&mut head, flags, FINAL, "final ");
        }
        if !is_enum && !permitted.is_empty() {
            head.push_str("sealed ");
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
        head.push_str(name);
        let sig = if self.options.decompile_generics {
            self.class
                .signature()?
                .map(|sig| parse(sig, ClassSignature::parse))
                .transpose()?
        } else {
            None
        };
        let map_name = |name: &str| self.names.render(name);
        if let Some(sig) = &sig {
            head.push_str(&render_type_parameters(&sig.type_parameters, map_name));
        }
        if let Some(components) = &components {
            self.record_header(&mut head, components)?;
        } else if !is_enum
            && !is_interface
            && self.class.super_class != 0
            && self.class.pool.class_name(self.class.super_class)? != "java/lang/Object"
        {
            head.push_str(" extends ");
            if let Some(sig) = &sig {
                head.push_str(&sig.superclass.render(map_name));
            } else {
                head.push_str(&map_name(
                    self.class.pool.class_name(self.class.super_class)?,
                ));
            }
        }
        if !is_annotation && !self.class.interfaces.is_empty() {
            head.push_str(if is_interface {
                " extends "
            } else {
                " implements "
            });
            if let Some(sig) = &sig {
                comma_list(
                    &mut head,
                    sig.interfaces.iter().map(|iface| iface.render(map_name)),
                );
            } else {
                push_class_list(&mut head, &self.class.interfaces, self.class, &map_name)?;
            }
        }
        if !is_enum && !permitted.is_empty() {
            head.push_str(" permits ");
            push_class_list(&mut head, &permitted, self.class, &map_name)?;
        }
        head.push_str(" {");
        self.line(0, &head);

        let mut needs_gap = false;
        if let Some(info) = &enumeration {
            let declarations = info.declarations();
            for (index, declaration) in declarations.iter().enumerate() {
                let separator = if index + 1 == declarations.len() {
                    ';'
                } else {
                    ','
                };
                self.line(1, &format!("{declaration}{separator}"));
            }
            if declarations.is_empty() {
                self.line(1, ";");
            }
            needs_gap = true;
        }
        let mut wrote_field = false;
        let mut interface_inits = is_interface
            .then(|| self.interface_initializers())
            .transpose()?;
        let mut interface_offsets = BTreeMap::new();
        for field in &self.class.fields {
            if let Some(info) = &enumeration {
                let name = self.class.pool.utf8(field.name_index)?;
                if info.hides_field(field, name) {
                    continue;
                }
            }
            if !self.hidden(field)? && !self.is_component_field(field, components.as_deref())? {
                if is_enum && !wrote_field {
                    self.line(0, "");
                }
                let initializer = if let Some(inits) = &mut interface_inits {
                    inits.values.remove(self.class.pool.utf8(field.name_index)?)
                } else {
                    None
                };
                let source_line = self.field(
                    field,
                    is_interface,
                    initializer.as_ref().map(|init| init.expression.as_str()),
                )?;
                if let Some(init) = initializer {
                    interface_offsets
                        .extend(init.offsets.into_iter().map(|offset| (offset, source_line)));
                }
                wrote_field = true;
                needs_gap = true;
            }
        }
        if let Some(inits) = interface_inits {
            if !inits.values.is_empty() {
                return Err(initializers::unsupported());
            }
            if let Some(mapping) = &mut self.mapping
                && !interface_offsets.is_empty()
            {
                mapping.add(
                    MethodMap {
                        name: "<clinit>".into(),
                        descriptor: "()V".into(),
                        offsets: interface_offsets,
                    },
                    inits.original_lines,
                );
            }
        }
        let mut constructors = 0;
        for method in &self.class.methods {
            constructors += usize::from(self.class.pool.utf8(method.name_index)? == "<init>");
        }
        for method in &self.class.methods {
            if is_interface && self.class.pool.utf8(method.name_index)? == "<clinit>" {
                continue;
            }
            if self.hidden(method)?
                || (self.options.remove_bridge && method.access_flags & BRIDGE != 0)
            {
                continue;
            }
            if self.method(
                name,
                method,
                components.as_deref(),
                enumeration.as_ref(),
                constructors,
                needs_gap,
            )? {
                needs_gap = true;
            }
        }
        self.line(0, "}");
        Ok(())
    }

    fn hidden(&self, member: &Member<'a>) -> Result<bool, DecompileError> {
        Ok(self.options.remove_synthetic
            && (member.access_flags & SYNTHETIC != 0
                || find_attribute(&member.attributes, &self.class.pool, "Synthetic")?.is_some()))
    }

    fn field(
        &mut self,
        field: &Member<'a>,
        is_interface: bool,
        initializer: Option<&str>,
    ) -> Result<usize, DecompileError> {
        let pool = &self.class.pool;
        let descriptor = pool.utf8(field.descriptor_index)?;
        let ty = parse(descriptor, Type::parse)?;
        let map_name = |name: &str| self.names.render(name);
        let mut out = String::new();
        let flags = field.access_flags;
        if !is_interface {
            visibility(&mut out, flags);
            modifier(&mut out, flags, STATIC, "static ");
            modifier(&mut out, flags, FINAL, "final ");
        }
        modifier(&mut out, flags, 0x0080, "transient ");
        modifier(&mut out, flags, 0x0040, "volatile ");
        if let Some(signature) = self.member_signature(field)? {
            out.push_str(
                &parse(signature, FieldSignature::parse)?
                    .field_type
                    .render(map_name),
            );
        } else {
            out.push_str(&ty.render(map_name));
        }
        out.push(' ');
        out.push_str(pool.utf8(field.name_index)?);
        if let Some(value) = find_attribute(&field.attributes, pool, "ConstantValue")? {
            let index = u16::from_be_bytes(
                value
                    .try_into()
                    .map_err(|_| DecompileError::InvalidAttribute("ConstantValue"))?,
            );
            out.push_str(" = ");
            out.push_str(
                &constant_literal(pool, index, Some(&ty), self.options.ascii_strings).map_err(
                    |source| DecompileError::Render {
                        context: "constant field initializer",
                        source: Box::new(source),
                    },
                )?,
            );
        } else if let Some(initializer) = initializer {
            out.push_str(" = ");
            out.push_str(initializer);
        }
        out.push(';');
        self.member_annotations(1, field)?;
        let source_line = self.lines;
        self.line(1, &out);
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
        let code = method.code(pool)?;
        let constructor = name == "<init>";
        let initializer = name == "<clinit>";
        let implicit_parameters = if constructor && enumeration.is_some() {
            2
        } else {
            0
        };
        let names = self.names;
        let map_name = |name: &str| names.render(name);
        let exceptions = method.exceptions(pool)?;
        let flags = method.access_flags;

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
            let instructions =
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
            let prefix = enumeration
                .map(|info| info.method_prefix(self.class, name, descriptor, &instructions))
                .transpose()?
                .unwrap_or(0);
            let instructions = if initializer {
                &instructions[prefix..]
            } else {
                &instructions
            };
            let graph = ControlFlowGraph::build(instructions, &code.exceptions)
                .map_err(|source| method_error(Box::new(source)))?;
            let machine = Machine::new(self.class, method, code, &ty, self.options, &map_name)
                .map_err(|source| method_error(Box::new(source)))?;
            let parameters = machine.parameter_names().to_vec();
            let lines = structure_with_handlers(instructions, &graph, machine, &code.exceptions)
                .map_err(|source| method_error(Box::new(source)))?;
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
        if constructor {
            if enumeration.is_some() {
                if !lines
                    .first()
                    .is_some_and(|line| line.depth == 0 && line.text.starts_with("super("))
                {
                    return Err(DecompileError::Unsupported {
                        feature: "enum constructor has no recoverable super call",
                    });
                }
                lines.remove(0);
            } else if self.options.hide_empty_super
                && lines
                    .first()
                    .is_some_and(|line| line.depth == 0 && line.text == "super();")
            {
                lines.remove(0);
            }
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
        let mut head = String::new();
        if initializer {
            head.push_str("static");
        } else {
            let annotations = self.annotations_of(method)?;
            if constructor
                && self.options.hide_default_constructor
                && constructors == 1
                && ty.parameters.len() == implicit_parameters
                && exceptions.is_empty()
                && annotations.is_empty()
                && (enumeration.is_some()
                    || flags & VISIBILITY == self.class.access_flags & VISIBILITY)
                && lines.is_empty()
            {
                return Ok(false);
            }
            if needs_gap {
                self.line(0, "");
            }
            for annotation in annotations {
                self.line(1, &annotation);
            }
            if !is_interface || flags & PUBLIC == 0 {
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
            let signature = self
                .member_signature(method)?
                .map(|sig| parse(sig, MethodSignature::parse))
                .transpose()?;
            let signature = signature.as_ref().filter(|sig| {
                sig.parameters.len() == parameters.len()
                    || sig.parameters.len() + implicit_parameters == parameters.len()
            });
            if let Some(sig) = signature
                && !sig.type_parameters.is_empty()
            {
                head.push_str(&render_type_parameters(&sig.type_parameters, map_name));
                head.push(' ');
            }
            if constructor {
                head.push_str(class_name);
            } else {
                let result = signature.map_or_else(
                    || ty.return_type.render(map_name),
                    |sig| sig.return_type.render(map_name),
                );
                head.push_str(&result);
                head.push(' ');
                head.push_str(name);
            }
            head.push('(');
            let annot_visible = method.parameter_annotations(pool, true)?;
            let annot_invisible = method.parameter_annotations(pool, false)?;
            for (index, (param, name)) in ty
                .parameters
                .iter()
                .zip(parameters)
                .enumerate()
                .skip(implicit_parameters)
            {
                if index != implicit_parameters {
                    head.push_str(", ");
                }
                for group in [&annot_visible, &annot_invisible] {
                    let skip = ty.parameters.len().saturating_sub(group.len());
                    if let Some(annotations) = index.checked_sub(skip).and_then(|i| group.get(i)) {
                        for annotation in annotations {
                            head.push_str(&self.annotation(annotation)?);
                            head.push(' ');
                        }
                    }
                }
                let rendered = signature.map_or_else(
                    || param.render(map_name),
                    |sig| {
                        let skip = ty.parameters.len() - sig.parameters.len();
                        sig.parameters[index - skip].render(map_name)
                    },
                );
                if flags & VARARGS != 0
                    && index + 1 == ty.parameters.len()
                    && let Some(element) = rendered.strip_suffix("[]")
                {
                    head.push_str(element);
                    head.push_str("...");
                } else {
                    head.push_str(&rendered);
                }
                head.push(' ');
                head.push_str(&name);
            }
            head.push(')');
            let generic_throws = signature.filter(|sig| !sig.throws.is_empty());
            if generic_throws.is_some() || !exceptions.is_empty() {
                head.push_str(" throws ");
                if let Some(sig) = generic_throws {
                    comma_list(
                        &mut head,
                        sig.throws
                            .iter()
                            .map(|exception| exception.render(map_name)),
                    );
                } else {
                    push_class_list(&mut head, &exceptions, self.class, &map_name)?;
                }
            }
            if let Some(default) = method.annotation_default(pool)? {
                head.push_str(" default ");
                head.push_str(&self.annotation_value(&default)?);
            }
        }
        if let Some(code) = &code {
            if initializer && needs_gap {
                self.line(0, "");
            }
            head.push_str(" {");
            self.line(1, &head);
            self.method_body(name, descriptor, code, lines, closing)?;
        } else {
            head.push(';');
            self.line(1, &head);
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
    ) -> Result<(), ClassError> {
        let mapping = self.mapping.is_some();
        let mut offsets = BTreeMap::new();
        let mut closed_block = None;
        for line in lines {
            if closed_block == Some(line.depth) && !line.text.starts_with('}') {
                self.line(0, "");
            }
            closed_block =
                (line.text == "}" || line.text.starts_with("} while ")).then_some(line.depth);
            if mapping {
                for offset in line.offsets {
                    offsets.entry(offset).or_insert(self.lines);
                }
            }
            self.line(2 + line.depth, &line.text);
        }
        if mapping && let Some(closing) = closing {
            for offset in closing {
                offsets.entry(offset).or_insert(self.lines);
            }
        }
        self.line(1, "}");
        if let Some(mapping) = &mut self.mapping {
            let original = code.line_numbers(&self.class.pool)?;
            mapping.add(
                MethodMap {
                    name: name.into(),
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

fn visibility(out: &mut String, flags: u16) {
    out.push_str(match flags & VISIBILITY {
        PUBLIC => "public ",
        PRIVATE => "private ",
        PROTECTED => "protected ",
        _ => "",
    });
}

fn modifier(out: &mut String, flags: u16, mask: u16, text: &'static str) {
    if flags & mask != 0 {
        out.push_str(text);
    }
}

fn comma_list(out: &mut String, items: impl IntoIterator<Item = String>) {
    for (index, item) in items.into_iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        out.push_str(&item);
    }
}

fn push_class_list(
    out: &mut String,
    classes: &[u16],
    class: &ClassFile<'_>,
    map: &dyn Fn(&str) -> String,
) -> Result<(), ClassError> {
    for (index, &class_index) in classes.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        out.push_str(&map(class.pool.class_name(class_index)?));
    }
    Ok(())
}
