// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::borrow::Cow;

use super::{DescriptorError, Parser, Primitive, append_array_suffix};

const IDENTIFIER_DELIMITERS: &[u8] = b".;[/<>:";
// Unlike array rank, this isn't a JVM limit. Guard recursive type trees and their
// rendering/drops against stack exhaustion when decompiling untrusted inputs.
const MAX_TYPE_ARGUMENT_DEPTH: usize = 256;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum GenericType {
    Primitive(Primitive),
    Class(ClassType),
    Array {
        element: Box<GenericType>,
        dimensions: u8,
    },
    Variable(String),
    Void,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ClassType {
    /// Package-qualified JVM name of the first type in the signature.
    pub internal_name: String,
    pub arguments: Vec<TypeArgument>,
    pub nested: Vec<NestedType>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NestedType {
    pub name: String,
    pub arguments: Vec<TypeArgument>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum TypeArgument {
    Any,
    Exact(GenericType),
    Extends(GenericType),
    Super(GenericType),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypeParameter {
    pub name: String,
    pub class_bound: Option<GenericType>,
    pub interface_bounds: Vec<GenericType>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ClassSignature {
    pub type_parameters: Vec<TypeParameter>,
    pub superclass: GenericType,
    pub interfaces: Vec<GenericType>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct MethodSignature {
    pub type_parameters: Vec<TypeParameter>,
    pub parameters: Vec<GenericType>,
    pub return_type: GenericType,
    pub throws: Vec<GenericType>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FieldSignature {
    pub field_type: GenericType,
}

impl ClassSignature {
    pub fn parse(signature: &str) -> Result<Self, DescriptorError> {
        let mut parser = Parser::new(signature);
        let type_parameters = parse_type_parameters(&mut parser)?;
        let superclass = GenericType::Class(parse_class_type(&mut parser, 0)?);
        let mut interfaces = Vec::new();
        while parser.peek().is_some() {
            interfaces.push(GenericType::Class(parse_class_type(&mut parser, 0)?));
        }
        Ok(Self {
            type_parameters,
            superclass,
            interfaces,
        })
    }
}

impl MethodSignature {
    pub fn parse(signature: &str) -> Result<Self, DescriptorError> {
        let mut parser = Parser::new(signature);
        let type_parameters = parse_type_parameters(&mut parser)?;
        parser.expect(b'(', "'('")?;
        let mut parameters = Vec::new();
        while !parser.consume(b')') {
            parameters.push(parse_java_type(&mut parser, 0)?);
        }
        let return_type = if parser.consume(b'V') {
            GenericType::Void
        } else {
            parse_java_type(&mut parser, 0)?
        };
        let mut throws = Vec::new();
        while parser.consume(b'^') {
            throws.push(match parser.peek() {
                Some(b'L') => GenericType::Class(parse_class_type(&mut parser, 0)?),
                Some(b'T') => parse_type_variable(&mut parser)?,
                _ => return Err(parser.expected("class or type variable after '^'")),
            });
        }
        parser.finish()?;
        Ok(Self {
            type_parameters,
            parameters,
            return_type,
            throws,
        })
    }
}

impl FieldSignature {
    pub fn parse(signature: &str) -> Result<Self, DescriptorError> {
        let mut parser = Parser::new(signature);
        let field_type = parse_reference_type(&mut parser, 0)?;
        parser.finish()?;
        Ok(Self { field_type })
    }
}

impl GenericType {
    /// Renders Java syntax, passing JVM names to `map`. Explicit inner suffixes
    /// are emitted relative to their owner so the owner's arguments stay attached.
    pub fn render(&self, mut map: impl FnMut(&str) -> String) -> String {
        let mut element = self;
        let mut dimensions = 0;
        while let Self::Array {
            element: component,
            dimensions: rank,
        } = element
        {
            element = component;
            dimensions += usize::from(*rank);
        }
        let mut out = match element {
            Self::Primitive(primitive) => primitive.java_name().to_owned(),
            Self::Class(class) => {
                let mut out = map(&class.internal_name);
                class.write_suffix(&mut out, &mut map);
                out
            }
            Self::Variable(name) => name.clone(),
            Self::Void => String::from("void"),
            Self::Array { .. } => unreachable!(),
        };
        append_array_suffix(&mut out, dimensions);
        out
    }

    pub fn is_java_lang_object(&self) -> bool {
        matches!(self, Self::Class(class)
            if class.internal_name == "java/lang/Object"
                && class.arguments.is_empty()
                && class.nested.is_empty())
    }

    fn write_java(&self, out: &mut String, map: &mut dyn FnMut(&str) -> String) {
        match self {
            Self::Primitive(primitive) => out.push_str(primitive.java_name()),
            Self::Class(class) => {
                out.push_str(&map(&class.internal_name));
                class.write_suffix(out, map);
            }
            Self::Array {
                element,
                dimensions,
            } => {
                element.write_java(out, map);
                append_array_suffix(out, usize::from(*dimensions));
            }
            Self::Variable(name) => out.push_str(name),
            Self::Void => out.push_str("void"),
        }
    }
}

impl ClassType {
    /// Returns the erased JVM name, joining explicit inner suffixes with `$`.
    pub fn binary_name(&self) -> Cow<'_, str> {
        if self.nested.is_empty() {
            return Cow::Borrowed(&self.internal_name);
        }
        let length = self.internal_name.len()
            + self
                .nested
                .iter()
                .map(|part| 1 + part.name.len())
                .sum::<usize>();
        let mut name = String::with_capacity(length);
        name.push_str(&self.internal_name);
        for part in &self.nested {
            name.push('$');
            name.push_str(&part.name);
        }
        Cow::Owned(name)
    }

    fn write_suffix(&self, out: &mut String, map: &mut dyn FnMut(&str) -> String) {
        write_type_arguments(&self.arguments, out, map);
        for part in &self.nested {
            out.push('.');
            out.push_str(&part.name);
            write_type_arguments(&part.arguments, out, map);
        }
    }
}

fn write_type_arguments(
    arguments: &[TypeArgument],
    out: &mut String,
    map: &mut dyn FnMut(&str) -> String,
) {
    if arguments.is_empty() {
        return;
    }
    out.push('<');
    for (index, argument) in arguments.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        match argument {
            TypeArgument::Any => out.push('?'),
            TypeArgument::Exact(ty) => ty.write_java(out, map),
            TypeArgument::Extends(ty) => {
                out.push_str("? extends ");
                ty.write_java(out, map);
            }
            TypeArgument::Super(ty) => {
                out.push_str("? super ");
                ty.write_java(out, map);
            }
        }
    }
    out.push('>');
}

impl TypeParameter {
    pub fn render(&self, mut map: impl FnMut(&str) -> String) -> String {
        let mut out = String::new();
        self.write_java(&mut out, &mut map);
        out
    }

    fn write_java(&self, out: &mut String, map: &mut dyn FnMut(&str) -> String) {
        out.push_str(&self.name);
        let class_bound = self
            .class_bound
            .iter()
            .filter(|bound| !bound.is_java_lang_object() || !self.interface_bounds.is_empty());
        let mut bounds = class_bound.chain(self.interface_bounds.iter());
        if let Some(first) = bounds.next() {
            out.push_str(" extends ");
            first.write_java(out, map);
            for bound in bounds {
                out.push_str(" & ");
                bound.write_java(out, map);
            }
        }
    }
}

/// Renders a declaration's generic parameters, including angle brackets if nonempty.
pub fn render_type_parameters(
    parameters: &[TypeParameter],
    mut map: impl FnMut(&str) -> String,
) -> String {
    if parameters.is_empty() {
        return String::new();
    }
    let mut out = String::from("<");
    for (index, parameter) in parameters.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        parameter.write_java(&mut out, &mut map);
    }
    out.push('>');
    out
}

fn parse_type_parameters(parser: &mut Parser<'_>) -> Result<Vec<TypeParameter>, DescriptorError> {
    let mut parameters = Vec::new();
    if !parser.consume(b'<') {
        return Ok(parameters);
    }
    loop {
        let name = parser.identifier(IDENTIFIER_DELIMITERS, "type parameter name")?;
        parser.expect(b':', "':' after type parameter name")?;
        let class_bound = if starts_class_bound(parser) {
            Some(parse_reference_type(parser, 0)?)
        } else {
            None
        };
        let mut interface_bounds = Vec::new();
        while parser.consume(b':') {
            interface_bounds.push(parse_reference_type(parser, 0)?);
        }
        parameters.push(TypeParameter {
            name: name.to_owned(),
            class_bound,
            interface_bounds,
        });
        if parser.consume(b'>') {
            return Ok(parameters);
        }
    }
}

fn starts_class_bound(parser: &Parser<'_>) -> bool {
    match parser.peek() {
        Some(b'[') => true,
        // If an omitted bound is followed by a parameter starting in L or T,
        // the following colon belongs to the next parameter, not to a type.
        Some(b'L' | b'T') => {
            let end = parser.identifier_end(IDENTIFIER_DELIMITERS);
            parser.source.as_bytes().get(end) != Some(&b':')
        }
        _ => false,
    }
}

fn parse_java_type(parser: &mut Parser<'_>, depth: usize) -> Result<GenericType, DescriptorError> {
    match parser.primitive() {
        Some(primitive) => Ok(GenericType::Primitive(primitive)),
        None => parse_reference_type(parser, depth),
    }
}

fn parse_reference_type(
    parser: &mut Parser<'_>,
    depth: usize,
) -> Result<GenericType, DescriptorError> {
    if depth > MAX_TYPE_ARGUMENT_DEPTH {
        return Err(DescriptorError::SignatureDepth {
            offset: parser.position,
        });
    }
    match parser.peek() {
        Some(b'L') => Ok(GenericType::Class(parse_class_type(parser, depth)?)),
        Some(b'T') => parse_type_variable(parser),
        Some(b'[') => {
            let dimensions = parser.array_dimensions()?;
            let element = parse_java_type(parser, depth)?;
            Ok(GenericType::Array {
                element: Box::new(element),
                dimensions,
            })
        }
        _ => Err(parser.expected("reference type signature")),
    }
}

fn parse_type_variable(parser: &mut Parser<'_>) -> Result<GenericType, DescriptorError> {
    parser.expect(b'T', "'T' before type variable name")?;
    let name = parser.identifier(IDENTIFIER_DELIMITERS, "type variable name")?;
    parser.expect(b';', "';' after type variable name")?;
    Ok(GenericType::Variable(name.to_owned()))
}

fn parse_class_type(parser: &mut Parser<'_>, depth: usize) -> Result<ClassType, DescriptorError> {
    parser.expect(b'L', "class type signature")?;
    let start = parser.position;
    loop {
        parser.identifier(IDENTIFIER_DELIMITERS, "class name component")?;
        if !parser.consume(b'/') {
            break;
        }
    }
    let internal_name = &parser.source[start..parser.position];
    let arguments = parse_type_arguments(parser, depth)?;
    let mut nested = Vec::new();
    while parser.consume(b'.') {
        let name = parser.identifier(IDENTIFIER_DELIMITERS, "nested class name")?;
        let arguments = parse_type_arguments(parser, depth)?;
        nested.push(NestedType {
            name: name.to_owned(),
            arguments,
        });
    }
    parser.expect(b';', "';' after class type signature")?;
    Ok(ClassType {
        internal_name: internal_name.to_owned(),
        arguments,
        nested,
    })
}

fn parse_type_arguments(
    parser: &mut Parser<'_>,
    depth: usize,
) -> Result<Vec<TypeArgument>, DescriptorError> {
    let mut arguments = Vec::new();
    if !parser.consume(b'<') {
        return Ok(arguments);
    }
    loop {
        arguments.push(if parser.consume(b'*') {
            TypeArgument::Any
        } else if parser.consume(b'+') {
            TypeArgument::Extends(parse_reference_type(parser, depth + 1)?)
        } else if parser.consume(b'-') {
            TypeArgument::Super(parse_reference_type(parser, depth + 1)?)
        } else {
            TypeArgument::Exact(parse_reference_type(parser, depth + 1)?)
        });
        if parser.consume(b'>') {
            return Ok(arguments);
        }
    }
}
