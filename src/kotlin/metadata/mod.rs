// SPDX-License-Identifier: Apache-2.0

//! Parse the Kotlin JVM metadata annotation without binding declarations
//! to fields or methods of the owning class.

use prost::Message;

use crate::structs::{
    StructClass,
    attr::{AnnotationData, ElementValue},
    consts::ConstantValue,
};
use crate::util::java_str::{self, JavaString};

mod bit_encoding;
pub mod flags;
mod names;
pub mod proto;
mod wire_checks;

pub use bit_encoding::decode_bytes;
pub use names::{NameResolver, ResolveError};
use wire_checks::CheckWire;

const ANNOTATION: &str = "kotlin/Metadata";
const FUNCTION_REFERENCE: &str = "kotlin/jvm/internal/FunctionReferenceImpl";

/// A class selected for Kotlin decompilation, metadata export, or both.
/// KotlinChooser selects on annotation presence even if parsing fails.
#[derive(Clone, Copy, Debug)]
pub struct Selection<'a> {
    pub decompile: bool,
    pub annotation: &'a AnnotationData,
}

pub fn select(
    class: &StructClass,
    decompile: bool,
    export_metadata: bool,
) -> Option<Selection<'_>> {
    if !decompile && !export_metadata {
        return None;
    }
    metadata_annotation(class).map(|annotation| Selection {
        decompile,
        annotation,
    })
}

pub fn metadata_annotation(class: &StructClass) -> Option<&AnnotationData> {
    [
        &class.attributes.runtime_visible_annotations,
        &class.attributes.runtime_invisible_annotations,
    ]
    .into_iter()
    .flatten()
    .flat_map(|attribute| &attribute.annotations)
    .find(|annotation| annotation.class_name == ANNOTATION)
}

#[derive(Clone, Debug)]
pub struct Metadata {
    pub header: Header,
    pub payload: Payload,
    pub names: Option<NameResolver>,
    pub warnings: Vec<Warning>,
}

#[derive(Clone, Debug)]
pub struct Header {
    pub kind: i32,
    pub metadata_version: Option<Vec<i32>>,
    pub bytecode_version: Option<Vec<i32>>,
    pub extra_flags: Option<i32>,
    pub package_name: Option<JavaString>,
    pub extra_string: Option<JavaString>,
}

#[derive(Clone, Debug)]
pub enum Payload {
    Class(Box<proto::Class>),
    File(Box<proto::Package>),
    Synthetic(Box<proto::Function>),
    MultifileFacade(Vec<JavaString>),
    MultifilePart {
        package: Box<proto::Package>,
        facade: JavaString,
    },
    FunctionReference,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Warning {
    MissingStrings,
    MissingFacade,
    MissingDataAssumingFunctionReference,
}

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("Kotlin metadata has no kind (k)")]
    MissingKind,
    #[error("Kotlin metadata has no data (d1)")]
    MissingData,
    #[error("Kotlin metadata field {0} has the wrong annotation element type")]
    AnnotationType(&'static str),
    #[error("Kotlin metadata has an empty delimited string table")]
    MissingStringTable,
    #[error("Kotlin metadata has no multifile facade name")]
    MissingFacade,
    #[error("invalid Kotlin metadata {section}")]
    Wire {
        section: &'static str,
        #[source]
        cause: prost::DecodeError,
    },
    #[error("Kotlin metadata {section} is missing required field {field}")]
    Required {
        section: &'static str,
        field: &'static str,
    },
}

/// Read raw class metadata independently of the chooser options and of JVM
/// member binding. Classes without an annotation and unsupported kinds
/// have no payload.
pub fn parse(class: &StructClass) -> Result<Option<Metadata>, ParseError> {
    let Some(annotation) = metadata_annotation(class) else {
        return Ok(None);
    };
    parse_annotation(class, annotation)
}

/// Parse the annotation returned by `select`.
pub fn parse_annotation(
    class: &StructClass,
    annotation: &AnnotationData,
) -> Result<Option<Metadata>, ParseError> {
    let field = |name: &str| {
        let index = annotation
            .par_names
            .iter()
            .position(|entry| entry == name)?;
        annotation.par_values.get(index).map(|entry| &entry.value)
    };
    let kind = field("k").ok_or(ParseError::MissingKind)?;
    let kind = integer(kind).ok_or(ParseError::AnnotationType("k"))?;
    let header = Header {
        kind,
        metadata_version: field("mv").and_then(integer_array),
        bytecode_version: field("bv").and_then(integer_array),
        extra_flags: field("xi").and_then(integer),
        package_name: field("pn").and_then(string).cloned(),
        extra_string: field("xs").and_then(string).cloned(),
    };
    let Some(data) = field("d1") else {
        if class
            .super_class
            .as_ref()
            .is_some_and(|parent| parent.get_string() == FUNCTION_REFERENCE)
        {
            return Ok(Some(Metadata {
                header,
                payload: Payload::FunctionReference,
                names: None,
                warnings: vec![Warning::MissingDataAssumingFunctionReference],
            }));
        }
        return Err(ParseError::MissingData);
    };

    let data = string_array(data).ok_or(ParseError::AnnotationType("d1"))?;
    let bytes = decode_bytes(&data);
    let mut input = bytes.as_slice();
    let mut warnings = Vec::new();
    let names = if let Some(strings) = field("d2") {
        let strings = string_array(strings).ok_or(ParseError::AnnotationType("d2"))?;
        let table = read_string_table(&mut input)?;
        Some(NameResolver::new(table, strings))
    } else {
        warnings.push(Warning::MissingStrings);
        None
    };

    let payload = match kind {
        1 => Payload::Class(Box::new(decode(input, "class")?)),
        2 => Payload::File(Box::new(decode(input, "package")?)),
        3 => Payload::Synthetic(Box::new(decode(input, "synthetic function")?)),
        4 => Payload::MultifileFacade(data),
        5 => {
            let package = Box::new(decode(input, "multifile package")?);
            let facade = match field("xs") {
                Some(value) => string(value)
                    .cloned()
                    .ok_or(ParseError::AnnotationType("xs"))?,
                None => {
                    warnings.push(Warning::MissingFacade);
                    let parts = java_str::split(&class.qualified_name, "__");
                    (*parts.first().ok_or(ParseError::MissingFacade)?).into()
                }
            };
            Payload::MultifilePart { package, facade }
        }
        _ => return Ok(None),
    };
    Ok(Some(Metadata {
        header,
        payload,
        names,
        warnings,
    }))
}

fn read_string_table(input: &mut &[u8]) -> Result<proto::jvm::StringTableTypes, ParseError> {
    const SECTION: &str = "string table";
    if input.is_empty() {
        return Err(ParseError::MissingStringTable);
    }
    let length = prost::decode_length_delimiter(&mut *input).map_err(|cause| ParseError::Wire {
        section: SECTION,
        cause,
    })?;
    // Java reads the size into an int32 and limits the underlying stream to
    // that many bytes. EOF can terminate a complete message within the limit.
    let length = ((length as i32).max(0) as usize).min(input.len());
    let (table, remaining) = input.split_at(length);
    *input = remaining;
    decode(table, SECTION)
}

fn decode<T: Default + Message + CheckWire>(
    input: &[u8],
    section: &'static str,
) -> Result<T, ParseError> {
    let mut data = T::decode(input).map_err(|cause| ParseError::Wire { section, cause })?;
    data.check_wire()
        .map_err(|field| ParseError::Required { section, field })?;
    Ok(data)
}

fn integer(value: &ElementValue) -> Option<i32> {
    match value {
        ElementValue::Const {
            value: ConstantValue::Integer(number),
            ..
        } => Some(*number),
        _ => None,
    }
}

fn string(value: &ElementValue) -> Option<&JavaString> {
    match value {
        ElementValue::Const {
            value: ConstantValue::String(string),
            ..
        } => Some(string),
        _ => None,
    }
}

fn string_array(value: &ElementValue) -> Option<Vec<JavaString>> {
    let ElementValue::Array(elements) = value else {
        return None;
    };
    elements
        .iter()
        .map(|element| string(&element.value).cloned())
        .collect()
}

fn integer_array(value: &ElementValue) -> Option<Vec<i32>> {
    let ElementValue::Array(elements) = value else {
        return None;
    };
    elements
        .iter()
        .map(|element| integer(&element.value))
        .collect()
}
