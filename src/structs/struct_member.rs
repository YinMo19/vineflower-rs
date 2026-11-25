// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.StructMember`: what classes, fields and methods have in common —
//! access flags and attributes.
//!
//! Upstream keeps attributes in a map from `Key` to object; here each known
//! attribute is a field of [`Attributes`], named after its
//! `StructGeneralAttribute.ATTRIBUTE_*` key, so `getAttribute(KEY)` is the
//! field and `hasAttribute(KEY)` is `is_some()` on it.

use std::io;

use super::attr::*;
use super::consts::ConstantPool;
use crate::code::BytecodeVersion;
use crate::code::code_constants::ACC_SYNTHETIC;
use crate::engine::Options;
use crate::util::data_input::DataInputFullStream;

macro_rules! attributes {
    ($($field:ident: $ty:ty,)*) => {
        #[derive(Default)]
        pub struct Attributes {
            $(pub $field: Option<$ty>,)*
        }

        impl Attributes {
            /// `Map.putAll`: each attribute `other` has replaces the one here.
            pub fn put_all(&mut self, other: Attributes) {
                $(if other.$field.is_some() {
                    self.$field = other.$field;
                })*
            }
        }
    };
}

attributes! {
    code: StructCodeAttribute,
    inner_classes: StructInnerClassesAttribute,
    signature: StructGenericSignatureAttribute,
    annotation_default: StructAnnDefaultAttribute,
    exceptions: StructExceptionsAttribute,
    enclosing_method: StructEnclosingMethodAttribute,
    runtime_visible_annotations: StructAnnotationAttribute,
    runtime_invisible_annotations: StructAnnotationAttribute,
    runtime_visible_parameter_annotations: StructAnnotationParameterAttribute,
    runtime_invisible_parameter_annotations: StructAnnotationParameterAttribute,
    runtime_visible_type_annotations: StructTypeAnnotationAttribute,
    runtime_invisible_type_annotations: StructTypeAnnotationAttribute,
    local_variable_table: StructLocalVariableTableAttribute,
    local_variable_type_table: StructLocalVariableTypeTableAttribute,
    constant_value: StructConstantValueAttribute,
    bootstrap_methods: StructBootstrapMethodsAttribute,
    synthetic: StructGeneralAttribute,
    deprecated: StructGeneralAttribute,
    line_number_table: StructLineNumberTableAttribute,
    method_parameters: StructMethodParametersAttribute,
    module: StructModuleAttribute,
    record: StructRecordAttribute,
    permitted_subclasses: StructPermittedSubclassesAttribute,
    source_file: StructSourceFileAttribute,
    nest_host: StructNestHostAttribute,
}

pub trait StructMember {
    fn access_flags(&self) -> i32;

    fn attributes(&self) -> &Attributes;

    fn has_modifier(&self, modifier: i32) -> bool {
        (self.access_flags() & modifier) == modifier
    }

    fn is_synthetic(&self) -> bool {
        self.has_modifier(ACC_SYNTHETIC) || self.attributes().synthetic.is_some()
    }
}

/// `StructMember.readAttributes`: an attribute table. As upstream, each
/// attribute is read straight from the stream, whatever length it declares;
/// only the attributes that are not read are skipped by their length.
pub fn read_attributes(
    input: &mut DataInputFullStream<'_>,
    pool: &ConstantPool,
    read_code: bool,
    version: BytecodeVersion,
    options: &Options,
) -> io::Result<Attributes> {
    let mut attributes = Attributes::default();

    let length = input.read_unsigned_short()?;
    for _ in 0..length {
        let name_index = input.read_unsigned_short()?;
        let name = pool
            .get_primitive_constant(name_index)
            .unwrap()
            .get_string()
            .clone();
        let att_length = input.read_int()?;

        match name.as_str() {
            "Code" if read_code => {
                attributes.code = Some(StructCodeAttribute::read(input, pool, version, options)?);
            }
            "InnerClasses" => {
                attributes.inner_classes = Some(StructInnerClassesAttribute::read(input, pool)?);
            }
            "ConstantValue" => {
                attributes.constant_value = Some(StructConstantValueAttribute::read(input)?);
            }
            "Signature" => {
                attributes.signature = Some(StructGenericSignatureAttribute::read(input, pool)?);
            }
            "AnnotationDefault" => {
                attributes.annotation_default = Some(StructAnnDefaultAttribute::read(input, pool)?);
            }
            "Exceptions" => {
                attributes.exceptions = Some(StructExceptionsAttribute::read(input)?);
            }
            "EnclosingMethod" => {
                attributes.enclosing_method =
                    Some(StructEnclosingMethodAttribute::read(input, pool)?);
            }
            "RuntimeVisibleAnnotations" => {
                attributes.runtime_visible_annotations =
                    Some(StructAnnotationAttribute::read(input, pool)?);
            }
            "RuntimeInvisibleAnnotations" => {
                attributes.runtime_invisible_annotations =
                    Some(StructAnnotationAttribute::read(input, pool)?);
            }
            "RuntimeVisibleParameterAnnotations" => {
                attributes.runtime_visible_parameter_annotations =
                    Some(StructAnnotationParameterAttribute::read(input, pool)?);
            }
            "RuntimeInvisibleParameterAnnotations" => {
                attributes.runtime_invisible_parameter_annotations =
                    Some(StructAnnotationParameterAttribute::read(input, pool)?);
            }
            "RuntimeVisibleTypeAnnotations" => {
                attributes.runtime_visible_type_annotations =
                    Some(StructTypeAnnotationAttribute::read(input, pool)?);
            }
            "RuntimeInvisibleTypeAnnotations" => {
                attributes.runtime_invisible_type_annotations =
                    Some(StructTypeAnnotationAttribute::read(input, pool)?);
            }
            "LocalVariableTable" => {
                // merge all variable tables
                let table = StructLocalVariableTableAttribute::read(input, pool)?;
                match &mut attributes.local_variable_table {
                    Some(merged) => merged.add(table),
                    None => attributes.local_variable_table = Some(table),
                }
            }
            "LocalVariableTypeTable" => {
                // merge all variable tables
                let table = StructLocalVariableTypeTableAttribute::read(input, pool)?;
                match &mut attributes.local_variable_type_table {
                    Some(merged) => merged.add(table),
                    None => attributes.local_variable_type_table = Some(table),
                }
            }
            "BootstrapMethods" => {
                attributes.bootstrap_methods =
                    Some(StructBootstrapMethodsAttribute::read(input, pool)?);
            }
            "Synthetic" => attributes.synthetic = Some(StructGeneralAttribute),
            "Deprecated" => attributes.deprecated = Some(StructGeneralAttribute),
            "LineNumberTable" => {
                attributes.line_number_table = Some(StructLineNumberTableAttribute::read(input)?);
            }
            "MethodParameters" => {
                attributes.method_parameters =
                    Some(StructMethodParametersAttribute::read(input, pool)?);
            }
            "Module" => attributes.module = Some(StructModuleAttribute::read(input, pool)?),
            "Record" => {
                attributes.record =
                    Some(StructRecordAttribute::read(input, pool, version, options)?);
            }
            "PermittedSubclasses" => {
                attributes.permitted_subclasses =
                    Some(StructPermittedSubclassesAttribute::read(input, pool)?);
            }
            "SourceFile" => attributes.source_file = Some(StructSourceFileAttribute::read(input)?),
            "NestHost" => attributes.nest_host = Some(StructNestHostAttribute::read(input)?),
            // Unknown attribute
            _ => input.discard(att_length)?,
        }
    }

    if let (Some(table), Some(type_table)) = (
        &mut attributes.local_variable_table,
        &attributes.local_variable_type_table,
    ) {
        table.merge_signatures(type_table);
    }

    Ok(attributes)
}
