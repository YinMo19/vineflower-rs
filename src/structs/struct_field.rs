//! `struct.StructField` and `struct.StructRecordComponent`.
/*
  field_info {
    u2 access_flags;
    u2 name_index;
    u2 descriptor_index;
    u2 attributes_count;
    attribute_info attributes[attributes_count];
   }

  record_component_info {
    u2 name_index;
    u2 descriptor_index;
    u2 attributes_count;
    attribute_info attributes[attributes_count];
   }
*/

use std::fmt;
use std::io;
use std::sync::Arc;

use arcstr::ArcStr;

use super::consts::{self, ConstantPool, PooledConstant};
use super::struct_member::{
    Attributes, ClassReadContext, StructMember, read_attributes_with_context,
};
use crate::code::BytecodeVersion;
use crate::engine::Options;
use crate::engine::counter_container::ExpressionIds;
use crate::types::{GenericFieldDescriptor, SharedSignature, generic_main};
use crate::util::data_input::DataInputFullStream;

pub struct StructField {
    pub access_flags: i32,
    pub attributes: Attributes,
    pub name: ArcStr,
    pub descriptor: ArcStr,
    signature: Option<Arc<SharedSignature<GenericFieldDescriptor>>>,
    pub version: BytecodeVersion,
}

/// A record component is a field without access flags.
pub type StructRecordComponent = StructField;

impl StructField {
    pub fn create(
        input: &mut DataInputFullStream<'_>,
        pool: &ConstantPool,
        cl_qualified_name: &str,
        version: BytecodeVersion,
        options: &Options,
    ) -> io::Result<StructField> {
        Self::create_with_context(
            input,
            pool,
            cl_qualified_name,
            version,
            ClassReadContext {
                options,
                ids: &ExpressionIds::default(),
            },
        )
    }

    pub(super) fn create_with_context(
        input: &mut DataInputFullStream<'_>,
        pool: &ConstantPool,
        cl_qualified_name: &str,
        version: BytecodeVersion,
        context: ClassReadContext<'_>,
    ) -> io::Result<StructField> {
        let access_flags = input.read_unsigned_short()?;
        let name_index = input.read_unsigned_short()?;
        let descriptor_index = input.read_unsigned_short()?;

        let (name, descriptor) = pool.get_class_element(
            consts::FIELD,
            cl_qualified_name,
            name_index,
            descriptor_index,
        );
        let attributes = read_attributes_with_context(input, pool, true, version, context)?;

        Ok(Self::new(
            access_flags,
            attributes,
            name,
            descriptor,
            version,
            context.options,
        ))
    }

    /// `StructRecordComponent.create`.
    pub fn create_record_component(
        input: &mut DataInputFullStream<'_>,
        pool: &ConstantPool,
        version: BytecodeVersion,
        options: &Options,
    ) -> io::Result<StructRecordComponent> {
        Self::create_record_component_with_context(
            input,
            pool,
            version,
            ClassReadContext {
                options,
                ids: &ExpressionIds::default(),
            },
        )
    }

    pub(super) fn create_record_component_with_context(
        input: &mut DataInputFullStream<'_>,
        pool: &ConstantPool,
        version: BytecodeVersion,
        context: ClassReadContext<'_>,
    ) -> io::Result<StructRecordComponent> {
        let name_index = input.read_unsigned_short()?;
        let descriptor_index = input.read_unsigned_short()?;

        let string_at = |index| match pool.get_constant(index) {
            Some(PooledConstant::Primitive(constant)) => constant.get_string().clone(),
            constant => panic!("{constant:?} cannot be cast to PrimitiveConstant"),
        };
        let name = string_at(name_index);
        let descriptor = string_at(descriptor_index);
        let attributes = read_attributes_with_context(input, pool, true, version, context)?;

        Ok(Self::new(
            0,
            attributes,
            name,
            descriptor,
            version,
            context.options,
        ))
    }

    fn new(
        access_flags: i32,
        attributes: Attributes,
        name: ArcStr,
        descriptor: ArcStr,
        version: BytecodeVersion,
        options: &Options,
    ) -> Self {
        let signature = attributes
            .signature
            .as_ref()
            .filter(|_| options.decompile_generics)
            .and_then(|attr| generic_main::parse_field_signature(&attr.signature))
            .map(SharedSignature::new);

        Self {
            access_flags,
            attributes,
            name,
            descriptor,
            signature,
            version,
        }
    }

    /// `getSignature()`: the generic type of the field as it is now.
    pub fn signature(&self) -> Option<Arc<GenericFieldDescriptor>> {
        self.signature.as_ref().map(|signature| signature.get())
    }

    pub(crate) fn verified_type(
        &self,
        cx: &crate::engine::Cx,
        owner: &super::StructClass,
        erased: &crate::types::VarType,
    ) -> crate::types::VarType {
        if let Some(signature) = self.shared_signature() {
            signature.update(|s| s.verify_type(cx, owner.signature().as_deref(), erased));
            signature.get().ty.clone()
        } else {
            erased.clone()
        }
    }

    /// The cell behind [`signature`](Self::signature), for verifying it.
    pub fn shared_signature(&self) -> Option<&Arc<SharedSignature<GenericFieldDescriptor>>> {
        self.signature.as_ref()
    }
}

impl StructMember for StructField {
    fn access_flags(&self) -> i32 {
        self.access_flags
    }

    fn attributes(&self) -> &Attributes {
        &self.attributes
    }
}

impl fmt::Display for StructField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)
    }
}
