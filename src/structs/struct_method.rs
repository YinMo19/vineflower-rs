// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.StructMethod`.
//!
//! Upstream decodes a method's bytecode into the method object on
//! `expandData` and drops it on `releaseResources`. A loaded method is
//! immutable here, so [`StructMethod::expand_data`] returns the decoded
//! sequence to the caller, who simply lets go of it when done. The decoder
//! itself is `code::bytecode_parser`.
/*
  method_info {
    u2 access_flags;
    u2 name_index;
    u2 descriptor_index;
    u2 attributes_count;
    attribute_info attributes[attributes_count];
  }
*/

use std::fmt;
use std::io;
use std::sync::{Arc, Mutex};

use arcstr::ArcStr;

use super::attr::StructLocalVariableTableAttribute;
use super::consts::{self, ConstantPool};
use super::struct_class::StructClass;
use super::struct_member::{
    Attributes, ClassReadContext, StructMember, read_attributes_with_context,
};
use crate::code::bytecode_parser::parse_bytecode;
use crate::code::{BytecodeVersion, FullInstructionSequence};
use crate::decompiler::vars::naming::VariableNamer;
use crate::engine::Options;
use crate::engine::counter_container::ExpressionIds;
use crate::types::{GenericMethodDescriptor, SharedSignature, generic_main};
use crate::util::data_input::DataInputFullStream;

pub struct StructMethod {
    pub access_flags: i32,
    pub attributes: Attributes,
    pub name: ArcStr,
    pub descriptor: ArcStr,
    pub bytecode_version: BytecodeVersion,
    /// `max_locals`, or -1 for a method without code.
    pub local_variables: i32,
    code_and_exceptions: Option<Vec<u8>>,
    pub class_qualified_name: ArcStr,
    signature: Option<Arc<SharedSignature<GenericMethodDescriptor>>>,
    variable_namer: Mutex<Option<VariableNamer>>,
}

impl StructMethod {
    pub fn create(
        input: &mut DataInputFullStream<'_>,
        pool: &ConstantPool,
        cl_qualified_name: &ArcStr,
        bytecode_version: BytecodeVersion,
        own: bool,
        options: &Options,
    ) -> io::Result<StructMethod> {
        Self::create_with_context(
            input,
            pool,
            cl_qualified_name,
            bytecode_version,
            own,
            ClassReadContext {
                options,
                ids: &ExpressionIds::default(),
            },
        )
    }

    pub(super) fn create_with_context(
        input: &mut DataInputFullStream<'_>,
        pool: &ConstantPool,
        cl_qualified_name: &ArcStr,
        bytecode_version: BytecodeVersion,
        own: bool,
        context: ClassReadContext<'_>,
    ) -> io::Result<StructMethod> {
        let access_flags = input.read_unsigned_short()?;
        let name_index = input.read_unsigned_short()?;
        let descriptor_index = input.read_unsigned_short()?;

        let (name, descriptor) = pool.get_class_element(
            consts::METHOD,
            cl_qualified_name,
            name_index,
            descriptor_index,
        );
        let mut attributes =
            read_attributes_with_context(input, pool, own, bytecode_version, context)?;
        let code = attributes.code.take().map(|code| {
            attributes.put_all(*code.code_attributes);
            (code.local_variables, code.code_and_exception_data)
        });

        let signature = attributes
            .signature
            .as_ref()
            .filter(|_| context.options.decompile_generics)
            .and_then(|attr| generic_main::parse_method_signature(&attr.signature))
            .map(SharedSignature::new);

        let (local_variables, code_and_exceptions) = match code {
            Some((local_variables, code_and_exceptions)) if own => {
                (local_variables, Some(code_and_exceptions))
            }
            _ => (-1, None),
        };

        Ok(StructMethod {
            access_flags,
            attributes,
            name,
            descriptor,
            bytecode_version,
            local_variables,
            code_and_exceptions,
            class_qualified_name: cl_qualified_name.clone(),
            signature,
            variable_namer: Mutex::default(),
        })
    }

    pub(crate) fn with_variable_namer<T>(
        &self,
        options: &Options,
        f: impl FnOnce(&mut VariableNamer) -> T,
    ) -> T {
        let mut guard = self
            .variable_namer
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        f(guard.get_or_insert_with(|| VariableNamer::new(options)))
    }

    /// `expandData(classStruct)` followed by `getInstructionSequence()`: the
    /// decoded bytecode, or `None` for a method without code.
    pub fn expand_data(
        &self,
        class_struct: &StructClass,
    ) -> io::Result<Option<FullInstructionSequence>> {
        self.code_and_exceptions
            .as_deref()
            .map(|code| parse_bytecode(code, &class_struct.pool, self.bytecode_version))
            .transpose()
    }

    pub fn contains_code(&self) -> bool {
        self.code_and_exceptions.is_some()
    }

    pub fn get_local_variable_attr(&self) -> Option<&StructLocalVariableTableAttribute> {
        self.attributes.local_variable_table.as_ref()
    }

    /// `getSignature()`: the generic signature of the method as it is now.
    pub fn signature(&self) -> Option<Arc<GenericMethodDescriptor>> {
        self.signature.as_ref().map(|signature| signature.get())
    }

    /// The cell behind [`signature`](Self::signature), for verifying it and
    /// for descriptors that must see later corrections.
    pub fn shared_signature(&self) -> Option<&Arc<SharedSignature<GenericMethodDescriptor>>> {
        self.signature.as_ref()
    }
}

impl StructMember for StructMethod {
    fn access_flags(&self) -> i32 {
        self.access_flags
    }

    fn attributes(&self) -> &Attributes {
        &self.attributes
    }
}

impl fmt::Display for StructMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name, self.descriptor)
    }
}
