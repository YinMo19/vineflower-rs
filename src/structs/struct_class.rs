// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.StructClass`: a loaded class file.
/*
  class_file {
    u4 magic;
    u2 minor_version;
    u2 major_version;
    u2 constant_pool_count;
    cp_info constant_pool[constant_pool_count-1];
    u2 access_flags;
    u2 this_class;
    u2 super_class;
    u2 interfaces_count;
    u2 interfaces[interfaces_count];
    u2 fields_count;
    field_info fields[fields_count];
    u2 methods_count;
    method_info methods[methods_count];
    u2 attributes_count;
    attribute_info attributes[attributes_count];
  }
*/

use std::fmt;
use std::io;
use std::sync::{Arc, OnceLock};

use arcstr::ArcStr;
use rustc_hash::FxHashSet;

use super::consts::{ConstantPool, PrimitiveConstant};
use super::struct_field::{StructField, StructRecordComponent};
use super::struct_member::{
    Attributes, ClassReadContext, StructMember, read_attributes_with_context,
};
use super::struct_method::StructMethod;
use crate::code::{BytecodeVersion, MethodProperties};
use crate::engine::counter_container::ExpressionIds;
use crate::engine::{Cx, Options};
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::types::{GenericClassDescriptor, GenericsMap, SharedSignature, VarType, generic_main};
use crate::util::data_input::DataInputFullStream;
use crate::util::interpreter_util::make_unique_key;
use crate::util::jhash::JHashMap;
use crate::util::vb_style_collection::VBStyleCollection;

/// For each class and interface a class derives from (by internal name), the
/// type parameters of that supertype mapped to what the class supplies.
pub type GenericHierarchy = JHashMap<ArcStr, Arc<GenericsMap>>;

pub struct StructClass {
    pub access_flags: i32,
    pub attributes: Attributes,
    pub qualified_name: ArcStr,
    pub super_class: Option<PrimitiveConstant>,
    pub own: bool,
    pub version: BytecodeVersion,
    pub interfaces: Vec<i32>,
    pub interface_names: Vec<ArcStr>,
    pub fields: VBStyleCollection<Arc<StructField>, String>,
    pub methods: VBStyleCollection<Arc<StructMethod>, String>,
    signature: Option<Arc<SharedSignature<GenericClassDescriptor>>>,
    pub pool: ConstantPool,
    generic_hierarchy: OnceLock<Arc<GenericHierarchy>>,
    method_properties: OnceLock<Box<[MethodProperties]>>,
}

impl StructClass {
    pub fn create(
        input: &mut DataInputFullStream<'_>,
        own: bool,
        options: &Options,
        interceptor: Option<Arc<PoolInterceptor>>,
    ) -> io::Result<StructClass> {
        Self::create_with_ids(input, own, options, interceptor, &ExpressionIds::default())
    }

    pub(super) fn create_with_ids(
        input: &mut DataInputFullStream<'_>,
        own: bool,
        options: &Options,
        interceptor: Option<Arc<PoolInterceptor>>,
        ids: &ExpressionIds,
    ) -> io::Result<StructClass> {
        let context = ClassReadContext { options, ids };
        input.discard(4)?;
        let minor_version = input.read_unsigned_short()?;
        let major_version = input.read_unsigned_short()?;
        let bytecode_version = BytecodeVersion::new(major_version, minor_version);

        let pool = ConstantPool::new(input, interceptor)?;

        let access_flags = input.read_unsigned_short()?;
        let this_class_idx = input.read_unsigned_short()?;
        let super_class_idx = input.read_unsigned_short()?;
        let qualified_name = pool
            .get_primitive_constant(this_class_idx)
            .unwrap()
            .get_string()
            .clone();
        let super_class = pool.get_primitive_constant(super_class_idx);

        let length = input.read_unsigned_short()?;
        let mut interfaces = Vec::with_capacity(length as usize);
        let mut interface_names = Vec::with_capacity(length as usize);
        for _ in 0..length {
            let interface = input.read_unsigned_short()?;
            interfaces.push(interface);
            interface_names.push(
                pool.get_primitive_constant(interface)
                    .unwrap()
                    .get_string()
                    .clone(),
            );
        }

        let length = input.read_unsigned_short()?;
        let mut fields = VBStyleCollection::with_capacity(length as usize);
        for _ in 0..length {
            let field = StructField::create_with_context(
                input,
                &pool,
                &qualified_name,
                bytecode_version,
                context,
            )?;
            let key = make_unique_key(&field.name, &field.descriptor);
            fields.add_with_key(Arc::new(field), key);
        }

        let length = input.read_unsigned_short()?;
        let mut methods = VBStyleCollection::with_capacity(length as usize);
        for _ in 0..length {
            let method = StructMethod::create_with_context(
                input,
                &pool,
                &qualified_name,
                bytecode_version,
                own,
                context,
            )?;
            let key = make_unique_key(&method.name, &method.descriptor);
            if methods.contains_key(&key) {
                log::warn!(
                    "Duplicate method {qualified_name}.{}{}",
                    method.name,
                    method.descriptor
                );
            }
            methods.add_with_key(Arc::new(method), key);
        }

        let attributes =
            read_attributes_with_context(input, &pool, true, bytecode_version, context)?;

        let signature = attributes
            .signature
            .as_ref()
            .filter(|_| options.decompile_generics)
            .and_then(|attr| generic_main::parse_class_signature(&qualified_name, &attr.signature))
            .map(SharedSignature::new);

        Ok(StructClass {
            access_flags,
            attributes,
            qualified_name,
            super_class,
            own,
            version: bytecode_version,
            interfaces,
            interface_names,
            fields,
            methods,
            signature,
            pool,
            generic_hierarchy: OnceLock::new(),
            method_properties: OnceLock::new(),
        })
    }

    pub fn has_field(&self, name: &str, descriptor: &str) -> bool {
        self.get_field(name, descriptor).is_some()
    }

    pub fn get_field(&self, name: &str, descriptor: &str) -> Option<&Arc<StructField>> {
        self.fields
            .get_with_key(make_unique_key(name, descriptor).as_str())
    }

    /// Bytecode properties computed in declaration order before method simplification.
    pub fn method_properties(&self, key: &str) -> Option<&MethodProperties> {
        let index = self.methods.index_of_key(key)?;
        let entries = self.method_properties.get_or_init(|| {
            self.methods
                .iter()
                .map(|method| MethodProperties::analyze(Arc::clone(method), self))
                .collect()
        });
        Some(&entries[index])
    }

    /// `getMethod(key)`, for a key made by `make_unique_key`.
    pub fn get_method_by_key(&self, key: &str) -> Option<&Arc<StructMethod>> {
        self.methods.get_with_key(key)
    }

    pub fn get_method(&self, name: &str, descriptor: &str) -> Option<&Arc<StructMethod>> {
        self.get_method_by_key(&make_unique_key(name, descriptor))
    }

    /// The method as this class declares or inherits it.
    pub fn get_method_recursive(
        &self,
        cx: &Cx,
        name: &str,
        descriptor: &str,
    ) -> Option<Arc<StructMethod>> {
        if let Some(method) = self.get_method(name, descriptor) {
            return Some(Arc::clone(method));
        }

        let super_name = self.super_class.as_ref().map(PrimitiveConstant::get_string);
        super_name
            .into_iter()
            .chain(&self.interface_names)
            .filter_map(|supertype| cx.classes().get_class(supertype))
            .find_map(|cls| cls.get_method_recursive(cx, name, descriptor))
    }

    pub fn get_interface(&self, i: usize) -> &ArcStr {
        &self.interface_names[i]
    }

    /// The record components; `None` if this class is not a record.
    pub fn get_record_components(&self) -> Option<&[StructRecordComponent]> {
        match &self.attributes.record {
            Some(record_attr) => Some(record_attr.components.as_slice()),
            // If our class extends j.l.Record but also has no components, it's probably malformed.
            // Force processing as a record anyway, in the hopes that we can come to a better result.
            None => self
                .super_class
                .as_ref()
                .is_some_and(|super_class| super_class.get_string() == "java/lang/Record")
                .then_some(&[][..]),
        }
    }

    /// `getSignature()`: the generic signature of the class as it is now.
    pub fn signature(&self) -> Option<Arc<GenericClassDescriptor>> {
        self.signature.as_ref().map(|signature| signature.get())
    }

    /// The cell behind [`signature`](Self::signature), for verifying it.
    pub fn shared_signature(&self) -> Option<&Arc<SharedSignature<GenericClassDescriptor>>> {
        self.signature.as_ref()
    }

    /// The type parameters of this class mapped to the arguments of `ty`, an
    /// instantiation of it.
    fn get_generic_map(&self, ty: Option<&VarType>) -> GenericsMap {
        let mut ret = GenericsMap::new();
        let (Some(signature), Some(ty)) = (self.signature(), ty) else {
            return ret;
        };
        //Invalid instance type?
        if !ty.is_generic() || ty.arguments().len() != signature.fparameters.len() {
            return ret;
        }

        for (fparameter, var) in signature.fparameters.iter().zip(ty.arguments()) {
            if let Some(var) = var {
                ret.insert(VarType::parse(&format!("T{fparameter};")), Some(var.clone()));
            }
        }
        ret
    }

    pub fn get_all_generics(&self, cx: &Cx) -> Arc<GenericHierarchy> {
        Arc::clone(
            self.generic_hierarchy
                .get_or_init(|| Arc::new(self.build_generic_hierarchy(cx))),
        )
    }

    fn build_generic_hierarchy(&self, cx: &Cx) -> GenericHierarchy {
        let signature = self.signature();
        let mut ret = GenericHierarchy::new();

        if let Some(signature) = &signature
            && !signature.fparameters.is_empty()
        {
            let mut mine = GenericsMap::new();
            for par in &signature.fparameters {
                let ty = VarType::parse(&format!("T{par};"));
                mine.insert(ty.clone(), Some(ty));
            }
            ret.insert(self.qualified_name.clone(), Arc::new(mine));
        }

        //Is there a better way? Is the signature forced to contain all interfaces?
        let mut visited = FxHashSet::default();
        if let Some(signature) = &signature {
            for intf in &signature.superinterfaces {
                visited.insert(intf.value.clone());
                let Some(cls) = intf
                    .value
                    .as_deref()
                    .and_then(|name| cx.classes().get_class(name))
                else {
                    continue;
                };
                let sig = cls.get_generic_map(Some(intf));
                add_substituted(&mut ret, &cls.get_all_generics(cx), &sig);
            }
        }

        for intf in &self.interface_names {
            if visited.contains(&Some(intf.clone())) {
                continue;
            }
            if let Some(cls) = cx.classes().get_class(intf) {
                put_all(&mut ret, &cls.get_all_generics(cx));
            }
        }

        if let Some(super_class) = &self.super_class
            && let Some(cls) = cx.classes().get_class(super_class.get_string())
        {
            let sig = cls.get_generic_map(signature.as_ref().map(|signature| &signature.superclass));
            if sig.is_empty() {
                put_all(&mut ret, &cls.get_all_generics(cx));
            } else {
                add_substituted(&mut ret, &cls.get_all_generics(cx), &sig);
            }
        }

        ret
    }
}

fn put_all(ret: &mut GenericHierarchy, other: &GenericHierarchy) {
    ret.put_all(
        other
            .iter()
            .map(|(name, generics)| (name.clone(), Arc::clone(generics))),
        other.len(),
    );
}

/// Adds the hierarchy of a supertype, with the supertype's own type
/// parameters replaced by the arguments in `sig`.
fn add_substituted(ret: &mut GenericHierarchy, hierarchy: &GenericHierarchy, sig: &GenericsMap) {
    for (name, generics) in hierarchy.iter() {
        if generics.is_empty() {
            ret.insert(name.clone(), Arc::clone(generics));
            continue;
        }

        let mut sub = GenericsMap::new();
        for (var, value) in generics.iter() {
            let substituted = value
                .as_ref()
                .and_then(|value| sig.get(value))
                .unwrap_or(value);
            sub.insert(var.clone(), substituted.clone());
        }
        ret.insert(name.clone(), Arc::new(sub));
    }
}

impl StructMember for StructClass {
    fn access_flags(&self) -> i32 {
        self.access_flags
    }

    fn attributes(&self) -> &Attributes {
        &self.attributes
    }
}

impl fmt::Display for StructClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.qualified_name)
    }
}
