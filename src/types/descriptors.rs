// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.gen.FieldDescriptor` and `struct.gen.MethodDescriptor`: parsed
//! field and method descriptors.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use arcstr::ArcStr;

use super::generic_main::{GenericMethodDescriptor, SharedSignature};
use super::var_type::{CodeType, VarType};

/// `NewClassNameBuilder.buildNewClassname`: the new name of a renamed class.
pub trait NewClassNameBuilder {
    fn build_new_classname(&self, class_name: &str) -> Option<String>;
}

#[derive(Clone, Debug)]
pub struct FieldDescriptor {
    pub ty: VarType,
    pub descriptor_string: ArcStr,
}

impl FieldDescriptor {
    pub fn parse_descriptor(descriptor: &str) -> Self {
        Self {
            ty: VarType::from_signature(descriptor),
            descriptor_string: descriptor.into(),
        }
    }

    pub fn build_new_descriptor(&self, builder: &dyn NewClassNameBuilder) -> Option<String> {
        build_new_type(&self.ty, builder).map(|ty| ty.to_string())
    }
}

impl PartialEq for FieldDescriptor {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
    }
}

impl Eq for FieldDescriptor {}

impl Hash for FieldDescriptor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
    }
}

#[derive(Clone, Debug)]
pub struct MethodDescriptor {
    pub params: Vec<VarType>,
    pub ret: VarType,
    descriptor: ArcStr,
    pub generic_info: Option<Arc<SharedSignature<GenericMethodDescriptor>>>,
}

impl MethodDescriptor {
    pub fn parse_descriptor(descriptor: &str) -> Self {
        let invalid = || panic!("Invalid descriptor: {descriptor}");
        let parenth = descriptor.rfind(')').unwrap_or_else(invalid);
        if !descriptor.starts_with('(') {
            invalid();
        }

        let mut params = Vec::new();
        let parameters = &descriptor[1..parenth];
        let mut from = None;
        let mut index = 0;
        while let Some(c) = parameters[index..].chars().next() {
            let start = *from.get_or_insert(index);
            index += match c {
                '[' => 1,
                'L' => parameters[index..].find(';').unwrap_or_else(invalid) + 1,
                _ => c.len_utf8(),
            };
            if c != '[' {
                params.push(VarType::from_signature(&parameters[start..index]));
                from = None;
            }
        }

        Self {
            params,
            ret: VarType::from_signature(&descriptor[parenth + 1..]),
            descriptor: descriptor.into(),
            generic_info: None,
        }
    }

    /// Bytecode local slots of the declared parameters, excluding the receiver.
    pub fn parameter_slots(&self, is_static: bool) -> impl Iterator<Item = (i32, &VarType)> {
        self.params.iter().scan(i32::from(!is_static), |slot, ty| {
            let start = *slot;
            *slot += ty.stack_size;
            Some((start, ty))
        })
    }

    pub fn add_generic_descriptor(&mut self, desc: Arc<SharedSignature<GenericMethodDescriptor>>) {
        self.generic_info = Some(desc);
    }

    pub fn as_str(&self) -> &str {
        &self.descriptor
    }

    pub fn build_new_descriptor(&self, builder: &dyn NewClassNameBuilder) -> Option<String> {
        let new_params: Vec<Option<VarType>> = self
            .params
            .iter()
            .map(|param| build_new_type(param, builder))
            .collect();
        let new_ret = build_new_type(&self.ret, builder);

        if new_ret.is_none() && new_params.iter().all(Option::is_none) {
            return None;
        }

        let mut res = String::from("(");
        for (param, new_param) in self.params.iter().zip(&new_params) {
            res.push_str(&new_param.as_ref().unwrap_or(param).to_string());
        }
        res.push(')');
        res.push_str(&new_ret.as_ref().unwrap_or(&self.ret).to_string());
        Some(res)
    }
}

fn build_new_type(ty: &VarType, builder: &dyn NewClassNameBuilder) -> Option<VarType> {
    if ty.ty != CodeType::Object {
        return None;
    }
    let new_class_name = builder.build_new_classname(ty.name())?;
    Some(VarType::with_value(ty.ty, ty.array_dim, new_class_name))
}

impl fmt::Display for MethodDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.descriptor)
    }
}

impl PartialEq for MethodDescriptor {
    fn eq(&self, other: &Self) -> bool {
        self.ret == other.ret && self.params == other.params
    }
}

impl Eq for MethodDescriptor {}

impl Hash for MethodDescriptor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ret.hash(state);
        self.params.len().hash(state);
    }
}
