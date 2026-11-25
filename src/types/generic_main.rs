// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.gen.generics`: `GenericMain`, the parser of `Signature`
//! attributes, with the descriptors it produces (`GenericClassDescriptor`,
//! `GenericFieldDescriptor`, `GenericMethodDescriptor`) and the
//! `GenericsChecker` that validates them against the erased descriptors.

use std::fmt::Write as _;
use std::sync::{Arc, RwLock};

use rustc_hash::FxHashMap;

use super::generic_type::GenericType;
use super::var_type::{CodeType, VarType};
use crate::engine::Cx;
use crate::util::java_str;

/// The parsed `Signature` attribute of a class, field or method.
///
/// Upstream corrects these descriptor objects in place when they contradict
/// the erased descriptor, and whoever holds the object sees the correction.
/// The holders share this cell instead.
#[derive(Debug)]
pub struct SharedSignature<T>(RwLock<Arc<T>>);

impl<T: Clone> SharedSignature<T> {
    pub fn new(descriptor: T) -> Arc<Self> {
        Arc::new(Self(RwLock::new(Arc::new(descriptor))))
    }

    /// The descriptor as it is now.
    pub fn get(&self) -> Arc<T> {
        Arc::clone(&self.0.read().unwrap())
    }

    /// Replaces the descriptor by a changed copy. The change runs without
    /// the cell being locked, so it may look up other signatures.
    pub fn update<R>(&self, change: impl FnOnce(&mut T) -> R) -> R {
        let mut descriptor = T::clone(&self.get());
        let result = change(&mut descriptor);
        *self.0.write().unwrap() = Arc::new(descriptor);
        result
    }
}

#[derive(Clone, Debug)]
pub struct GenericClassDescriptor {
    pub superclass: VarType,
    /// The class itself, applied to its own type parameters.
    pub generic_type: VarType,
    pub superinterfaces: Vec<VarType>,
    pub fparameters: Vec<String>,
    pub fbounds: Vec<Vec<VarType>>,
}

impl GenericClassDescriptor {
    pub fn get_checker(&self) -> GenericsChecker {
        GenericsChecker::new(&self.fparameters, &self.fbounds)
    }

    pub fn verify_types(
        &mut self,
        cx: &Cx,
        actual_superclass: &VarType,
        actual_super_interfaces: &[VarType],
    ) {
        let checker = self.get_checker();

        if !checker.is_properly_bounded(cx, actual_superclass, &self.superclass) {
            log::warn!(
                "Mismatched superclass signature, expected: {actual_superclass}, actual: {}",
                value_text(&self.superclass)
            );
            self.superclass = actual_superclass.clone();
        }

        for (i, super_interface) in self.superinterfaces.iter_mut().enumerate() {
            let Some(actual_super_interface) = actual_super_interfaces.get(i) else {
                log::warn!("Actual superinterface count is less than expected");
                break;
            };
            if !checker.is_properly_bounded(cx, actual_super_interface, super_interface) {
                log::warn!(
                    "Mismatched superinterface signature, expected: {actual_super_interface}, actual: {}",
                    value_text(super_interface)
                );
                *super_interface = actual_super_interface.clone();
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct GenericFieldDescriptor {
    pub ty: VarType,
}

impl GenericFieldDescriptor {
    pub fn verify_type(
        &mut self,
        cx: &Cx,
        containing_class_generics: Option<&GenericClassDescriptor>,
        real_type: &VarType,
    ) {
        let Some(containing_class_generics) = containing_class_generics else {
            self.verify_loosely(cx, real_type);
            return;
        };

        let checker = containing_class_generics.get_checker();
        if !checker.is_properly_bounded(cx, &self.ty, real_type) {
            log::warn!(
                "Mismatched field signature, expected: {}, actual: {}",
                value_text(real_type),
                value_text(&self.ty)
            );
            self.ty = real_type.clone();
        }
    }

    //FIXME this is necessary because some places don't have other signature information,
    // which prevents the ability to check class- or method-provided generic types
    pub fn verify_loosely(&mut self, cx: &Cx, actual_type: &VarType) {
        if actual_type.higher_equal_in_lattice_than(cx, &self.ty) {
            return;
        }

        if self.ty.ty == CodeType::Genvar {
            return; // Impossible to verify
        }

        log::warn!(
            "Mismatched field signature, expected: {}, actual: {}",
            value_text(&self.ty),
            value_text(actual_type)
        );
        self.ty = actual_type.clone();
    }
}

#[derive(Clone, Debug)]
pub struct GenericMethodDescriptor {
    pub type_parameters: Vec<String>,
    pub type_parameter_bounds: Vec<Vec<VarType>>,
    pub parameter_types: Vec<VarType>,
    pub return_type: VarType,
    pub exception_types: Vec<VarType>,
}

impl GenericMethodDescriptor {
    pub fn verify_types(
        &mut self,
        cx: &Cx,
        checker: Option<&GenericsChecker>,
        real_param_types: &[VarType],
        real_return_type: &VarType,
        real_exception_types: &[VarType],
    ) {
        let checker = match checker {
            None => GenericsChecker::new(&self.type_parameters, &self.type_parameter_bounds),
            Some(checker) => {
                checker.copy_with(&self.type_parameters, &self.type_parameter_bounds)
            }
        };

        for (i, parameter_type) in self.parameter_types.iter_mut().enumerate() {
            let real_type = &real_param_types[i];
            if !checker.is_properly_bounded(cx, parameter_type, real_type) {
                log::warn!(
                    "Mismatched method parameter signature, expected: {}, actual: {}",
                    value_text(real_type),
                    value_text(parameter_type)
                );
                *parameter_type = real_type.clone();
            }
        }

        if !checker.is_properly_bounded(cx, &self.return_type, real_return_type) {
            log::warn!(
                "Mismatched method return signature, expected: {}, actual: {}",
                value_text(real_return_type),
                value_text(&self.return_type)
            );
            self.return_type = real_return_type.clone();
        }

        for (i, exception_type) in self.exception_types.iter().enumerate() {
            let real_type = &real_exception_types[i];
            if !checker.is_properly_bounded(cx, exception_type, real_type) {
                log::warn!(
                    "Mismatched method exception signature, expected: {}, actual: {}",
                    value_text(real_type),
                    value_text(exception_type)
                );
            }
        }
    }
}

/// The name of a type as upstream concatenates `type.value` into a message.
fn value_text(ty: &VarType) -> &str {
    ty.value.as_deref().unwrap_or("null")
}

/// The bounds of the type variables in scope.
#[derive(Clone, Debug, Default)]
pub struct GenericsChecker {
    bounds_map: FxHashMap<String, Vec<VarType>>,
}

impl GenericsChecker {
    pub fn new(type_variables: &[String], bounds: &[Vec<VarType>]) -> Self {
        Self::default().copy_with(type_variables, bounds)
    }

    /// `copy(typeVariables, bounds)`: this scope with further type variables,
    /// which shadow those of the same name.
    pub fn copy_with(&self, type_variables: &[String], bounds: &[Vec<VarType>]) -> Self {
        let mut bounds_map = self.bounds_map.clone();
        bounds_map.extend(type_variables.iter().cloned().zip(bounds.iter().cloned()));
        Self { bounds_map }
    }

    /// `copy(parent)`: this scope, with the variables of `parent` it does not define.
    pub fn copy_with_parent(&self, parent: &GenericsChecker) -> Self {
        let mut bounds_map = self.bounds_map.clone();
        for (name, bounds) in &parent.bounds_map {
            bounds_map
                .entry(name.clone())
                .or_insert_with(|| bounds.clone());
        }
        Self { bounds_map }
    }

    pub fn is_properly_bounded(&self, cx: &Cx, ty: &VarType, bound: &VarType) -> bool {
        if ty.higher_equal_in_lattice_than(cx, bound) {
            return true;
        }

        // Get base type if array
        let bound = bound.resize_array_dim(0);

        ty.ty == CodeType::Genvar
            && ty.is_generic_type()
            && self.bounds_map.get(ty.name()).is_some_and(|type_bounds| {
                type_bounds
                    .iter()
                    .any(|type_bound| self.is_properly_bounded(cx, type_bound, &bound))
            })
    }
}

pub fn parse_class_signature(
    qualified_name: &str,
    signature: &str,
) -> Option<GenericClassDescriptor> {
    let descriptor = try_parse_class_signature(qualified_name, signature);
    if descriptor.is_none() {
        log::warn!("Invalid signature: {signature}");
    }
    descriptor
}

fn try_parse_class_signature(
    qualified_name: &str,
    signature: &str,
) -> Option<GenericClassDescriptor> {
    let (mut signature, fparameters, fbounds) = parse_formal_parameters(signature)?;

    let super_cl = VarType::try_get_next_type(signature)?;
    let superclass = VarType::try_parse(super_cl, GenericType::WILDCARD_NO)?;
    signature = &signature[super_cl.len()..];

    let mut superinterfaces = Vec::new();
    while !signature.is_empty() {
        let super_if = VarType::try_get_next_type(signature)?;
        superinterfaces.push(VarType::try_parse(super_if, GenericType::WILDCARD_NO)?);
        signature = &signature[super_if.len()..];
    }

    let mut buf = format!("L{qualified_name}<");
    for parameter in &fparameters {
        write!(buf, "T{parameter};").unwrap();
    }
    buf.push_str(">;");
    let generic_type = VarType::try_parse(&buf, GenericType::WILDCARD_NO)?;

    Some(GenericClassDescriptor {
        superclass,
        generic_type,
        superinterfaces,
        fparameters,
        fbounds,
    })
}

pub fn parse_field_signature(signature: &str) -> Option<GenericFieldDescriptor> {
    let ty = VarType::try_parse(signature, GenericType::WILDCARD_NO);
    if ty.is_none() {
        log::warn!("Invalid signature: {signature}");
    }
    Some(GenericFieldDescriptor { ty: ty? })
}

pub fn parse_method_signature(signature: &str) -> Option<GenericMethodDescriptor> {
    let descriptor = try_parse_method_signature(signature);
    if descriptor.is_none() {
        log::warn!("Invalid signature: {signature}");
    }
    descriptor
}

fn try_parse_method_signature(signature: &str) -> Option<GenericMethodDescriptor> {
    let (signature, type_parameters, type_parameter_bounds) = parse_formal_parameters(signature)?;

    let to = signature.find(')')?;
    let mut parameters = signature.get(1..to)?;
    let mut signature = &signature[to + 1..];

    let mut parameter_types = Vec::new();
    while !parameters.is_empty() {
        let par = VarType::try_get_next_type(parameters)?;
        parameter_types.push(VarType::try_parse(par, GenericType::WILDCARD_NO)?);
        parameters = &parameters[par.len()..];
    }

    let ret = VarType::try_get_next_type(signature)?;
    let return_type = VarType::try_parse(ret, GenericType::WILDCARD_NO)?;
    signature = &signature[ret.len()..];

    // Each exception follows a '^'; whatever precedes the first one is ignored.
    let exception_types = java_str::split(signature, "^")
        .iter()
        .skip(1)
        .map(|exception| VarType::try_parse(exception, GenericType::WILDCARD_NO))
        .collect::<Option<_>>()?;

    Some(GenericMethodDescriptor {
        type_parameters,
        type_parameter_bounds,
        parameter_types,
        return_type,
        exception_types,
    })
}

/// The type parameters at the start of a signature, with their bounds, and
/// the rest of the signature.
fn parse_formal_parameters(signature: &str) -> Option<(&str, Vec<String>, Vec<Vec<VarType>>)> {
    let mut parameters = Vec::new();
    let mut bounds = Vec::new();
    if signature.chars().next()? != '<' {
        return Some((signature, parameters, bounds));
    }

    let mut counter = 1;
    let mut index = signature.len();
    for (i, c) in signature.char_indices().skip(1) {
        match c {
            '<' => counter += 1,
            '>' => {
                counter -= 1;
                if counter == 0 {
                    index = i;
                    break;
                }
            }
            _ => {}
        }
    }

    let mut value = &signature[1..index];
    let signature = signature.get(index + 1..)?;

    while !value.is_empty() {
        let to = value.find(':')?;
        let param = &value[..to];
        value = &value[to + 1..];

        let mut lst_bounds = Vec::new();
        loop {
            if *value.as_bytes().first()? == b':' {
                // empty superclass, skip
                value = &value[1..];
            }

            let bound = VarType::try_get_next_type(value)?;
            lst_bounds.push(VarType::try_parse(bound, GenericType::WILDCARD_NO)?);
            value = &value[bound.len()..];

            match value.strip_prefix(':') {
                Some(rest) => value = rest,
                None => break,
            }
        }

        parameters.push(param.to_owned());
        bounds.push(lst_bounds);
    }

    Some((signature, parameters, bounds))
}

pub fn get_generic_cast_type_name(cx: &mut Cx, ty: &VarType) -> String {
    let mut name = get_type_name(cx, ty);
    for _ in 0..ty.array_dim {
        name.push_str("[]");
    }
    name
}

fn get_type_name(cx: &mut Cx, ty: &VarType) -> String {
    const TYPE_NAMES: [&str; 8] = [
        "byte", "char", "double", "float", "int", "long", "short", "boolean",
    ];

    match ty.ty {
        tp if tp.ordinal() <= CodeType::Boolean.ordinal() => {
            TYPE_NAMES[tp.ordinal() as usize].to_owned()
        }
        CodeType::Void => "void".to_owned(),
        CodeType::Genvar => ty.name().to_owned(),
        CodeType::Object => ty.get_cast_name(cx),
        _ => panic!("Invalid type: {}", ty.to_generic_string(cx)),
    }
}
