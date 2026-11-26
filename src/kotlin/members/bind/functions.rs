// SPDX-License-Identifier: Apache-2.0

use std::{fmt::Write, io, sync::Arc};

use arcstr::{ArcStr, literal};
use rustc_hash::FxHashSet;

use crate::{
    engine::Cx,
    kotlin::{
        declarations::{KContract, KParameter, KType, KTypeParameter, resolve},
        metadata::{
            NameResolver, flags,
            proto::{self, Modality, Visibility, class::Kind},
        },
    },
    structs::{StructClass, StructMethod, consts::PrimitiveConstant},
    types::MethodDescriptor,
};

use super::{
    ACC_STATIC, DefaultArguments, Hidden, MethodElement, StructMember, default_arguments,
    hide_equivalent_method, method, state,
};
use crate::kotlin::members::{ClassElement, KConstructor, KFunction};

pub(in crate::kotlin::members) fn functions(
    cx: &mut Cx,
    class: &Arc<StructClass>,
    functions: &[proto::Function],
    names: &NameResolver,
    types: Option<&proto::TypeTable>,
    synthetic: bool,
    companion_parent: Option<&StructClass>,
) -> io::Result<()> {
    for function in functions {
        let flags = function.flags();
        let name = resolve(names, function.name())?;
        let parameters = function
            .value_parameter
            .iter()
            .map(|parameter| KParameter::for_function(parameter, names))
            .collect::<io::Result<Vec<_>>>()?;
        let receiver_type = function
            .receiver_type
            .as_ref()
            .map(|ty| KType::from_proto(Some(ty), names))
            .transpose()?;
        let return_type = KType::from_proto(function.return_type.as_ref(), names)?;

        let signature = function.method_signature.as_ref();
        let lookup_name = signature
            .and_then(|sig| sig.name)
            .map(|index| resolve(names, index))
            .transpose()?;
        let lookup_name = lookup_name.as_ref().unwrap_or(&name);
        let descriptor = signature
            .and_then(|sig| sig.desc)
            .map(|index| resolve(names, index))
            .transpose()?;
        let target = descriptor.and_then(|descriptor| method(cx, class, lookup_name, &descriptor));
        let method = if let Some(method) = target {
            method
        } else {
            let mut descriptor = "(".to_owned();
            for ty in receiver_type
                .iter()
                .chain(parameters.iter().map(|param| &param.ty))
            {
                write!(descriptor, "{ty}").unwrap();
            }
            write!(descriptor, "){return_type}").unwrap();
            let Some(target) = method(cx, class, lookup_name, &descriptor) else {
                if !(flags::IS_SUSPEND.get(flags) && name == "<anonymous>") {
                    log::error!(
                        "Couldn't find method {name} {descriptor} in class {}",
                        class.qualified_name
                    );
                }
                continue;
            };
            if let Some(parent) = companion_parent {
                hide_equivalent_method(cx, parent, lookup_name, &descriptor, Hidden::CompanionItem);
            }
            target
        };
        let type_parameters = function
            .type_parameter
            .iter()
            .map(|parameter| KTypeParameter::from_proto(parameter, names))
            .collect::<io::Result<Vec<_>>>()?;
        let context_receiver_types = function
            .context_receiver_type
            .iter()
            .map(|ty| KType::from_proto(Some(ty), names))
            .collect::<io::Result<Vec<_>>>()?;
        let descriptor = default_descriptor(
            class,
            &method,
            &parameters,
            &type_parameters,
            receiver_type.as_ref(),
            &return_type,
        );
        let defaults = default_arguments(
            cx,
            class,
            companion_parent,
            format!("{name}$default").into(),
            descriptor.into(),
        );
        let known_override = !matches!(
            flags::VISIBILITY.get(flags),
            Some(Visibility::Private | Visibility::PrivateToThis | Visibility::Local)
        ) && search_for_method(
            cx,
            class,
            &method.name,
            &MethodDescriptor::parse_descriptor(&method.descriptor),
        );
        let contract = function
            .contract
            .as_ref()
            .map(|contract| {
                let default = proto::TypeTable::default();
                KContract::from_proto(contract, &parameters, names, types.unwrap_or(&default))
            })
            .transpose()?;
        let binding = Arc::new(KFunction {
            name,
            parameters,
            type_parameters,
            return_type,
            flags,
            context_receiver_types,
            receiver_type,
            contract,
            known_override,
            defaults,
            class: Arc::clone(class),
            method,
        });
        let attributes = state(cx);
        attributes.methods.get_mut(&binding.method).element =
            Some(MethodElement::Function(Arc::clone(&binding)));
        if synthetic {
            attributes.classes.get_mut(class).element = Some(ClassElement::Synthetic(binding));
        }
    }
    Ok(())
}

fn default_descriptor(
    class: &StructClass,
    method: &StructMethod,
    parameters: &[KParameter],
    type_parameters: &[KTypeParameter],
    receiver_type: Option<&KType>,
    return_type: &KType,
) -> String {
    let mut descriptor = "(".to_owned();
    if !method.has_modifier(ACC_STATIC) {
        write!(descriptor, "L{};", class.qualified_name).unwrap();
    }
    if let Some(ty) = receiver_type {
        write!(descriptor, "{ty}").unwrap();
    }
    for parameter in parameters {
        let ty = &parameter.ty;
        if let Some(name) = &ty.parameter_name {
            let bounds = type_parameters
                .iter()
                .find(|tp| tp.name == *name)
                .map(|tp| tp.upper_bounds.as_slice());
            if let Some([bound]) = bounds {
                write!(descriptor, "{bound}").unwrap();
            } else {
                descriptor.push_str("Ljava/lang/Object;");
            }
        } else {
            write!(descriptor, "{ty}").unwrap();
        }
    }
    append_masks(&mut descriptor, parameters.len());
    write!(descriptor, "Ljava/lang/Object;){return_type}").unwrap();
    descriptor
}

pub(in crate::kotlin::members) fn constructors(
    cx: &mut Cx,
    class: &Arc<StructClass>,
    proto: &proto::Class,
    names: &NameResolver,
) -> io::Result<()> {
    let class_flags = proto.flags();
    if flags::MODALITY.get(class_flags) == Some(Modality::Abstract) {
        return Ok(());
    }
    let kind = flags::CLASS_KIND.get(class_flags);
    for constructor in &proto.constructor {
        let parameters = constructor
            .value_parameter
            .iter()
            .map(|parameter| KParameter::for_constructor(parameter, names))
            .collect::<io::Result<Vec<_>>>()?;
        let flags = constructor.flags();
        let signature = constructor.constructor_signature.unwrap_or_default();
        let descriptor = resolve(names, signature.desc())?;
        let Some(target) = method(cx, class, "<init>", &descriptor) else {
            if kind == Some(Kind::AnnotationClass) {
                state(cx).classes.get_mut(class).primary_constructor =
                    Some(Arc::new(KConstructor {
                        parameters,
                        flags,
                        defaults: DefaultArguments::Annotation,
                        class: Arc::clone(class),
                        method: None,
                        is_primary: true,
                        class_flags,
                    }));
                return Ok(());
            }
            log::warn!(
                "Method <init>{descriptor} not found in {}",
                class.qualified_name
            );
            continue;
        };
        let mut descriptor = "(".to_owned();
        if kind == Some(Kind::EnumClass) {
            descriptor.push_str("Ljava/lang/String;I");
        }
        for parameter in &parameters {
            write!(descriptor, "{}", parameter.ty).unwrap();
        }
        append_masks(&mut descriptor, parameters.len());
        descriptor.push_str("Lkotlin/jvm/internal/DefaultConstructorMarker;)V");
        let defaults = default_arguments(cx, class, None, literal!("<init>"), descriptor.into());
        let is_primary = !flags::IS_SECONDARY.get(flags);
        let binding = Arc::new(KConstructor {
            parameters,
            flags,
            defaults,
            class: Arc::clone(class),
            method: Some(Arc::clone(&target)),
            is_primary,
            class_flags,
        });
        let attributes = state(cx);
        attributes.methods.get_mut(&target).element =
            Some(MethodElement::Constructor(Arc::clone(&binding)));
        if is_primary {
            attributes.classes.get_mut(class).primary_constructor = Some(binding);
        }
    }
    Ok(())
}

fn append_masks(descriptor: &mut String, parameters: usize) {
    descriptor.extend(std::iter::repeat_n('I', parameters / 32 + 1));
}

pub(crate) fn search_for_method(
    cx: &Cx,
    class: &StructClass,
    name: &str,
    descriptor: &MethodDescriptor,
) -> bool {
    let mut visited = FxHashSet::default();
    visited.insert(class.qualified_name.clone());
    search_parents(cx, class, name, descriptor, &mut visited)
}

fn search_parents(
    cx: &Cx,
    class: &StructClass,
    name: &str,
    descriptor: &MethodDescriptor,
    visited: &mut FxHashSet<ArcStr>,
) -> bool {
    let superclass = class
        .super_class
        .as_ref()
        .map(PrimitiveConstant::get_string);
    for parent in superclass.into_iter().chain(&class.interface_names) {
        if !visited.insert(parent.clone()) {
            continue;
        }
        let Some(parent) = cx.classes().get_class(parent) else {
            continue;
        };
        let matches = |method: &Arc<StructMethod>| {
            method.name == name
                && !method.has_modifier(ACC_STATIC)
                && MethodDescriptor::parse_descriptor(&method.descriptor) == *descriptor
        };
        let found = match cx.kotlin_members.as_ref() {
            Some(members) => members.methods(&parent).any(matches),
            None => parent.methods.iter().any(matches),
        };
        if found || search_parents(cx, &parent, name, descriptor, visited) {
            return true;
        }
    }
    false
}
