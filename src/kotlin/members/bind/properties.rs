use std::{io, sync::Arc};

use crate::{
    engine::Cx,
    kotlin::{
        declarations::{KType, resolve},
        metadata::{
            NameResolver, flags,
            proto::{self, jvm::JvmMethodSignature},
        },
        types::java_signature,
    },
    structs::{
        StructClass, StructField,
        attr::{AnnotationData, AnnotationElement, ElementValue},
        consts::ConstantValue,
        struct_member::Attributes,
    },
    types::VarType,
    util::interpreter_util::make_unique_key,
};

use super::{
    ACC_STATIC, FieldElement, Hidden, MethodElement, StructMember, field, hide_equivalent_method,
    hide_field, hide_method, method, resolve_signature, state,
};
use crate::kotlin::members::{
    KProperty, KPropertyAccessor, PropertyInitializer, PropertyMethod, invalid_data,
};

pub(in crate::kotlin::members) fn properties(
    cx: &mut Cx,
    class: &Arc<StructClass>,
    properties: &[proto::Property],
    names: &NameResolver,
    companion_parent: Option<&Arc<StructClass>>,
) -> io::Result<()> {
    for property in properties {
        let flags = property.flags();
        let signature = property.property_signature.unwrap_or_default();
        let mut annotations = Vec::new();
        if let Some(synthetic) = &signature.synthetic_method {
            let (name, descriptor) = resolve_signature(names, Some(synthetic))?;
            if let Some(target) = method(cx, class, &name, &descriptor) {
                hide_method(cx, &target, Hidden::Generic);
                append_annotations(&mut annotations, &target.attributes);
            }
        }

        let name = resolve(names, property.name())?;
        let ty = property
            .return_type
            .as_ref()
            .map(|ty| KType::from_proto(Some(ty), names))
            .transpose()?;
        let mut property_descriptor = ty
            .as_ref()
            .map(|ty| java_signature(&ty.classifier, ty.nullable));

        let delegate_field = if flags::IS_DELEGATED.get(flags) {
            let signature = signature.field.unwrap_or_default();
            let name = resolve(names, signature.name())?;
            let descriptor = resolve(names, signature.desc())?;
            let field = field(cx, class, &name, &descriptor);
            if let Some(field) = &field {
                hide_field(cx, field, Hidden::Generic);
            }
            field
        } else {
            None
        };

        let getter = if flags::HAS_GETTER.get(flags) {
            let (name, descriptor) = resolve_signature(names, signature.getter.as_ref())?;
            let getter = method(cx, class, &name, &descriptor).map(|method| {
                if property_descriptor.is_none() {
                    let return_type = method
                        .descriptor
                        .split_once(')')
                        .map_or(method.descriptor.as_str(), |(_, ret)| ret);
                    property_descriptor = Some(return_type.to_owned());
                }
                KPropertyAccessor {
                    flags: property.getter_flags(),
                    method,
                }
            });
            if let Some(parent) = companion_parent {
                hide_equivalent_method(cx, parent, &name, &descriptor, Hidden::CompanionItem);
            }
            getter
        } else {
            None
        };

        let setter = if flags::HAS_SETTER.get(flags) {
            setter(
                cx,
                class,
                names,
                property,
                signature.setter.as_ref(),
                companion_parent,
            )?
        } else {
            None
        };
        let (setter, setter_param_name) = setter
            .map(|(accessor, name)| (Some(accessor), Some(name)))
            .unwrap_or_default();

        let mut underlying_field = None;
        let mut field_container = class;
        if let Some(signature) = signature.field {
            let field_name = signature.name.map(|idx| resolve(names, idx)).transpose()?;
            let field_name = field_name.as_ref().unwrap_or(&name);
            let field_descriptor = signature.desc.map(|idx| resolve(names, idx)).transpose()?;
            let field_descriptor = field_descriptor
                .as_deref()
                .or(property_descriptor.as_deref());
            if let Some(descriptor) = field_descriptor {
                underlying_field = field(cx, class, field_name, descriptor);
                if let Some(parent) = companion_parent
                    && let Some(parent_field) = field(cx, parent, field_name, descriptor)
                {
                    hide_field(cx, &parent_field, Hidden::CompanionItem);
                    if underlying_field.is_none() {
                        underlying_field = Some(parent_field);
                        field_container = parent;
                    }
                }
            } else {
                let matches = |field: &&Arc<StructField>| field.name == name;
                underlying_field = match cx.kotlin_members.as_ref() {
                    Some(members) => members.fields(class).find(matches),
                    None => class.fields.iter().find(matches),
                }
                .cloned();
                if let Some(field) = &underlying_field {
                    property_descriptor = Some(field.descriptor.to_string());
                }
            }
        }

        if flags::HAS_ANNOTATIONS.get(flags)
            && annotations.is_empty()
            && let Some(field) = &underlying_field
        {
            append_annotations(&mut annotations, &field.attributes);
            if field.attributes.deprecated.is_some() {
                annotations.push(deprecated_annotation(cx));
            }
        }

        let initializer = if let Some(delegate) = delegate_field {
            let initializer = field_initializer(
                &delegate,
                make_unique_key(&delegate.name, &delegate.descriptor),
            );
            underlying_field = Some(delegate);
            Some(initializer)
        } else if let Some(field) = &underlying_field {
            let var_type = property_descriptor
                .as_deref()
                .map(VarType::from_signature)
                .unwrap_or(VarType::VARTYPE_OBJECT);
            if let Some(attribute) = &field.attributes.constant_value {
                let constant = field_container
                    .pool
                    .get_primitive_constant(attribute.index)
                    .ok_or_else(|| invalid_data("Missing Kotlin property constant value"))?;
                Some(PropertyInitializer::Constant {
                    ty: ty.as_ref().map_or(var_type, |ty| ty.jvm.clone()),
                    value: constant.value,
                })
            } else {
                Some(field_initializer(
                    field,
                    make_unique_key(&name, &var_type.to_string()),
                ))
            }
        } else {
            None
        };

        let binding = Arc::new(KProperty {
            name,
            ty,
            flags,
            getter,
            setter,
            setter_param_name,
            underlying_field,
            initializer,
            annotations,
            class: Arc::clone(class),
        });
        publish(cx, class, field_container, binding);
    }
    Ok(())
}

fn setter(
    cx: &mut Cx,
    class: &StructClass,
    names: &NameResolver,
    property: &proto::Property,
    signature: Option<&JvmMethodSignature>,
    companion_parent: Option<&Arc<StructClass>>,
) -> io::Result<Option<(KPropertyAccessor, arcstr::ArcStr)>> {
    let (name, descriptor) = resolve_signature(names, signature)?;
    let setter = method(cx, class, &name, &descriptor)
        .map(|method| {
            let parameter_name = property
                .setter_value_parameter
                .as_ref()
                .map_or(0, |param| param.name());
            Ok::<_, io::Error>((
                KPropertyAccessor {
                    flags: property.setter_flags(),
                    method,
                },
                resolve(names, parameter_name)?,
            ))
        })
        .transpose()?;
    if let Some(parent) = companion_parent {
        hide_equivalent_method(cx, parent, &name, &descriptor, Hidden::CompanionItem);
    }
    Ok(setter)
}

fn append_annotations(annotations: &mut Vec<AnnotationData>, attributes: &Attributes) {
    annotations.extend(
        [
            &attributes.runtime_visible_annotations,
            &attributes.runtime_invisible_annotations,
        ]
        .into_iter()
        .flatten()
        .flat_map(|attribute| attribute.annotations.iter().cloned()),
    );
}

fn deprecated_annotation(cx: &mut Cx) -> AnnotationData {
    let ids = cx.expression_ids.clone();
    state(cx)
        .deprecated_annotation
        .get_or_insert_with(|| {
            let message = AnnotationElement {
                id: ids.next(),
                value: ElementValue::Const {
                    ty: VarType::VARTYPE_STRING,
                    value: ConstantValue::String("Deprecated by attribute.".into()),
                },
            };
            AnnotationData::from_elements(
                arcstr::literal!("kotlin/Deprecated"),
                vec![arcstr::literal!("message")],
                vec![message],
                &ids,
            )
        })
        .clone()
}

fn field_initializer(field: &StructField, key: String) -> PropertyInitializer {
    PropertyInitializer::Field {
        key,
        is_static: field.has_modifier(ACC_STATIC),
    }
}

fn publish(
    cx: &mut Cx,
    class: &Arc<StructClass>,
    field_container: &Arc<StructClass>,
    binding: Arc<KProperty>,
) {
    let state = state(cx);
    if let Some(field) = &binding.underlying_field {
        state.fields.get_mut(field).element = Some(FieldElement::Property(Arc::clone(&binding)));
    }
    for (accessor, kind) in [
        (&binding.getter, PropertyMethod::Getter),
        (&binding.setter, PropertyMethod::Setter),
    ] {
        if let Some(accessor) = accessor {
            let attrs = state.methods.get_mut(&accessor.method);
            attrs.element = Some(MethodElement::Property(Arc::clone(&binding)));
            attrs.property_method = Some(kind);
        }
    }
    if !Arc::ptr_eq(class, field_container) {
        let attrs = state.classes.get_mut(class);
        attrs
            .companion_fields
            .extend(binding.underlying_field.iter().cloned());
        attrs.companion_accessors.extend(
            binding
                .getter
                .iter()
                .chain(&binding.setter)
                .map(|accessor| Arc::clone(&accessor.method)),
        );
    }
}
