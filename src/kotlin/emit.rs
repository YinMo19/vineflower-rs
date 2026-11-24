// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{borrow::Cow, collections::HashMap, ops::Range};

use crate::{
    Options,
    classfile::{ClassFile, ElementValue, Member},
    context::ClassGroup,
    descriptor::{MethodDescriptor, Primitive, Type as JvmType},
    emit::SourceMap,
};

use super::{
    ClassDeclaration, ClassKind, Constructor, Declaration, Flags, Function, JvmMethodSignature,
    KotlinError, MemberKind, Metadata, Modality, PackageDeclaration, Property, TypeParameter,
    ValueParameter, Variance, Visibility,
    body::{self, ABSTRACT, Body, Bytecode, Expr, FINAL, NATIVE, STATIC},
    syntax::{INDENT, Types, identifier, qualified, variance_prefix, visibility},
};

mod data;
mod multifile;
mod nesting;
mod objects;
mod trace;

#[derive(Clone, Copy)]
struct Style<'a> {
    indent: &'a str,
    unit: &'a str,
    interface: bool,
}

type Location<'a> = Option<(&'a mut SourceMap, usize)>;

pub(super) fn render<'a, 'data>(
    class: &'a ClassFile<'data>,
    metadata: &Metadata,
    group: Option<&'a ClassGroup<'data>>,
    options: Option<&Options>,
) -> Result<(String, Option<SourceMap>), KotlinError> {
    let owner = class.pool.class_name(class.this_class)?;
    let bytecode = Bytecode { class, owner };
    let (jvm_package, simple_name) = owner.rsplit_once('/').unwrap_or(("", owner));
    let package = match &metadata.declaration {
        Declaration::Class(declaration) => declaration.name.package(),
        Declaration::Synthetic(_) => return Err(error(owner, "synthetic class")),
        _ => jvm_package,
    };
    if let Some(name) = metadata
        .header
        .package_name
        .as_deref()
        .filter(|name| !name.is_empty())
        && !name.split('.').eq(package.split('/'))
    {
        return Err(error(owner, "relocated JVM package"));
    }
    let part_facade = if matches!(metadata.declaration, Declaration::MultifilePart(_)) {
        Some(multifile::package_part_facade(
            owner,
            metadata.header.extra_string.as_deref(),
            group,
        )?)
    } else {
        None
    };
    let mut out = String::new();
    let jvm_name = part_facade
        .as_deref()
        .map(multifile::simple_name)
        .or_else(|| {
            matches!(metadata.declaration, Declaration::FileFacade(_)).then_some(simple_name)
        });
    if part_facade.is_some() {
        out.push_str("@file:JvmMultifileClass\n");
        push_file_jvm_name(
            &mut out,
            jvm_name.expect("package parts have a JVM facade name"),
        );
    }
    file_annotations(&mut out, &bytecode, jvm_name, part_facade.is_some())?;
    if !package.is_empty() {
        out.push_str("package ");
        qualified(&mut out, package, owner)?;
        out.push_str("\n\n");
    }
    let unit = options.map_or(INDENT, |options| options.indent.as_str());
    let mut mapping = options
        .filter(|options| options.include_line_mappings)
        .map(|_| SourceMap::default());
    match &metadata.declaration {
        Declaration::Class(declaration) => {
            let decompile_inner = options.is_none_or(|options| options.decompile_inner);
            render_class(
                &mut out,
                &bytecode,
                declaration,
                ClassScope { group, decompile_inner, parent: None, indent: "", unit, depth: 0 },
                mapping.as_mut().map(|map| (map, 0)),
            )?;
        }
        Declaration::FileFacade(members) | Declaration::MultifilePart(members) => {
            for method in &class.methods {
                if class.pool.utf8(method.name_index)? == "<init>" {
                    return Err(error(
                        owner,
                        "Kotlin package file has an instance constructor",
                    ));
                }
            }
            let types = Types {
                declaration: owner,
                package,
                owner: None,
                owner_parameters: &[],
                local_parameters: &[],
            };
            let plan = Plan::new(&bytecode, members, None, Layout::File)?;
            let style = Style {
                indent: "",
                unit,
                interface: false,
            };
            render_members(
                &mut out,
                &bytecode,
                &types,
                &plan,
                members,
                style,
                group,
                mapping.as_mut().map(|map| (map, 0)),
                false,
            )?;
        }
        Declaration::MultifileFacade(parts) => {
            multifile::render(
                &mut out,
                &bytecode,
                simple_name,
                parts,
                group,
                options,
                mapping.as_mut(),
            )?;
        }
        Declaration::Synthetic(_) => unreachable!(),
    }
    Ok((out, mapping))
}

fn file_annotations(
    out: &mut String,
    bytecode: &Bytecode<'_, '_>,
    jvm_name: Option<&str>,
    part: bool,
) -> Result<(), KotlinError> {
    let pool = &bytecode.class.pool;
    for visible in [true, false] {
        for annotation in bytecode.class.annotations(visible)? {
            match pool.utf8(annotation.type_index)? {
                "Lkotlin/Metadata;" | "Lkotlin/jvm/internal/SourceDebugExtension;" => {}
                "Lkotlin/jvm/JvmMultifileClass;" if part && annotation.elements.is_empty() => {}
                "Lkotlin/jvm/JvmName;" => {
                    let simple_name = jvm_name
                        .ok_or_else(|| error(bytecode.owner, "unexpected file-level @JvmName"))?;
                    let [(name, ElementValue::Constant { tag: b's', index })] =
                        annotation.elements.as_slice()
                    else {
                        return Err(error(bytecode.owner, "invalid @file:JvmName"));
                    };
                    if pool.utf8(*name)? != "name" || pool.utf8(*index)? != simple_name {
                        return Err(error(bytecode.owner, "invalid @file:JvmName"));
                    }
                    if !part {
                        push_file_jvm_name(out, simple_name);
                    }
                }
                _ => return Err(error(bytecode.owner, "class or file annotations")),
            }
        }
    }
    if !out.is_empty() {
        out.push('\n');
    }
    Ok(())
}

fn push_file_jvm_name(out: &mut String, name: &str) {
    out.push_str("@file:JvmName(");
    body::write_string(out, name.encode_utf16());
    out.push_str(")\n");
}

#[derive(Clone, Copy)]
struct ClassScope<'scope, 'a, 'data> {
    group: Option<&'a ClassGroup<'data>>,
    decompile_inner: bool,
    parent: Option<(&'scope Bytecode<'a, 'data>, &'scope ClassDeclaration)>,
    indent: &'scope str,
    unit: &'scope str,
    depth: u8,
}

fn render_class<'a, 'data>(
    out: &mut String,
    bytecode: &Bytecode<'a, 'data>,
    declaration: &ClassDeclaration,
    scope: ClassScope<'_, 'a, 'data>,
    mut location: Location<'_>,
) -> Result<(), KotlinError> {
    let invalid = |feature| error(bytecode.owner, feature);
    let ClassScope { group, decompile_inner, parent, indent, unit, depth } = scope;
    let nested = parent.is_some();
    if depth >= 32 || declaration.name.local
        || declaration.name.relative_name().contains('.') != nested
        || declaration.name.jvm_internal_name() != bytecode.owner
    {
        return Err(invalid("invalid local or nested Kotlin class identity"));
    }
    if nested {
        file_annotations(&mut String::new(), bytecode, None, false)?;
    }
    let children = nesting::children(bytecode, declaration, group.filter(|_| decompile_inner))?;
    let relative_name = declaration.name.relative_name();
    let name = relative_name.rsplit('.').next().unwrap_or(relative_name);
    let types = Types {
        declaration: bytecode.owner,
        package: declaration.name.package(),
        owner: Some(&declaration.name),
        owner_parameters: &declaration.type_parameters,
        local_parameters: &[],
    };
    let data_class = declaration.flags.has(10);
    if declaration.flags.has_annotations()
        || declaration.flags.0 & (0b11_1101 << 9) != 0
        || !declaration.context_receivers.is_empty()
        || !declaration.enum_entries.is_empty()
    {
        return Err(invalid(
            "class modifiers, annotations, or context receivers",
        ));
    }
    let interface = declaration.kind == ClassKind::Interface;
    let singleton = match declaration.kind {
        ClassKind::Class | ClassKind::Interface => None,
        ClassKind::Object | ClassKind::CompanionObject => {
            if data_class || !declaration.type_parameters.is_empty()
                || declaration.flags.modality() != Modality::Final
                || declaration.companion_name.is_some()
            {
                return Err(invalid("nontrivial singleton declaration"));
            }
            let host = if declaration.kind == ClassKind::CompanionObject {
                let (host, owner) = parent.ok_or_else(|| invalid("companion object requires its owning class"))?;
                if owner.companion_name.as_deref() != Some(name) {
                    return Err(invalid("companion object does not match its owner's metadata"));
                }
                Some((host, name))
            } else {
                None
            };
            Some(objects::Singleton::validate(bytecode, declaration, host)?)
        }
        _ => return Err(invalid("class kind")),
    };
    if interface != (bytecode.class.access_flags & 0x0200 != 0) {
        return Err(invalid("metadata class kind does not match the JVM class"));
    }
    if bytecode.class.super_class == 0
        || bytecode.class.pool.class_name(bytecode.class.super_class)? != "java/lang/Object"
        || !bytecode.class.interfaces.is_empty()
        || declaration
            .supertypes
            .iter()
            .any(|ty| ty.class_id() != Some("kotlin/Any"))
    {
        return Err(invalid("inherited declarations require supertype context"));
    }
    if !declaration.members.type_aliases.is_empty() {
        return Err(invalid("nested type aliases"));
    }
    let constructor = match declaration.constructors.as_slice() {
        _ if singleton.is_some() => None,
        [] if interface => None,
        [constructor]
            if !interface && !constructor.flags.has(4) && !constructor.flags.has_annotations() =>
        {
            Some(constructor)
        }
        _ => return Err(invalid("nontrivial constructor declarations")),
    };
    let hierarchy = declaration.flags.modality();
    if hierarchy == Modality::Sealed || (interface && hierarchy != Modality::Abstract) {
        return Err(invalid("sealed or non-abstract interface declarations"));
    }
    if !nested && declaration.flags.visibility()? == Visibility::Protected {
        return Err(invalid("protected top-level class"));
    }
    let layout = if let Some(singleton) = &singleton {
        Layout::Singleton(singleton)
    } else if declaration.companion_name.is_some() {
        Layout::CompanionHost
    } else {
        Layout::Class
    };
    let plan = Plan::new(bytecode, &declaration.members, constructor, layout)?;
    if data_class {
        data::validate(bytecode, declaration, &plan)?;
    }
    out.push_str(indent);
    out.push_str(visibility(declaration.flags.visibility()?)?);
    out.push_str(modality(hierarchy, interface));
    if data_class {
        out.push_str("data ");
    }
    match declaration.kind {
        ClassKind::Interface => out.push_str("interface "),
        ClassKind::Class => out.push_str("class "),
        ClassKind::Object => out.push_str("object "),
        ClassKind::CompanionObject => {
            out.push_str("companion object");
            if name != "Companion" {
                out.push(' ');
            }
        }
        _ => unreachable!(),
    }
    if declaration.kind != ClassKind::CompanionObject || name != "Companion" {
        identifier(out, name, bytecode.owner)?;
    }
    type_parameters(
        out,
        &types,
        &declaration.type_parameters,
        TypeParameters::Class,
    )?;
    if let Some(constructor) = constructor {
        let constructor_visibility = constructor.flags.visibility()?;
        if constructor_visibility != Visibility::Public {
            out.push(' ');
            out.push_str(visibility(constructor_visibility)?);
            out.push_str("constructor");
        }
        if constructor_visibility != Visibility::Public || !constructor.parameters.is_empty() {
            let signature = constructor
                .signature
                .as_ref()
                .ok_or_else(|| invalid("constructor lacks JVM identity"))?;
            let defaults = body::parameter_defaults(
                bytecode,
                signature,
                &constructor.parameters,
                true,
                bytecode.owner,
            )?;
            let mut defaults = defaults.iter().peekable();
            out.push('(');
            for (index, parameter) in constructor.parameters.iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                if let Some(prop) = plan.promoted[index] {
                    let property = plan.properties[prop].property;
                    if data_class && property.flags.visibility()? == Visibility::Public {
                        out.push_str(if property.mutable() { "var " } else { "val " });
                    } else {
                        property_prefix(out, property, false, false)?;
                    }
                }
                let default =
                    defaults
                        .next_if(|(parameter, _)| *parameter == index)
                        .map(|(_, value)| {
                            (
                                value,
                                &signature.descriptor.parameters[index],
                                constructor.parameters.as_slice(),
                            )
                        });
                value_parameter(out, &types, parameter, false, default)?;
            }
            out.push(')');
        }
    }
    type_constraints(out, &types, &declaration.type_parameters)?;
    let mut members = String::new();
    let member_indent = if indent.is_empty() { Cow::Borrowed(unit) }
        else { Cow::Owned(format!("{indent}{unit}")) };
    let style = Style {
        indent: &member_indent,
        unit,
        interface,
    };
    let members_line = location.as_ref().map_or(0, |(_, base)| *base + trace::line_count(out) + 1);
    render_members(
        &mut members,
        bytecode,
        &types,
        &plan,
        &declaration.members,
        style,
        group,
        location.as_mut().map(|(map, _)| (&mut **map, members_line)),
        data_class,
    )?;
    for child in children {
        if !members.is_empty() {
            members.push('\n');
        }
        let owner = child.class.pool.class_name(child.class.this_class)?;
        render_class(
            &mut members,
            &Bytecode { class: child.class, owner },
            &child.declaration,
            ClassScope { group, decompile_inner, parent: Some((bytecode, declaration)), indent: &member_indent, unit, depth: depth + 1 },
            location.as_mut().map(|(map, _)| (&mut **map, members_line)),
        )?;
    }
    if let Some(singleton) = &singleton {
        singleton.verify_host_methods()?;
    }
    if members.is_empty() {
        out.push('\n');
    } else {
        out.push_str(" {\n");
        out.push_str(&members);
        out.push_str(indent);
        out.push_str("}\n");
    }
    Ok(())
}

type Field<'a, 'data> = &'a Member<'data>;

#[derive(Clone, Copy)]
enum Layout<'scope, 'a, 'data> {
    Class,
    CompanionHost,
    File,
    Singleton(&'scope objects::Singleton<'a, 'data>),
}

impl<'scope, 'a, 'data> Layout<'scope, 'a, 'data> {
    fn file(self) -> bool {
        matches!(self, Self::File)
    }

    fn singleton(self) -> Option<&'scope objects::Singleton<'a, 'data>> {
        match self {
            Self::Singleton(singleton) => Some(singleton),
            _ => None,
        }
    }
}

struct PlannedProperty<'a, 'data, 'metadata> {
    property: &'metadata Property,
    field: Option<Field<'a, 'data>>,
    initializer: Option<objects::Initializer<'a>>,
    initializer_offsets: Option<Range<u32>>,
    getter: Option<Expr<'a>>,
    setter_visibility: Option<Visibility>,
    promoted: bool,
    jvm_static: bool,
}

struct Plan<'a, 'data, 'metadata> {
    properties: Vec<PlannedProperty<'a, 'data, 'metadata>>,
    ordered: Vec<usize>,
    promoted: Vec<Option<usize>>,
    parameters: &'metadata [ValueParameter],
    initialization_method: Option<Field<'a, 'data>>,
    metadata_properties: &'metadata [Property],
    layout: Layout<'metadata, 'a, 'data>,
}

impl<'a, 'data, 'metadata> Plan<'a, 'data, 'metadata> {
    fn new(
        bytecode: &Bytecode<'a, 'data>,
        members: &'metadata PackageDeclaration,
        constructor: Option<&'metadata Constructor>,
        layout: Layout<'metadata, 'a, 'data>,
    ) -> Result<Self, KotlinError> {
        let singleton = layout.singleton();
        let storage = singleton.map_or(bytecode, |singleton| &singleton.storage);
        let mut properties = members
            .properties
            .iter()
            .filter(|p| p.flags.member_kind() != MemberKind::FakeOverride)
            .map(|p| plan_property(bytecode, p, &members.properties, layout))
            .collect::<Result<Vec<_>, _>>()?;
        let mut field_index = HashMap::new();
        for (index, property) in properties.iter().enumerate() {
            if let Some(field) = property.field {
                let pool = &storage.class.pool;
                if field_index
                    .insert(
                        (
                            pool.utf8(field.name_index)?,
                            pool.utf8(field.descriptor_index)?,
                        ),
                        index,
                    )
                    .is_some()
                {
                    return Err(error(bytecode.owner, "properties share a backing field"));
                }
            }
        }
        let expected_fields = storage.class.fields.iter().filter(|field| match layout {
            Layout::CompanionHost => field.access_flags & STATIC == 0,
            Layout::Singleton(singleton) => !std::ptr::eq(*field, singleton.instance)
                && (!singleton.is_companion() || field.access_flags & STATIC != 0),
            _ => true,
        }).count();
        if field_index.len() != expected_fields {
            return Err(error(
                bytecode.owner,
                "JVM fields without Kotlin declarations",
            ));
        }
        let parameters = constructor.map_or(&[][..], |con| con.parameters.as_slice());
        let mut promoted = vec![None; parameters.len()];
        let mut ordered = Vec::new();
        let clinit = if matches!(layout, Layout::Class | Layout::File) {
            let signature = JvmMethodSignature {
                name: "<clinit>".to_owned(),
                descriptor: MethodDescriptor {
                    parameters: Vec::new(),
                    return_type: JvmType::Void,
                },
            };
            let initialization = bytecode.find_method(&signature)?.map(|method| {
                let assignments = bytecode.initialization(
                    method, &signature.descriptor, &[], None, bytecode.owner,
                )?;
                Ok::<_, KotlinError>((assignments, method))
            }).transpose()?;
            if !layout.file() && initialization.as_ref().is_some_and(|(assignments, _)| !assignments.is_empty()) {
                return Err(error(bytecode.owner, "static initializer inside a Kotlin class"));
            }
            initialization
        } else {
            None
        };
        let initialization = if let Some(constructor) = constructor {
            let signature = constructor
                .signature
                .as_ref()
                .filter(|s| s.name == "<init>")
                .ok_or_else(|| error(bytecode.owner, "constructor lacks JVM identity"))?;
            let method = bytecode
                .find_method(signature)?
                .ok_or_else(|| error(bytecode.owner, "missing JVM constructor"))?;
            let assignments = bytecode.initialization(
                method,
                &signature.descriptor,
                parameters,
                Some("java/lang/Object"),
                bytecode.owner,
            )?;
            Some((assignments, method))
        } else {
            clinit
        };
        let (assignments, initialization_method) = initialization
            .map_or_else(|| (Vec::new(), None), |(assignments, method)| (assignments, Some(method)));
        let mut next_candidate = Some(0);
        let singleton_assignments = singleton.map(objects::Singleton::assignments).transpose()?;
        for assignment in assignments.into_iter().map(objects::Initialization::from)
            .chain(singleton_assignments.into_iter().flatten())
        {
            let Some(&index) = field_index.get(&(assignment.field, assignment.descriptor)) else {
                return Err(error(
                    bytecode.owner,
                    "initializer writes an undeclared property",
                ));
            };
            let state = &mut properties[index];
            if state.initializer.is_some() || state.promoted {
                return Err(error(
                    &state.property.name,
                    "multiple backing field initializations",
                ));
            }
            let descriptor = &state.property.signature.field.as_ref().unwrap().descriptor;
            if let Some(parameter) = assignment
                .value
                .parameter(descriptor)
                .filter(|&p| next_candidate.is_some_and(|min| p >= min))
                && parameters[parameter].name == state.property.name
                && parameters[parameter].ty == state.property.ty
                && parameters[parameter].vararg_element.is_none()
                && state.property.flags.modality() == Modality::Final
                && state.setter_visibility.is_none()
            {
                promoted[parameter] = Some(index);
                state.promoted = true;
                next_candidate = Some(parameter + 1);
            } else {
                state.initializer = Some(assignment.value);
                state.initializer_offsets = assignment.rhs_offsets;
                ordered.push(index);
                next_candidate = None;
            }
        }
        for (index, state) in properties.iter_mut().enumerate() {
            if state.field.is_some() && state.initializer.is_none() && !state.promoted {
                let property = state.property;
                let signature = property.signature.field.as_ref().unwrap();
                let default = Expr::default_field(&property.ty, &signature.descriptor)
                    .ok_or_else(|| error(&property.name, "no proven backing field initializer"))?;
                state.initializer = Some(objects::Initializer::Expression(default));
                ordered.push(index);
            }
        }
        Ok(Self {
            properties,
            ordered,
            promoted,
            parameters,
            initialization_method,
            metadata_properties: &members.properties,
            layout,
        })
    }
}

fn plan_property<'a, 'data, 'metadata>(
    bytecode: &Bytecode<'a, 'data>,
    property: &'metadata Property,
    properties: &'metadata [Property],
    layout: Layout<'metadata, 'a, 'data>,
) -> Result<PlannedProperty<'a, 'data, 'metadata>, KotlinError> {
    let name = &property.name;
    let invalid = |feature| error(name, feature);
    let singleton = layout.singleton();
    let jvm_static = if let Some(singleton) = singleton {
        singleton.property_static(property.signature.annotations_method.as_ref(), name)?
    } else {
        false
    };
    let storage = singleton.map_or(bytecode, |singleton| &singleton.storage);
    let static_field = layout.file() || singleton.is_some();
    let static_accessor = layout.file() || jvm_static && singleton.is_some_and(|singleton| !singleton.is_companion());
    if (property.flags.has_annotations() || property.signature.annotations_method.is_some()) && !jvm_static
        || property.flags.member_kind() != MemberKind::Declaration
        || property.flags.has(14)
        || property.flags.has(16)
        || property.flags.has(17)
        || property.late_init()
        || property.delegated()
        || property.jvm_flags != 0
        || property.signature.delegate_method.is_some()
        || property.receiver.is_some()
        || !property.type_parameters.is_empty()
        || !property.context_receivers.is_empty()
        || !property.context_parameters.is_empty()
    {
        return Err(invalid(
            "property modifiers, extension, annotations, or context parameters",
        ));
    }
    if layout.file()
        && (property.flags.modality() != Modality::Final
            || property.flags.visibility()? == Visibility::Protected)
    {
        return Err(invalid("non-final or protected top-level property"));
    }
    let abstract_property = property.flags.modality() == Modality::Abstract;
    let mut state = PlannedProperty {
        property,
        field: None,
        initializer: None,
        initializer_offsets: None,
        getter: None,
        setter_visibility: None,
        promoted: false,
        jvm_static,
    };
    let field = property
        .signature
        .field
        .as_ref()
        .map(|signature| {
            if signature.name != *name {
                return Err(invalid("renamed backing field"));
            }
            let field = storage
                .find_field(signature)?
                .ok_or_else(|| invalid("missing JVM backing field"))?;
            if abstract_property
                || (field.access_flags & STATIC != 0) != static_field
                || (field.access_flags & FINAL != 0) == property.mutable()
                || (!property.constant() && field.access_flags & 0x0002 == 0)
                || field.access_flags & (0x0040 | 0x0080) != 0
            {
                return Err(invalid(
                    "JVM backing field flags do not match Kotlin property",
                ));
            }
            Ok((
                signature,
                field,
                storage.class.pool.utf8(field.descriptor_index)?,
            ))
        })
        .transpose()?;
    if let Some((_, member, _)) = field {
        state.field = Some(member);
        state.initializer = storage.constant(member, name)?.map(objects::Initializer::Expression);
    }
    if property.constant() != state.initializer.is_some()
        || (property.constant() && (property.mutable() || !static_field))
    {
        return Err(invalid(
            "constant property lacks a static literal ConstantValue",
        ));
    }
    if jvm_static && (field.is_none() || property.signature.getter.is_none()) {
        return Err(invalid("@JvmStatic property without a known backing field and getter"));
    }
    let implicit_flags = Flags(property.flags.0 & if jvm_static { 0x3e } else { 0x3f });
    let getter_flags = property
        .getter_flags
        .unwrap_or(implicit_flags);
    let setter_flags = property
        .setter_flags
        .unwrap_or(implicit_flags);
    if property.setter_parameter.is_some()
        || setter_flags.has(6)
        || getter_flags.0 & 0x181 != 0
        || setter_flags.0 & 0x181 != 0
        || getter_flags.visibility()? != property.flags.visibility()?
    {
        return Err(invalid("custom accessor modifiers or setter"));
    }
    let property_visibility = property.flags.visibility()?;
    let private = |vis| matches!(vis, Visibility::Private | Visibility::PrivateToThis);
    if let Some(signature) = &property.signature.getter {
        let getter = checked_method(
            bytecode,
            signature,
            static_accessor,
            abstract_property,
            false,
            name,
        )?;
        let descriptor = &signature.descriptor;
        if !descriptor.parameters.is_empty() || descriptor.return_type == JvmType::Void {
            return Err(invalid("invalid JVM getter signature"));
        }
        if let Some((field, _, raw)) = field {
            if getter_flags.has(6) || descriptor.return_type != field.descriptor {
                return Err(invalid("custom getter over a backing field"));
            }
            if let Some(singleton) = singleton {
                singleton.getter(getter, signature, field, raw, jvm_static, name)?;
            } else {
                bytecode.default_getter(getter, field, raw, name)?;
            }
        } else if !abstract_property {
            if !getter_flags.has(6) || property.mutable() {
                return Err(invalid("non-abstract property without backing field"));
            }
            let Body::Expression(expr, _) =
                bytecode.function(getter, descriptor, &[], &property.ty, properties, None, name, false)?
            else {
                return Err(invalid("getter has no return expression"));
            };
            state.getter = Some(expr);
        }
    } else if !(property.constant() || (field.is_some() && private(property_visibility))) {
        return Err(invalid("missing JVM getter"));
    }
    if property.mutable() && setter_flags.visibility()? != property_visibility {
        state.setter_visibility = Some(setter_flags.visibility()?);
    }
    if let Some(signature) = &property.signature.setter {
        let setter = checked_method(
            bytecode,
            signature,
            static_accessor,
            abstract_property,
            false,
            name,
        )?;
        let descriptor = &signature.descriptor;
        if !property.mutable()
            || descriptor.parameters.len() != 1
            || descriptor.return_type != JvmType::Void
        {
            return Err(invalid("invalid JVM setter signature"));
        }
        if let Some((field, _, raw)) = field {
            if descriptor.parameters[0] != field.descriptor {
                return Err(invalid("JVM setter and field type mismatch"));
            }
            if let Some(singleton) = singleton {
                singleton.setter(setter, signature, field, raw, jvm_static, name)?;
            } else {
                bytecode.default_setter(setter, field, raw, &property.ty, name)?;
            }
        } else if !abstract_property {
            return Err(invalid("setter without backing field"));
        }
    } else if property.mutable() && !(field.is_some() && private(setter_flags.visibility()?)) {
        return Err(invalid("missing JVM setter"));
    }
    Ok(state)
}

fn checked_method<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    signature: &JvmMethodSignature,
    static_member: bool,
    abstract_member: bool,
    external: bool,
    declaration: &str,
) -> Result<&'a Member<'data>, KotlinError> {
    let method = bytecode
        .find_method(signature)?
        .ok_or_else(|| error(declaration, "missing JVM method"))?;
    let flags = method.access_flags;
    if (flags & STATIC != 0) != static_member
        || (flags & ABSTRACT != 0) != abstract_member
        || (flags & NATIVE != 0) != external
    {
        return Err(error(
            declaration,
            "JVM method flags do not match Kotlin declaration",
        ));
    }
    if (abstract_member || external) && method.code(&bytecode.class.pool)?.is_some() {
        return Err(error(
            declaration,
            "unexpected JVM implementation of bodyless declaration",
        ));
    }
    Ok(method)
}

fn render_members<'a, 'data>(
    out: &mut String,
    bytecode: &Bytecode<'a, 'data>,
    types: &Types<'_>,
    plan: &Plan<'a, 'data, '_>,
    members: &PackageDeclaration,
    style: Style<'_>,
    group: Option<&ClassGroup<'_>>,
    mut location: Location<'_>,
    data_class: bool,
) -> Result<(), KotlinError> {
    for alias in &members.type_aliases {
        if alias.flags.has_annotations() || alias.flags.visibility()? == Visibility::Protected {
            return Err(error(&alias.name, "type alias modifiers or annotations"));
        }
        let types = types.local(&alias.name, &alias.type_parameters);
        out.push_str(style.indent);
        out.push_str(visibility(alias.flags.visibility()?)?);
        out.push_str("typealias ");
        identifier(out, &alias.name, &alias.name)?;
        type_parameters(out, &types, &alias.type_parameters, TypeParameters::Alias)?;
        out.push_str(" = ");
        types.write(out, &alias.underlying)?;
        out.push('\n');
    }
    let mut initializer_trace = if location.is_some()
        && let Some(member) = plan.initialization_method
        && plan.ordered.iter().any(|&index| plan.properties[index].initializer_offsets.is_some())
    {
        Some((
            trace::Trace::new(bytecode, member)?,
            bytecode.code(member, bytecode.owner)?.line_numbers(&bytecode.class.pool)?,
        ))
    } else {
        None
    };
    if let Some((_, line)) = &mut location {
        *line += trace::line_count(out);
    }
    let properties = plan.properties.iter().filter(|property| {
        !property.promoted && (property.initializer.is_none() || property.property.constant())
    }).chain(plan.ordered.iter().map(|&index| &plan.properties[index]));
    for property in properties {
        let start = out.len();
        if let Some((_, line)) = &location
            && let Some((trace, _)) = &mut initializer_trace
            && let Some(offsets) = &property.initializer_offsets
        {
            trace.offsets(offsets.clone(), *line);
        }
        render_property(out, types, property, plan.parameters, style, !plan.layout.file())?;
        if let Some((_, line)) = &mut location {
            *line += trace::line_count(&out[start..]);
        }
    }
    if let Some((trace, original)) = initializer_trace
        && let Some((map, _)) = &mut location
    {
        trace.finish(map, original);
    }
    for function in &members.functions {
        let kind = function.flags.member_kind();
        if kind == MemberKind::FakeOverride || (data_class && kind == MemberKind::Synthesized) {
            continue;
        }
        if !out.is_empty() && out.ends_with('\n') && !out.ends_with("\n\n") {
            out.push('\n');
            if let Some((_, line)) = &mut location {
                *line += 1;
            }
        }
        let start = out.len();
        render_function(
            out,
            bytecode,
            types,
            function,
            members,
            style,
            plan,
            group,
            location.as_mut().map(|(map, line)| (&mut **map, *line)),
        )?;
        if let Some((_, line)) = &mut location {
            *line += trace::line_count(&out[start..]);
        }
    }
    Ok(())
}

fn property_prefix(
    out: &mut String,
    property: &Property,
    interface: bool,
    explicit_final: bool,
) -> Result<(), KotlinError> {
    out.push_str(visibility(property.flags.visibility()?)?);
    if property.constant() {
        out.push_str("const ");
    }
    let kind = property.flags.modality();
    if explicit_final && kind == Modality::Final && !property.constant() {
        out.push_str("final ");
    } else {
        out.push_str(modality(kind, interface));
    }
    out.push_str(if property.mutable() { "var " } else { "val " });
    Ok(())
}

fn render_property(
    out: &mut String,
    types: &Types<'_>,
    planned: &PlannedProperty<'_, '_, '_>,
    parameters: &[ValueParameter],
    style: Style<'_>,
    class_member: bool,
) -> Result<(), KotlinError> {
    let property = planned.property;
    let types = types.local(&property.name, &[]);
    if planned.jvm_static {
        out.push_str(style.indent);
        out.push_str("@kotlin.jvm.JvmStatic\n");
    }
    out.push_str(style.indent);
    property_prefix(out, property, style.interface, class_member && !style.interface)?;
    identifier(out, &property.name, &property.name)?;
    out.push_str(": ");
    types.write(out, &property.ty)?;
    if let Some(initializer) = &planned.initializer {
        out.push_str(" = ");
        initializer.write(
            out,
            &property.ty,
            &property.signature.field.as_ref().unwrap().descriptor,
            parameters,
            &property.name,
        )?;
    }
    out.push('\n');
    if let Some(getter) = &planned.getter {
        out.push_str(style.indent);
        out.push_str(style.unit);
        out.push_str("get() = ");
        getter.write(
            out,
            &property.ty,
            &property
                .signature
                .getter
                .as_ref()
                .unwrap()
                .descriptor
                .return_type,
            &[],
            &property.name,
        )?;
        out.push('\n');
    }
    if let Some(visibility_value) = planned.setter_visibility {
        out.push_str(style.indent);
        out.push_str(style.unit);
        out.push_str(visibility(visibility_value)?);
        out.push_str("set\n");
    }
    Ok(())
}

fn render_function<'a, 'data>(
    out: &mut String,
    bytecode: &Bytecode<'a, 'data>,
    types: &Types<'_>,
    function: &Function,
    members: &PackageDeclaration,
    style: Style<'_>,
    plan: &Plan<'a, 'data, '_>,
    group: Option<&ClassGroup<'_>>,
    mut location: Location<'_>,
) -> Result<(), KotlinError> {
    let name = &function.name;
    let Style {
        indent,
        unit: indent_unit,
        interface,
    } = style;
    let types = types.local(name, &function.type_parameters);
    let flags = function.flags;
    let external = flags.has(12);
    let abstract_function = flags.modality() == Modality::Abstract;
    let inline = flags.has(10);
    let facade = plan.layout.file();
    let singleton = plan.layout.singleton();
    if flags.has_annotations() && singleton.is_none()
        || flags.has(13)
        || flags.has(14)
        || flags.has(16)
        || flags.member_kind() != MemberKind::Declaration
        || flags.modality() == Modality::Sealed
        || !function.context_receivers.is_empty()
        || !function.context_parameters.is_empty()
        || function.has_contract
        || (facade
            && (flags.modality() != Modality::Final
                || flags.visibility()? == Visibility::Protected))
    {
        return Err(types.unsupported("function modifiers, contract, or context parameters"));
    }
    let signature = function
        .signature
        .as_ref()
        .ok_or_else(|| types.unsupported("function lacks JVM identity"))?;
    let jvm_static = if let Some(singleton) = singleton {
        singleton.function_static(signature, flags.has_annotations(), name)?
    } else {
        false
    };
    let static_member = facade || jvm_static && singleton.is_some_and(|singleton| !singleton.is_companion());
    let method = checked_method(
        bytecode,
        signature,
        static_member,
        abstract_function,
        external,
        name,
    )?;
    let descriptor = &signature.descriptor;
    if descriptor.parameters.len()
        != function.parameters.len() + usize::from(function.receiver.is_some())
    {
        return Err(types.unsupported("JVM parameters do not match Kotlin function"));
    }
    let defaults = if function.receiver.is_none() {
        body::parameter_defaults(bytecode, signature, &function.parameters, !static_member, name)?
    } else {
        Vec::new()
    };
    let mut defaults = defaults.iter().peekable();
    let unit = function.returns.class_id() == Some("kotlin/Unit") && !function.returns.nullable;
    if (descriptor.return_type == JvmType::Void) != unit {
        return Err(types.unsupported("JVM return does not match Kotlin Unit"));
    }
    let overrides_any =
        !static_member && function.receiver.is_none() && overrides_any(&signature.name, descriptor);
    if overrides_any && (signature.name != *name || flags.visibility()? != Visibility::Public) {
        return Err(types.unsupported("invalid override of kotlin.Any method"));
    }
    let show_return =
        !unit || function.returns.abbreviated.is_some() || !function.returns.annotations.is_empty();
    if jvm_static {
        out.push_str(indent);
        out.push_str("@kotlin.jvm.JvmStatic\n");
        if let Some((_, header)) = &mut location {
            *header += 1;
        }
    }
    out.push_str(indent);
    out.push_str(visibility(flags.visibility()?)?);
    if overrides_any {
        if flags.modality() == Modality::Final {
            out.push_str("final ");
        }
        if abstract_function && !interface {
            out.push_str("abstract ");
        }
        out.push_str("override ");
    } else {
        out.push_str(modality(flags.modality(), interface));
    }
    for (enabled, keyword) in [
        (external, "external "),
        (inline, "inline "),
        (flags.has(11), "tailrec "),
        (flags.has(8), "operator "),
        (flags.has(9), "infix "),
    ] {
        if enabled {
            out.push_str(keyword);
        }
    }
    out.push_str("fun ");
    type_parameters(
        out,
        &types,
        &function.type_parameters,
        TypeParameters::Function { inline },
    )?;
    if !function.type_parameters.is_empty() {
        out.push(' ');
    }
    if let Some(receiver) = &function.receiver {
        types.receiver(out, receiver)?;
        out.push('.');
    }
    identifier(out, name, name)?;
    out.push('(');
    for (index, parameter) in function.parameters.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        let default = defaults
            .next_if(|(parameter, _)| *parameter == index)
            .map(|(_, value)| {
                (
                    value,
                    &descriptor.parameters[index],
                    function.parameters.as_slice(),
                )
            });
        value_parameter(out, &types, parameter, inline, default)?;
    }
    out.push(')');
    if show_return {
        out.push_str(": ");
        types.write(out, &function.returns)?;
    }
    type_constraints(out, &types, &function.type_parameters)?;
    if !abstract_function && !external {
        if descriptor.parameters.is_empty() && descriptor.return_type == JvmType::Void
            && let Some(singleton) = singleton
            && let Some(update) = singleton.int_update(method, name)?
        {
            if !plan.properties.iter().any(|state| {
                let property = state.property;
                property.name == update.field && property.mutable()
                    && !property.ty.nullable && property.ty.class_id() == Some("kotlin/Int")
                    && property.signature.field.as_ref().is_some_and(|field| {
                        field.descriptor == JvmType::Primitive(Primitive::Int)
                    })
            }) {
                return Err(types.unsupported("singleton update does not name a mutable Int property"));
            }
            out.push_str(" {\n");
            out.push_str(indent);
            out.push_str(indent_unit);
            identifier(out, update.field, name)?;
            out.push_str(if update.increment { "++\n" } else { "--\n" });
            out.push_str(indent);
            out.push_str("}\n");
            if let Some((map, header)) = location {
                let mut trace = trace::Trace::new(bytecode, method)?;
                let code = bytecode.code(method, name)?;
                let (ret, statement) = update.instructions.split_last().expect("update ends with return");
                for instruction in statement {
                    trace.instruction(instruction, header + 1);
                }
                trace.instruction(ret, header + 2);
                trace.finish(map, code.line_numbers(&bytecode.class.pool)?);
            }
            return Ok(());
        }
        match bytecode.function(
            method,
            descriptor,
            &function.parameters,
            &function.returns,
            plan.metadata_properties,
            Some(body::Extension::new(function, signature, method, members, group)?),
            name,
            location.is_some(),
        )? {
            Body::Empty => out.push_str(" {}"),
            Body::Expression(expr, expression_trace) => {
                if let (Some(expression_trace), Some((map, header))) = (expression_trace, location)
                {
                    out.push_str(" {\n");
                    out.push_str(indent);
                    out.push_str(indent_unit);
                    out.push_str("return ");
                    expr.write(
                        out,
                        &function.returns,
                        &descriptor.return_type,
                        &function.parameters,
                        name,
                    )?;
                    out.push('\n');
                    out.push_str(indent);
                    out.push('}');
                    let mut trace = trace::Trace::new(bytecode, method)?;
                    trace.offsets(expression_trace.offsets, header + 1);
                    trace.finish(map, expression_trace.lines);
                } else {
                    out.push_str(" = ");
                    expr.write(
                        out,
                        &function.returns,
                        &descriptor.return_type,
                        &function.parameters,
                        name,
                    )?;
                }
            }
            Body::Statements(block) => {
                out.push_str(" {\n");
                let mut trace = location
                    .as_ref()
                    .map(|_| trace::Trace::new(bytecode, method))
                    .transpose()?;
                let mut line = location.as_ref().map_or(0, |(_, header)| *header + 1);
                for statement in block.statements {
                    out.push_str(indent);
                    out.push_str(indent_unit);
                    statement.write(out, &function.parameters, name)?;
                    out.push('\n');
                    if let Some(trace) = &mut trace {
                        statement.trace(bytecode, &block.instructions, |instruction| {
                            trace.instruction(instruction, line);
                        })?;
                        line += 1;
                    }
                }
                out.push_str(indent);
                out.push('}');
                if let (Some(mut trace), Some((map, _))) = (trace, location) {
                    if block.implicit_return {
                        trace.instruction(
                            block
                                .instructions
                                .last()
                                .expect("statement block ends with return"),
                            line,
                        );
                    }
                    trace.finish(map, block.lines);
                }
            }
            Body::Switch(block) => {
                let mut trace = location
                    .as_ref()
                    .map(|_| trace::Trace::new(bytecode, method))
                    .transpose()?;
                block.write(
                    out,
                    (&function.returns, &descriptor.return_type),
                    &function.parameters,
                    name,
                    indent,
                    indent_unit,
                    |instruction, line| {
                        if let (Some(trace), Some((_, header))) = (&mut trace, &location) {
                            trace.instruction(instruction, *header + line);
                        }
                    },
                )?;
                if let (Some(trace), Some((map, _))) = (trace, location) {
                    trace.finish(map, block.lines);
                }
            }
            Body::Decision(body) => {
                let mut trace = location
                    .as_ref()
                    .map(|_| trace::Trace::new(bytecode, method))
                    .transpose()?;
                body.write(
                    out,
                    &function.parameters,
                    name,
                    indent,
                    indent_unit,
                    |instruction, line| {
                        if let (Some(trace), Some((_, header))) = (&mut trace, &location) {
                            trace.instruction(instruction, *header + line);
                        }
                    },
                )?;
                if let (Some(trace), Some((map, _))) = (trace, location) {
                    trace.finish(map, body.lines);
                }
            }
            Body::Loop(body) => {
                let mut trace = location
                    .as_ref()
                    .map(|_| trace::Trace::new(bytecode, method))
                    .transpose()?;
                body.write(
                    out,
                    &function.parameters,
                    name,
                    indent,
                    indent_unit,
                    |instruction, line| {
                        if let (Some(trace), Some((_, header))) = (&mut trace, &location) {
                            trace.instruction(instruction, *header + line);
                        }
                    },
                )?;
                if let (Some(trace), Some((map, _))) = (trace, location) {
                    trace.finish(map, body.lines);
                }
            }
            Body::Try(body) => {
                let mut trace = location
                    .as_ref()
                    .map(|_| trace::Trace::new(bytecode, method))
                    .transpose()?;
                body.write(
                    out,
                    (&function.returns, &descriptor.return_type),
                    &function.parameters,
                    name,
                    indent,
                    indent_unit,
                    |instruction, line| {
                        if let (Some(trace), Some((_, header))) = (&mut trace, &location) {
                            trace.instruction(instruction, *header + line);
                        }
                    },
                )?;
                if let (Some(trace), Some((map, _))) = (trace, location) {
                    trace.finish(map, body.lines);
                }
            }
        }
    }
    out.push('\n');
    Ok(())
}

fn overrides_any(name: &str, descriptor: &MethodDescriptor) -> bool {
    match (
        name,
        descriptor.parameters.as_slice(),
        &descriptor.return_type,
    ) {
        ("equals", [JvmType::Object(param)], JvmType::Primitive(Primitive::Boolean)) => {
            param == "java/lang/Object"
        }
        ("hashCode", [], JvmType::Primitive(Primitive::Int)) => true,
        ("toString", [], JvmType::Object(returns)) => returns == "java/lang/String",
        _ => false,
    }
}

#[derive(Clone, Copy)]
enum TypeParameters {
    Class,
    Function { inline: bool },
    Alias,
}

fn type_parameters(
    out: &mut String,
    types: &Types<'_>,
    parameters: &[TypeParameter],
    kind: TypeParameters,
) -> Result<(), KotlinError> {
    if parameters.is_empty() {
        return Ok(());
    }
    out.push('<');
    for (index, parameter) in parameters.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        if !parameter.annotations.is_empty()
            || parameters[..index]
                .iter()
                .any(|other| other.id == parameter.id || other.name == parameter.name)
            || (parameter.variance != Variance::Invariant && !matches!(kind, TypeParameters::Class))
            || (parameter.reified && !matches!(kind, TypeParameters::Function { inline: true }))
        {
            return Err(types.unsupported("unsupported or repeated type parameter"));
        }
        if parameter.reified {
            out.push_str("reified ");
        }
        out.push_str(variance_prefix(parameter.variance));
        identifier(out, &parameter.name, types.declaration)?;
        match parameter.upper_bounds.as_slice() {
            [bound] if bound.class_id() == Some("kotlin/Any") && bound.nullable => {}
            [bound] if !matches!(kind, TypeParameters::Alias) => {
                out.push_str(" : ");
                types.write(out, bound)?;
            }
            [_bound, ..] if matches!(kind, TypeParameters::Alias) => {
                return Err(types.unsupported("type alias constraints"));
            }
            _ => {}
        }
    }
    out.push('>');
    Ok(())
}

fn type_constraints(
    out: &mut String,
    types: &Types<'_>,
    parameters: &[TypeParameter],
) -> Result<(), KotlinError> {
    let mut first = true;
    for parameter in parameters
        .iter()
        .filter(|param| param.upper_bounds.len() > 1)
    {
        for bound in &parameter.upper_bounds {
            out.push_str(if first { " where " } else { ", " });
            first = false;
            identifier(out, &parameter.name, types.declaration)?;
            out.push_str(" : ");
            types.write(out, bound)?;
        }
    }
    Ok(())
}

fn value_parameter(
    out: &mut String,
    types: &Types<'_>,
    parameter: &ValueParameter,
    inline: bool,
    default: Option<(&Expr<'_>, &JvmType, &[ValueParameter])>,
) -> Result<(), KotlinError> {
    let crossinline = parameter.flags.has(2);
    let noinline = parameter.flags.has(3);
    if parameter.flags.has_annotations()
        || parameter.flags.has(1) != default.is_some()
        || ((crossinline || noinline) && (!inline || (crossinline && noinline)))
    {
        return Err(
            types.unsupported("annotated, default, or conflicting value parameter modifiers")
        );
    }
    if crossinline {
        out.push_str("crossinline ");
    }
    if noinline {
        out.push_str("noinline ");
    }
    if parameter.vararg_element.is_some() {
        out.push_str("vararg ");
    }
    identifier(out, &parameter.name, types.declaration)?;
    out.push_str(": ");
    types.write(
        out,
        parameter.vararg_element.as_ref().unwrap_or(&parameter.ty),
    )?;
    if let Some((value, descriptor, parameters)) = default {
        out.push_str(" = ");
        value.write(
            out,
            &parameter.ty,
            descriptor,
            parameters,
            types.declaration,
        )?;
    }
    Ok(())
}

fn modality(modality: Modality, interface: bool) -> &'static str {
    match modality {
        Modality::Open if !interface => "open ",
        Modality::Abstract if !interface => "abstract ",
        Modality::Sealed => "sealed ",
        _ => "",
    }
}

fn error(declaration: &str, feature: &'static str) -> KotlinError {
    KotlinError::unsupported(declaration, feature)
}
