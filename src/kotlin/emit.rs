// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::collections::HashMap;

use crate::{
    classfile::{ClassFile, ElementValue, Member},
    descriptor::{MethodDescriptor, Primitive, Type as JvmType},
};

use super::{
    ClassDeclaration, ClassKind, Constructor, Declaration, Flags, Function, JvmMethodSignature,
    KotlinError, MemberKind, Metadata, Modality, PackageDeclaration, Property, TypeParameter,
    ValueParameter, Variance, Visibility,
    body::{self, ABSTRACT, Body, Bytecode, Expr, FINAL, NATIVE, STATIC},
    syntax::{INDENT, Types, identifier, qualified, variance_prefix, visibility},
};

pub(super) fn render(class: &ClassFile<'_>, metadata: &Metadata) -> Result<String, KotlinError> {
    let owner = class.pool.class_name(class.this_class)?;
    let bytecode = Bytecode { class, owner };
    let (jvm_package, simple_name) = owner.rsplit_once('/').unwrap_or(("", owner));
    let (package, declaration, members) = match &metadata.declaration {
        Declaration::Class(declaration) => (declaration.name.package(), Some(declaration), &declaration.members),
        Declaration::FileFacade(members) => (jvm_package, None, members),
        Declaration::Synthetic(_) => return Err(error(owner, "synthetic class")),
        Declaration::MultifileFacade(_) => return Err(error(owner, "multifile facade requires its package parts")),
        Declaration::MultifilePart(_) => return Err(error(owner, "multifile package part")),
    };
    if let Some(name) = metadata.header.package_name.as_deref().filter(|name| !name.is_empty())
        && !name.split('.').eq(package.split('/'))
    {
        return Err(error(owner, "relocated JVM package"));
    }
    let mut out = String::new();
    file_annotations(&mut out, &bytecode, declaration.is_none(), simple_name)?;
    if !package.is_empty() {
        out.push_str("package ");
        qualified(&mut out, package, owner)?;
        out.push_str("\n\n");
    }
    let types = Types {
        declaration: owner, package, owner: declaration.map(|decl| &decl.name),
        owner_parameters: declaration.map_or(&[], |decl| &decl.type_parameters), local_parameters: &[],
    };
    if let Some(declaration) = declaration {
        render_class(&mut out, &bytecode, &types, declaration)?;
    } else {
        if class.methods.iter().any(|method| class.pool.utf8(method.name_index).is_ok_and(|name| name == "<init>")) {
            return Err(error(owner, "file facade has an instance constructor"));
        }
        let plan = Plan::new(&bytecode, members, None, true)?;
        render_members(&mut out, &bytecode, &types, &plan, members, "", false)?;
    }
    Ok(out)
}

fn file_annotations(out: &mut String, bytecode: &Bytecode<'_, '_>, facade: bool, simple_name: &str) -> Result<(), KotlinError> {
    let pool = &bytecode.class.pool;
    for visible in [true, false] {
        for annotation in bytecode.class.annotations(visible)? {
            match pool.utf8(annotation.type_index)? {
                "Lkotlin/Metadata;" | "Lkotlin/jvm/internal/SourceDebugExtension;" => {}
                "Lkotlin/jvm/JvmName;" if facade => {
                    let [(name, ElementValue::Constant { tag: b's', index })] = annotation.elements.as_slice() else {
                        return Err(error(bytecode.owner, "invalid @file:JvmName"));
                    };
                    if pool.utf8(*name)? != "name" || pool.utf8(*index)? != simple_name {
                        return Err(error(bytecode.owner, "invalid @file:JvmName"));
                    }
                    out.push_str("@file:JvmName(");
                    body::write_string(out, simple_name.encode_utf16());
                    out.push_str(")\n");
                }
                _ => return Err(error(bytecode.owner, "class or file annotations")),
            }
        }
    }
    if !out.is_empty() { out.push('\n'); }
    Ok(())
}

fn render_class(out: &mut String, bytecode: &Bytecode<'_, '_>, types: &Types<'_>, declaration: &ClassDeclaration) -> Result<(), KotlinError> {
    let invalid = |feature| error(bytecode.owner, feature);
    if declaration.name.local || declaration.name.relative_name().contains('.')
        || declaration.name.jvm_internal_name() != bytecode.owner || !declaration.nested_names.is_empty()
        || declaration.companion_name.is_some()
    {
        return Err(invalid("nested, local or companion classes require class-group analysis"));
    }
    if declaration.flags.has_annotations() || declaration.flags.0 & (0b11_1111 << 9) != 0
        || !declaration.context_receivers.is_empty() || !declaration.enum_entries.is_empty()
    {
        return Err(invalid("class modifiers, annotations, or context receivers"));
    }
    let interface = match declaration.kind { ClassKind::Class => false, ClassKind::Interface => true,
        _ => return Err(invalid("class kind")), };
    if interface != (bytecode.class.access_flags & 0x0200 != 0) {
        return Err(invalid("metadata class kind does not match the JVM class"));
    }
    if bytecode.class.super_class == 0 || bytecode.class.pool.class_name(bytecode.class.super_class)? != "java/lang/Object"
        || !bytecode.class.interfaces.is_empty() || declaration.supertypes.iter().any(|ty| ty.class_id() != Some("kotlin/Any"))
    {
        return Err(invalid("inherited declarations require supertype context"));
    }
    if !declaration.members.type_aliases.is_empty() { return Err(invalid("nested type aliases")); }
    let constructor = match declaration.constructors.as_slice() {
        [] if interface => None,
        [constructor] if !interface && !constructor.flags.has(4) && !constructor.flags.has_annotations() => Some(constructor),
        _ => return Err(invalid("nontrivial constructor declarations")),
    };
    let hierarchy = declaration.flags.modality();
    if hierarchy == Modality::Sealed || (interface && hierarchy != Modality::Abstract) {
        return Err(invalid("sealed or non-abstract interface declarations"));
    }
    if declaration.flags.visibility()? == Visibility::Protected {
        return Err(invalid("protected top-level class"));
    }
    let plan = Plan::new(bytecode, &declaration.members, constructor, false)?;
    out.push_str(visibility(declaration.flags.visibility()?)?);
    out.push_str(modality(hierarchy, interface));
    out.push_str(if interface { "interface " } else { "class " });
    identifier(out, declaration.name.relative_name(), bytecode.owner)?;
    type_parameters(out, types, &declaration.type_parameters, TypeParameters::Class)?;
    if let Some(constructor) = constructor {
        let constructor_visibility = constructor.flags.visibility()?;
        if constructor_visibility != Visibility::Public {
            out.push(' ');
            out.push_str(visibility(constructor_visibility)?);
            out.push_str("constructor");
        }
        if constructor_visibility != Visibility::Public || !constructor.parameters.is_empty() {
            out.push('(');
            for (index, parameter) in constructor.parameters.iter().enumerate() {
                if index != 0 { out.push_str(", "); }
                if let Some(prop) = plan.promoted[index] {
                    let property = plan.properties[prop].property;
                    property_prefix(out, property, false)?;
                }
                value_parameter(out, types, parameter, false)?;
            }
            out.push(')');
        }
    }
    type_constraints(out, types, &declaration.type_parameters)?;
    let mut members = String::new();
    render_members(&mut members, bytecode, types, &plan, &declaration.members, INDENT, interface)?;
    if members.is_empty() {
        out.push('\n');
    } else {
        out.push_str(" {\n");
        out.push_str(&members);
        out.push_str("}\n");
    }
    Ok(())
}

type Field<'a, 'data> = &'a Member<'data>;

struct PlannedProperty<'a, 'data, 'metadata> {
    property: &'metadata Property,
    field: Option<Field<'a, 'data>>,
    initializer: Option<Expr<'a>>,
    getter: Option<Expr<'a>>,
    setter_visibility: Option<Visibility>,
    promoted: bool,
}

struct Plan<'a, 'data, 'metadata> {
    properties: Vec<PlannedProperty<'a, 'data, 'metadata>>,
    ordered: Vec<usize>,
    promoted: Vec<Option<usize>>,
    parameters: &'metadata [ValueParameter],
    static_members: bool,
}

impl<'a, 'data, 'metadata> Plan<'a, 'data, 'metadata> {
    fn new(bytecode: &Bytecode<'a, 'data>, members: &'metadata PackageDeclaration,
        constructor: Option<&'metadata Constructor>, facade: bool,
    ) -> Result<Self, KotlinError> {
        let mut properties = members.properties.iter().filter(|p| p.flags.member_kind() != MemberKind::FakeOverride)
            .map(|p| plan_property(bytecode, p, facade)).collect::<Result<Vec<_>, _>>()?;
        let mut field_index = HashMap::new();
        for (index, property) in properties.iter().enumerate() {
            if let Some(field) = property.field {
                let pool = &bytecode.class.pool;
                if field_index.insert((pool.utf8(field.name_index)?, pool.utf8(field.descriptor_index)?), index).is_some() {
                    return Err(error(bytecode.owner, "properties share a backing field"));
                }
            }
        }
        if field_index.len() != bytecode.class.fields.len() {
            return Err(error(bytecode.owner, "JVM fields without Kotlin declarations"));
        }
        let parameters = constructor.map_or(&[][..], |con| con.parameters.as_slice());
        let mut promoted = vec![None; parameters.len()];
        let mut ordered = Vec::new();
        let static_initializer = JvmMethodSignature {
            name: "<clinit>".to_owned(),
            descriptor: MethodDescriptor { parameters: Vec::new(), return_type: JvmType::Void },
        };
        let clinit = bytecode.find_method(&static_initializer)?.map(|method| bytecode.initialization(method,
            &static_initializer.descriptor, &[], None, bytecode.owner)).transpose()?;
        if !facade && clinit.as_ref().is_some_and(|assignments| !assignments.is_empty()) {
            return Err(error(bytecode.owner, "static initializer inside a Kotlin class"));
        }
        let assignments = if let Some(constructor) = constructor {
            let signature = constructor.signature.as_ref().filter(|s| s.name == "<init>")
                .ok_or_else(|| error(bytecode.owner, "constructor lacks JVM identity"))?;
            let method = bytecode.find_method(signature)?.ok_or_else(|| error(bytecode.owner, "missing JVM constructor"))?;
            bytecode.initialization(method, &signature.descriptor, parameters, Some("java/lang/Object"), bytecode.owner)?
        } else { clinit.unwrap_or_default() };
        let mut next_candidate = Some(0);
        for assignment in assignments {
            let Some(&index) = field_index.get(&(assignment.field, assignment.descriptor)) else {
                return Err(error(bytecode.owner, "initializer writes an undeclared property"));
            };
            let state = &mut properties[index];
            if state.initializer.is_some() || state.promoted {
                return Err(error(&state.property.name, "multiple backing field initializations"));
            }
            let descriptor = &state.property.signature.field.as_ref().unwrap().descriptor;
            if let Some(parameter) = assignment.value.parameter(descriptor).filter(|&p| next_candidate.is_some_and(|min| p >= min))
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
                ordered.push(index);
                next_candidate = None;
            }
        }
        for state in &properties {
            if state.field.is_some() && state.initializer.is_none() && !state.promoted {
                return Err(error(&state.property.name, "no proven backing field initializer"));
            }
        }
        Ok(Self { properties, ordered, promoted, parameters, static_members: facade })
    }
}

fn plan_property<'a, 'data, 'metadata>(bytecode: &Bytecode<'a, 'data>, property: &'metadata Property,
    static_member: bool,
) -> Result<PlannedProperty<'a, 'data, 'metadata>, KotlinError> {
    let name = &property.name;
    let invalid = |feature| error(name, feature);
    if property.flags.has_annotations() || property.flags.member_kind() != MemberKind::Declaration
        || property.flags.has(14) || property.flags.has(16) || property.flags.has(17)
        || property.late_init() || property.delegated() || property.jvm_flags != 0
        || property.signature.annotations_method.is_some() || property.signature.delegate_method.is_some()
        || property.receiver.is_some() || !property.type_parameters.is_empty()
        || !property.context_receivers.is_empty() || !property.context_parameters.is_empty()
    {
        return Err(invalid("property modifiers, extension, annotations, or context parameters"));
    }
    if static_member && (property.flags.modality() != Modality::Final || property.flags.visibility()? == Visibility::Protected) {
        return Err(invalid("non-final or protected top-level property"));
    }
    let abstract_property = property.flags.modality() == Modality::Abstract;
    let mut state = PlannedProperty { property, field: None, initializer: None, getter: None, setter_visibility: None, promoted: false };
    let field = property.signature.field.as_ref().map(|signature| {
        if signature.name != *name { return Err(invalid("renamed backing field")); }
        let field = bytecode.find_field(signature)?.ok_or_else(|| invalid("missing JVM backing field"))?;
        if abstract_property || (field.access_flags & STATIC != 0) != static_member
            || (field.access_flags & FINAL != 0) == property.mutable()
            || (!property.constant() && field.access_flags & 0x0002 == 0)
            || field.access_flags & (0x0040 | 0x0080) != 0
        {
            return Err(invalid("JVM backing field flags do not match Kotlin property"));
        }
        Ok((signature, field, bytecode.class.pool.utf8(field.descriptor_index)?))
    }).transpose()?;
    if let Some((_, member, _)) = field {
        state.field = Some(member);
        state.initializer = bytecode.constant(member, name)?;
    }
    if property.constant() != state.initializer.is_some() || (property.constant() && (property.mutable() || !static_member)) {
        return Err(invalid("constant property lacks a static literal ConstantValue"));
    }
    let getter_flags = property.getter_flags.unwrap_or(Flags(property.flags.0 & 0x3f));
    let setter_flags = property.setter_flags.unwrap_or(Flags(property.flags.0 & 0x3f));
    if property.setter_parameter.is_some() || setter_flags.has(6) || getter_flags.0 & 0x181 != 0
        || setter_flags.0 & 0x181 != 0 || getter_flags.visibility()? != property.flags.visibility()?
    {
        return Err(invalid("custom accessor modifiers or setter"));
    }
    let property_visibility = property.flags.visibility()?;
    let private = |vis| matches!(vis, Visibility::Private | Visibility::PrivateToThis);
    if let Some(signature) = &property.signature.getter {
        let getter = checked_method(bytecode, signature, static_member, abstract_property, false, name)?;
        let descriptor = &signature.descriptor;
        if !descriptor.parameters.is_empty() || descriptor.return_type == JvmType::Void {
            return Err(invalid("invalid JVM getter signature"));
        }
        if let Some((field, _, raw)) = field {
            if getter_flags.has(6) || descriptor.return_type != field.descriptor {
                return Err(invalid("custom getter over a backing field"));
            }
            bytecode.default_getter(getter, field, raw, name)?;
        } else if !abstract_property {
            if !getter_flags.has(6) || property.mutable() { return Err(invalid("non-abstract property without backing field")); }
            let Body::Expression(expr) = bytecode.function(getter, descriptor, &[], name, false)? else {
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
        let setter = checked_method(bytecode, signature, static_member, abstract_property, false, name)?;
        let descriptor = &signature.descriptor;
        if !property.mutable() || descriptor.parameters.len() != 1 || descriptor.return_type != JvmType::Void {
            return Err(invalid("invalid JVM setter signature"));
        }
        if let Some((field, _, raw)) = field {
            if descriptor.parameters[0] != field.descriptor { return Err(invalid("JVM setter and field type mismatch")); }
            bytecode.default_setter(setter, field, raw, &property.ty, name)?;
        } else if !abstract_property {
            return Err(invalid("setter without backing field"));
        }
    } else if property.mutable() && !(field.is_some() && private(setter_flags.visibility()?)) {
        return Err(invalid("missing JVM setter"));
    }
    Ok(state)
}

fn checked_method<'a, 'data>(bytecode: &Bytecode<'a, 'data>, signature: &JvmMethodSignature, static_member: bool,
    abstract_member: bool, external: bool, declaration: &str,
) -> Result<&'a Member<'data>, KotlinError> {
    let method = bytecode.find_method(signature)?.ok_or_else(|| error(declaration, "missing JVM method"))?;
    let flags = method.access_flags;
    if (flags & STATIC != 0) != static_member || (flags & ABSTRACT != 0) != abstract_member
        || (flags & NATIVE != 0) != external
    {
        return Err(error(declaration, "JVM method flags do not match Kotlin declaration"));
    }
    if (abstract_member || external) && method.code(&bytecode.class.pool)?.is_some() {
        return Err(error(declaration, "unexpected JVM implementation of bodyless declaration"));
    }
    Ok(method)
}

fn render_members(out: &mut String, bytecode: &Bytecode<'_, '_>, types: &Types<'_>, plan: &Plan<'_, '_, '_>,
    members: &PackageDeclaration, indent: &str, interface: bool,
) -> Result<(), KotlinError> {
    for alias in &members.type_aliases {
        if alias.flags.has_annotations() || alias.flags.visibility()? == Visibility::Protected {
            return Err(error(&alias.name, "type alias modifiers or annotations"));
        }
        let types = types.local(&alias.name, &alias.type_parameters);
        out.push_str(indent);
        out.push_str(visibility(alias.flags.visibility()?)?);
        out.push_str("typealias ");
        identifier(out, &alias.name, &alias.name)?;
        type_parameters(out, &types, &alias.type_parameters, TypeParameters::Alias)?;
        out.push_str(" = ");
        types.write(out, &alias.underlying)?;
        out.push('\n');
    }
    for property in &plan.properties {
        if !property.promoted && (property.initializer.is_none() || property.property.constant()) {
            render_property(out, types, property, plan.parameters, indent, interface)?;
        }
    }
    for &index in &plan.ordered {
        render_property(out, types, &plan.properties[index], plan.parameters, indent, interface)?;
    }
    for function in &members.functions {
        if function.flags.member_kind() == MemberKind::FakeOverride { continue; }
        if !out.is_empty() && out.ends_with('\n') && !out.ends_with("\n\n") { out.push('\n'); }
        render_function(out, bytecode, types, function, indent, plan.static_members, interface)?;
    }
    Ok(())
}

fn property_prefix(out: &mut String, property: &Property, interface: bool) -> Result<(), KotlinError> {
    out.push_str(visibility(property.flags.visibility()?)?);
    if property.constant() { out.push_str("const "); }
    out.push_str(modality(property.flags.modality(), interface));
    out.push_str(if property.mutable() { "var " } else { "val " });
    Ok(())
}

fn render_property(out: &mut String, types: &Types<'_>, planned: &PlannedProperty<'_, '_, '_>, parameters: &[ValueParameter],
    indent: &str, interface: bool,
) -> Result<(), KotlinError> {
    let property = planned.property;
    let types = types.local(&property.name, &[]);
    out.push_str(indent);
    property_prefix(out, property, interface)?;
    identifier(out, &property.name, &property.name)?;
    out.push_str(": ");
    types.write(out, &property.ty)?;
    if let Some(initializer) = &planned.initializer {
        out.push_str(" = ");
        initializer.write(out, &property.ty, &property.signature.field.as_ref().unwrap().descriptor, parameters, &property.name)?;
    }
    out.push('\n');
    if let Some(getter) = &planned.getter {
        out.push_str(indent);
        out.push_str(INDENT);
        out.push_str("get() = ");
        getter.write(out, &property.ty, &property.signature.getter.as_ref().unwrap().descriptor.return_type, &[], &property.name)?;
        out.push('\n');
    }
    if let Some(visibility_value) = planned.setter_visibility {
        out.push_str(indent);
        out.push_str(INDENT);
        out.push_str(visibility(visibility_value)?);
        out.push_str("set\n");
    }
    Ok(())
}

fn render_function(out: &mut String, bytecode: &Bytecode<'_, '_>, types: &Types<'_>, function: &Function,
    indent: &str, facade: bool, interface: bool,
) -> Result<(), KotlinError> {
    let name = &function.name;
    let types = types.local(name, &function.type_parameters);
    let flags = function.flags;
    let external = flags.has(12);
    let abstract_function = flags.modality() == Modality::Abstract;
    let inline = flags.has(10);
    if flags.has_annotations() || flags.has(13) || flags.has(14) || flags.has(16)
        || flags.member_kind() != MemberKind::Declaration || flags.modality() == Modality::Sealed
        || !function.context_receivers.is_empty() || !function.context_parameters.is_empty() || function.has_contract
        || (facade && (flags.modality() != Modality::Final || flags.visibility()? == Visibility::Protected))
        || (function.receiver.is_some() && !(external || abstract_function))
    {
        return Err(types.unsupported("function modifiers, contract, extension body, or context parameters"));
    }
    let signature = function.signature.as_ref().ok_or_else(|| types.unsupported("function lacks JVM identity"))?;
    let method = checked_method(bytecode, signature, facade, abstract_function, external, name)?;
    let descriptor = &signature.descriptor;
    if descriptor.parameters.len() != function.parameters.len() + usize::from(function.receiver.is_some()) {
        return Err(types.unsupported("JVM parameters do not match Kotlin function"));
    }
    let unit = function.returns.class_id() == Some("kotlin/Unit") && !function.returns.nullable;
    if (descriptor.return_type == JvmType::Void) != unit {
        return Err(types.unsupported("JVM return does not match Kotlin Unit"));
    }
    let overrides_any = !facade && function.receiver.is_none() && overrides_any(&signature.name, descriptor);
    if overrides_any && (signature.name != *name || flags.visibility()? != Visibility::Public) {
        return Err(types.unsupported("invalid override of kotlin.Any method"));
    }
    let show_return = !unit || function.returns.abbreviated.is_some() || !function.returns.annotations.is_empty();
    out.push_str(indent);
    out.push_str(visibility(flags.visibility()?)?);
    if overrides_any {
        if flags.modality() == Modality::Final { out.push_str("final "); }
        if abstract_function && !interface { out.push_str("abstract "); }
        out.push_str("override ");
    } else {
        out.push_str(modality(flags.modality(), interface));
    }
    for (enabled, keyword) in [(external, "external "), (inline, "inline "), (flags.has(11), "tailrec "),
        (flags.has(8), "operator "), (flags.has(9), "infix ")]
    {
        if enabled { out.push_str(keyword); }
    }
    out.push_str("fun ");
    type_parameters(out, &types, &function.type_parameters, TypeParameters::Function { inline })?;
    if !function.type_parameters.is_empty() { out.push(' '); }
    if let Some(receiver) = &function.receiver {
        types.receiver(out, receiver)?;
        out.push('.');
    }
    identifier(out, name, name)?;
    out.push('(');
    for (index, parameter) in function.parameters.iter().enumerate() {
        if index != 0 { out.push_str(", "); }
        value_parameter(out, &types, parameter, inline)?;
    }
    out.push(')');
    if show_return {
        out.push_str(": ");
        types.write(out, &function.returns)?;
    }
    type_constraints(out, &types, &function.type_parameters)?;
    if !abstract_function && !external {
        match bytecode.function(method, descriptor, &function.parameters, name, false)? {
            Body::Empty => out.push_str(" {}"),
            Body::Expression(expr) => {
                out.push_str(" = ");
                expr.write(out, &function.returns, &descriptor.return_type, &function.parameters, name)?;
            }
            Body::Statements(block) => {
                out.push_str(" {\n");
                for statement in block.statements {
                    out.push_str(indent);
                    out.push_str(INDENT);
                    statement.write(out, &function.parameters, name)?;
                    out.push('\n');
                }
                out.push_str(indent);
                out.push('}');
            }
        }
    }
    out.push('\n');
    Ok(())
}

fn overrides_any(name: &str, descriptor: &MethodDescriptor) -> bool {
    match (name, descriptor.parameters.as_slice(), &descriptor.return_type) {
        ("equals", [JvmType::Object(param)], JvmType::Primitive(Primitive::Boolean)) => param == "java/lang/Object",
        ("hashCode", [], JvmType::Primitive(Primitive::Int)) => true,
        ("toString", [], JvmType::Object(returns)) => returns == "java/lang/String",
        _ => false,
    }
}

#[derive(Clone, Copy)]
enum TypeParameters { Class, Function { inline: bool }, Alias }

fn type_parameters(out: &mut String, types: &Types<'_>, parameters: &[TypeParameter], kind: TypeParameters) -> Result<(), KotlinError> {
    if parameters.is_empty() { return Ok(()); }
    out.push('<');
    for (index, parameter) in parameters.iter().enumerate() {
        if index != 0 { out.push_str(", "); }
        if !parameter.annotations.is_empty() || parameters[..index].iter().any(|other| other.id == parameter.id || other.name == parameter.name)
            || (parameter.variance != Variance::Invariant && !matches!(kind, TypeParameters::Class))
            || (parameter.reified && !matches!(kind, TypeParameters::Function { inline: true }))
        {
            return Err(types.unsupported("unsupported or repeated type parameter"));
        }
        if parameter.reified { out.push_str("reified "); }
        out.push_str(variance_prefix(parameter.variance));
        identifier(out, &parameter.name, types.declaration)?;
        match parameter.upper_bounds.as_slice() {
            [bound] if bound.class_id() == Some("kotlin/Any") && bound.nullable => {}
            [bound] if !matches!(kind, TypeParameters::Alias) => { out.push_str(" : "); types.write(out, bound)?; }
            [_bound, ..] if matches!(kind, TypeParameters::Alias) => return Err(types.unsupported("type alias constraints")),
            _ => {}
        }
    }
    out.push('>');
    Ok(())
}

fn type_constraints(out: &mut String, types: &Types<'_>, parameters: &[TypeParameter]) -> Result<(), KotlinError> {
    let mut first = true;
    for parameter in parameters.iter().filter(|param| param.upper_bounds.len() > 1) {
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

fn value_parameter(out: &mut String, types: &Types<'_>, parameter: &ValueParameter, inline: bool) -> Result<(), KotlinError> {
    let crossinline = parameter.flags.has(2);
    let noinline = parameter.flags.has(3);
    if parameter.flags.has_annotations() || parameter.flags.has(1)
        || ((crossinline || noinline) && (!inline || (crossinline && noinline)))
    {
        return Err(types.unsupported("annotated, default, or conflicting value parameter modifiers"));
    }
    if crossinline { out.push_str("crossinline "); }
    if noinline { out.push_str("noinline "); }
    if parameter.vararg_element.is_some() { out.push_str("vararg "); }
    identifier(out, &parameter.name, types.declaration)?;
    out.push_str(": ");
    types.write(out, parameter.vararg_element.as_ref().unwrap_or(&parameter.ty))
}

fn modality(modality: Modality, interface: bool) -> &'static str {
    match modality {
        Modality::Open if !interface => "open ",
        Modality::Abstract if !interface => "abstract ",
        Modality::Sealed => "sealed ",
        _ => "",
    }
}

fn error(declaration: &str, feature: &'static str) -> KotlinError { KotlinError::unsupported(declaration, feature) }
