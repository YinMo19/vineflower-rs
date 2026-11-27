use std::{io, sync::Arc};

use crate::{
    decompiler::exps::ExprKind,
    engine::{Cx, class_nodes::ClassNodeId},
    kotlin::{
        declarations::resolve,
        metadata::{flags, proto::class::Kind},
    },
    structs::StructClass,
    util::interpreter_util::make_unique_key,
};

use super::{ClassElement, FieldElement, Hidden, bind, invalid_data, parse_metadata_for, state};

/// Associate JVM companion members after initializer extraction, in the
/// order of KotlinObjectProcessors.parseWithCompanion and markObjectInstance.
pub fn process_objects(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    let class = Arc::clone(&cx.class_nodes[node].class);
    let Some(ClassElement::Class(data)) = cx
        .kotlin_members
        .as_ref()
        .and_then(|members| members.class(&class))
        .cloned()
    else {
        return Ok(());
    };

    if let Some(companion_name) = data.proto.companion_object_name {
        let names = data
            .names
            .as_ref()
            .ok_or_else(|| invalid_data("No Kotlin companion name resolver"))?;
        let name = resolve(names, companion_name)?;
        if let Some(companion) = cx.class_nodes[node]
            .nested
            .iter()
            .find(|&&nested| cx.class_nodes[nested].simple_name.as_ref() == Some(&name))
            .map(|&nested| Arc::clone(&cx.class_nodes[nested].class))
        {
            parse_metadata_for(cx, &companion);
            let Some(ClassElement::Class(companion_data)) = state(cx).class(&companion).cloned()
            else {
                return Err(invalid_data(format!(
                    "Companion object of {} is not a class",
                    class.qualified_name
                )));
            };
            let proto = &companion_data.proto;
            if let Some(names) = &companion_data.names {
                bind::functions(
                    cx,
                    &companion,
                    &proto.function,
                    names,
                    proto.type_table.as_ref(),
                    false,
                    Some(&class),
                )?;
                bind::properties(cx, &companion, &proto.property, names, Some(&class))?;
            }
            mark_instance(cx, node, &class, &companion, Hidden::CompanionInstance)?;
        }
    }

    if flags::CLASS_KIND.get(data.proto.flags()) == Some(Kind::Object) {
        mark_instance(cx, node, &class, &class, Hidden::ObjectInstance)?;
    }
    Ok(())
}

fn mark_instance(
    cx: &mut Cx,
    node: ClassNodeId,
    class: &StructClass,
    singleton: &StructClass,
    reason: Hidden,
) -> io::Result<()> {
    let wrapper = cx.class_nodes[node].wrapper.as_ref().ok_or_else(|| {
        invalid_data(format!(
            "Class {} has no Kotlin initializer wrapper",
            class.qualified_name
        ))
    })?;
    let target = format!("L{};", singleton.qualified_name);
    let field = state_fields(cx, class)
        .find(|field| {
            field.descriptor == target
                && wrapper
                    .static_field_initializers
                    .get_with_key(make_unique_key(&field.name, &field.descriptor).as_str())
                    .is_some_and(|&expr| matches!(cx.ir[expr].kind, ExprKind::New { .. }))
        })
        .cloned();
    if let Some(field) = field {
        state(cx).fields.get_mut(&field).element = Some(FieldElement::Hidden(reason));
    }
    Ok(())
}

fn state_fields<'a>(
    cx: &'a Cx,
    class: &'a StructClass,
) -> impl Iterator<Item = &'a Arc<crate::structs::StructField>> + 'a {
    cx.kotlin_members
        .as_ref()
        .into_iter()
        .flat_map(|members| members.fields(class))
}
