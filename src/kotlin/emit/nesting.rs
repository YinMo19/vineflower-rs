// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::{classfile::ClassFile, context::NestedKind};

use super::{Bytecode, ClassDeclaration, ClassGroup, ClassKind, Declaration, KotlinError, STATIC, error};
use crate::kotlin::read_metadata;

pub(super) struct Child<'a, 'data> {
    pub class: &'a ClassFile<'data>,
    pub declaration: ClassDeclaration,
}

/// Match metadata names to actual static member class files. A JVM `$` alone
/// does not establish Kotlin nesting, and a missing child must not turn a
/// source declaration into an empty or incomplete class.
pub(super) fn children<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    declaration: &ClassDeclaration,
    group: Option<&'a ClassGroup<'data>>,
) -> Result<Vec<Child<'a, 'data>>, KotlinError> {
    let invalid = || error(bytecode.owner, "Kotlin nested class does not match the class group");
    let companion = declaration.companion_name.as_deref();
    let names = &declaration.nested_names;
    let declared = names.iter().map(String::as_str).chain(
        companion.filter(|name| !names.iter().any(|nested| nested.as_str() == *name)),
    );
    let mut children = Vec::new();
    for simple in declared {
        if simple.is_empty() || simple.contains(['/', '.', '$']) {
            return Err(invalid());
        }
        let group = group.ok_or_else(invalid)?;
        let jvm_name = format!("{}${simple}", bytecode.owner);
        let class = group.get(&jvm_name).ok_or_else(invalid)?;
        let member = group.member_class(&jvm_name).ok_or_else(invalid)?;
        if !group.is_attached(&jvm_name) || member.outer != bytecode.owner || member.simple_name != simple
            || member.access_flags & STATIC == 0
        {
            return Err(invalid());
        }
        let metadata = read_metadata(class)?.ok_or_else(invalid)?;
        let Declaration::Class(child) = metadata.declaration else { return Err(invalid()); };
        let id = &child.name.id;
        if child.name.local || id.rsplit_once('.') != Some((declaration.name.id.as_str(), simple))
            || child.flags.has(9) || (child.kind == ClassKind::CompanionObject) != (companion == Some(simple))
            || children.iter().any(|sibling: &Child<'_, '_>| sibling.declaration.name.id == *id)
        {
            return Err(invalid());
        }
        children.push(Child { class, declaration: child });
    }
    if let Some(group) = group {
        for (actual, member) in group.children(bytecode.owner) {
            let NestedKind::Member(simple) = &member.kind else { continue; };
            if !names.contains(simple) && companion != Some(simple.as_str()) {
                return Err(error(actual, "JVM member class has no Kotlin nested declaration"));
            }
        }
    }
    Ok(children)
}
