use std::borrow::Cow;
use std::collections::HashSet;

use crate::classfile::{ClassError, ClassFile};
use crate::{ClassGroup, Options};

pub(crate) fn is_assignable(
    group: Option<&ClassGroup<'_>>,
    options: &Options,
    from: &str,
    to: &str,
) -> bool {
    if from == to || to == "java/lang/Object" {
        return true;
    }
    let classpaths = [
        options.library_classpath.as_deref(),
        options.runtime_classpath.as_deref(),
    ];
    if classpaths.iter().all(Option::is_none) {
        return group.is_some_and(|group| group.is_assignable(from, to));
    }
    let mut pending = vec![Cow::Borrowed(from)];
    let mut visited = HashSet::new();
    while let Some(name) = pending.pop() {
        if name == to {
            return true;
        }
        if visited.contains(&name) {
            continue;
        }
        if let Some(class) = group.and_then(|group| group.get(&name)) {
            pending.extend(
                std::iter::once(class.super_class)
                    .chain(class.interfaces.iter().copied())
                    .filter(|&index| index != 0)
                    .filter_map(|index| class.pool.class_name(index).ok())
                    .map(Cow::Borrowed),
            );
        } else {
            for classpath in classpaths.into_iter().flatten() {
                // An unreadable library type is unknown, not proof of an inheritance edge.
                // Callers must keep explicit conversions unless a path is proved here.
                if let Ok(Some(metadata)) = classpath.metadata(&name) {
                    pending.extend(
                        metadata
                            .super_name
                            .iter()
                            .chain(&metadata.interfaces)
                            .cloned()
                            .map(Cow::Owned),
                    );
                    break;
                }
            }
        }
        visited.insert(name);
    }
    false
}

pub(crate) fn is_permitted_subclass(
    group: &ClassGroup<'_>,
    options: &Options,
    class: &ClassFile<'_>,
    name: &str,
) -> Result<bool, ClassError> {
    let version = class.major_version;
    if version < 61 && !(version >= 59 && class.minor_version == u16::MAX) {
        return Ok(false);
    }
    for parent in std::iter::once(class.super_class).chain(class.interfaces.iter().copied()) {
        if parent == 0 {
            continue;
        }
        let parent = class.pool.class_name(parent)?;
        if parent == "java/lang/Object" {
            continue;
        }
        if let Some(parent) = group.get(parent) {
            for child in parent.permitted_subclasses()? {
                if parent.pool.class_name(child)? == name {
                    return Ok(true);
                }
            }
        } else {
            for path in [
                options.library_classpath.as_deref(),
                options.runtime_classpath.as_deref(),
            ]
            .into_iter()
            .flatten()
            {
                if let Ok(Some(parent)) = path.metadata(parent) {
                    if parent
                        .permitted_subclasses
                        .iter()
                        .any(|child| child == name)
                    {
                        return Ok(true);
                    }
                    break;
                }
            }
        }
    }
    Ok(false)
}

pub(crate) fn overrides(
    group: &ClassGroup<'_>,
    options: &Options,
    class: &ClassFile<'_>,
    child: &str,
    method: &str,
    descriptor: &str,
) -> Result<bool, ClassError> {
    const METHOD_VISIBILITY_AND_STATIC: u16 = 0x0001 | 0x0002 | 0x0004 | 0x0008;
    let paths = [
        options.library_classpath.as_deref(),
        options.runtime_classpath.as_deref(),
    ];
    let have_classpath = paths.iter().any(Option::is_some);
    let child_package = child.rsplit_once('/').map_or("", |(package, _)| package);
    let inherits = |parent: &str, flags: u16| match flags & METHOD_VISIBILITY_AND_STATIC {
        0x0001 | 0x0004 => true,
        0 => parent.rsplit_once('/').map_or("", |(package, _)| package) == child_package,
        _ => false,
    };
    fn parents<'c>(ty: &'c ClassFile<'_>) -> impl Iterator<Item = u16> + 'c {
        std::iter::once(ty.super_class)
            .chain(ty.interfaces.iter().copied())
            .filter(|&index| index != 0)
    }
    let mut pending = Vec::new();
    for index in parents(class) {
        let name = class.pool.class_name(index)?;
        if have_classpath || group.get(name).is_some() {
            pending.push(Cow::Borrowed(name));
        }
    }
    let mut visited = HashSet::new();
    while let Some(parent) = pending.pop() {
        if parent == child || visited.contains(&parent) {
            continue;
        }
        if let Some(class) = group.get(&parent) {
            let pool = &class.pool;
            for member in &class.methods {
                if inherits(&parent, member.access_flags)
                    && pool.utf8(member.name_index)? == method
                    && pool.utf8(member.descriptor_index)? == descriptor
                {
                    return Ok(true);
                }
            }
            for index in parents(class) {
                pending.push(Cow::Borrowed(pool.class_name(index)?));
            }
        } else {
            for path in paths.into_iter().flatten() {
                if let Ok(Some(class)) = path.metadata(&parent) {
                    if class.methods.iter().any(|member| {
                        inherits(&parent, member.access_flags)
                            && member.name == method
                            && member.descriptor == descriptor
                    }) {
                        return Ok(true);
                    }
                    pending.extend(
                        class
                            .super_name
                            .iter()
                            .chain(&class.interfaces)
                            .cloned()
                            .map(Cow::Owned),
                    );
                    break;
                }
            }
        }
        visited.insert(parent);
    }
    Ok(false)
}
