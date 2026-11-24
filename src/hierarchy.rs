use std::borrow::Cow;
use std::collections::HashSet;

use crate::{ClassGroup, Options};
use crate::classfile::{ClassError, ClassFile};

pub(crate) fn is_assignable(group: Option<&ClassGroup<'_>>, options: &Options, from: &str, to: &str) -> bool {
    if from == to || to == "java/lang/Object" {
        return true;
    }
    let classpaths = [options.library_classpath.as_deref(), options.runtime_classpath.as_deref()];
    if classpaths.iter().all(Option::is_none) {
        return group.is_some_and(|group| group.is_assignable(from, to));
    }
    let mut pending = vec![Cow::Borrowed(from)];
    let mut visited = HashSet::new();
    while let Some(name) = pending.pop() {
        if name == to { return true; }
        if visited.contains(&name) { continue; }
        if let Some(class) = group.and_then(|group| group.get(&name)) {
            pending.extend(std::iter::once(class.super_class).chain(class.interfaces.iter().copied())
                .filter(|&index| index != 0).filter_map(|index| class.pool.class_name(index).ok()).map(Cow::Borrowed));
        } else {
            for classpath in classpaths.into_iter().flatten() {
                // An unreadable library type is unknown, not proof of an inheritance edge.
                // Callers must keep explicit conversions unless a path is proved here.
                if let Ok(Some(metadata)) = classpath.metadata(&name) {
                    pending.extend(metadata.super_name.iter().chain(&metadata.interfaces).cloned().map(Cow::Owned));
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
            for path in [options.library_classpath.as_deref(), options.runtime_classpath.as_deref()].into_iter().flatten() {
                if let Ok(Some(parent)) = path.metadata(parent) {
                    if parent.permitted_subclasses.iter().any(|child| child == name) {
                        return Ok(true);
                    }
                    break;
                }
            }
        }
    }
    Ok(false)
}
