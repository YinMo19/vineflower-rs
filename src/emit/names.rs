// Based on Vineflower ImportCollector (Apache-2.0).
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
    fmt::Write,
};

use crate::{
    classfile::{ClassError, ClassFile},
    descriptor::Type,
};

pub(super) struct Names<'a> {
    owner: &'a str,
    package: &'a str,
    imports: RefCell<BTreeSet<String>>,
    bindings: RefCell<HashMap<String, String>>,
    members: HashMap<&'a str, (&'a str, &'a str)>,
    qualify: bool,
}

impl<'a> Names<'a> {
    pub(super) fn new(
        class: &'a ClassFile<'_>,
        name: &'a str,
        qualify: bool,
    ) -> Result<Self, ClassError> {
        let package = name.rsplit_once('/').map_or("", |(package, _)| package);
        let members = class
            .inner_classes()?
            .into_iter()
            .filter(|inner| {
                inner.outer_class != 0 && inner.inner_name != 0 && inner.inner_class != 0
            })
            .map(|inner| {
                Ok((
                    class.pool.class_name(inner.inner_class)?,
                    (
                        class.pool.class_name(inner.outer_class)?,
                        class.pool.utf8(inner.inner_name)?,
                    ),
                ))
            })
            .collect::<Result<_, ClassError>>()?;
        let mut bindings = HashMap::new();
        bindings.insert(simple(name).into(), name.into());
        Ok(Self {
            owner: name,
            package,
            imports: RefCell::new(BTreeSet::new()),
            bindings: RefCell::new(bindings),
            members,
            qualify,
        })
    }

    pub(super) fn render(&self, name: &str) -> String {
        if name == self.owner {
            return simple(name).into();
        }
        if name.starts_with('[')
            && let Ok(ty) = Type::parse(name)
        {
            return ty.render(|name| self.render(name));
        }
        let mut base = name;
        let mut chain = Vec::new();
        while let Some(&(outer, inner)) = self.members.get(base) {
            // InnerClasses is not required to form a valid ownership tree.
            if chain.len() == self.members.len() || outer == base {
                return name.replace('/', ".");
            }
            chain.push(inner);
            base = outer;
        }

        let (package, leaf) = base.rsplit_once('/').unwrap_or(("", base));
        let mut bindings = self.bindings.borrow_mut();
        let same_package = package == self.package || package.is_empty();
        let can_shorten = (!self.qualify || same_package || package == "java/lang")
            && bindings.get(leaf).is_none_or(|bound| bound == base);
        let mut result = if can_shorten {
            if !bindings.contains_key(leaf) {
                bindings.insert(leaf.into(), base.into());
                if !same_package && package != "java/lang" {
                    self.imports.borrow_mut().insert(base.replace('/', "."));
                }
            }
            leaf.into()
        } else {
            base.replace('/', ".")
        };
        for member in chain.into_iter().rev() {
            result.push('.');
            result.push_str(member);
        }
        result
    }

    pub(super) fn imports(&self, output: &mut String) {
        for import in self.imports.borrow().iter() {
            let _ = writeln!(output, "import {import};");
        }
    }
}

pub(super) fn simple(name: &str) -> &str {
    name.rsplit('/').next().unwrap_or(name)
}
