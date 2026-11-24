// Based on Vineflower ImportCollector (Apache-2.0).
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
    fmt::Write,
};

use crate::{
    Options,
    context::{ClassGroup, NestedKind},
    descriptor::Type,
    naming::MemberRenames,
};

pub(super) struct Names<'a, 'c> {
    owner: &'c str,
    package: &'c str,
    imports: RefCell<BTreeSet<String>>,
    bindings: RefCell<HashMap<String, String>>,
    group: &'c ClassGroup<'a>,
    renames: &'c MemberRenames,
    qualify: bool,
    include_inner: bool,
}

impl<'a, 'c> Names<'a, 'c> {
    pub(super) fn new(
        group: &'c ClassGroup<'a>,
        name: &'c str,
        options: &Options,
        renames: &'c MemberRenames,
    ) -> Self {
        let effective = renames.class_name(name);
        let package = effective
            .rsplit_once('/')
            .map_or("", |(package, _)| package);
        let mut bindings = HashMap::new();
        bindings.insert(simple(effective).into(), effective.into());
        Self {
            owner: name,
            package,
            imports: RefCell::new(BTreeSet::new()),
            bindings: RefCell::new(bindings),
            group,
            renames,
            qualify: options.remove_imports,
            include_inner: options.decompile_inner,
        }
    }

    pub(super) fn renames(&self) -> &'c MemberRenames {
        self.renames
    }

    pub(super) fn render(&self, name: &str) -> String {
        if name == self.owner {
            return simple(self.renames.class_name(name)).into();
        }
        if name.starts_with('[')
            && let Ok(ty) = Type::parse(name)
        {
            return ty.render(|name| self.render(name));
        }
        if self.group.is_attached(name)
            && let Some(class) = self.group.nested_class(name)
            && let NestedKind::Local(simple) = &class.kind
        {
            return self
                .renames
                .simple_class_alias(name)
                .unwrap_or(simple)
                .into();
        }
        let mut base = name;
        let mut chain = Vec::new();
        while let Some(member) = self.group.member_class(base) {
            if !self.include_inner
                && self
                    .group
                    .nested_class(base)
                    .is_some_and(|class| matches!(class.kind, NestedKind::Anonymous))
            {
                break;
            }
            chain.push(
                self.renames
                    .simple_class_alias(base)
                    .unwrap_or(member.simple_name),
            );
            base = member.outer;
            if base == self.owner {
                break;
            }
            if self.group.is_attached(base)
                && let Some(class) = self.group.nested_class(base)
                && let NestedKind::Local(simple) = &class.kind
            {
                let mut result = self
                    .renames
                    .simple_class_alias(base)
                    .unwrap_or(simple)
                    .to_owned();
                append_members(&mut result, chain);
                return result;
            }
        }

        let base = self.renames.class_name(base);
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
        append_members(&mut result, chain);
        result
    }

    pub(super) fn imports(&self, output: &mut String) {
        for import in self.imports.borrow().iter() {
            let _ = writeln!(output, "import {import};");
        }
    }
}

fn append_members(result: &mut String, chain: Vec<&str>) {
    for member in chain.into_iter().rev() {
        result.push('.');
        result.push_str(member);
    }
}

pub(super) fn simple(name: &str) -> &str {
    name.rsplit('/').next().unwrap_or(name)
}
