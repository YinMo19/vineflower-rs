// Based on Vineflower invocation generic binding (Apache-2.0).
use std::{borrow::Cow, sync::OnceLock};

use crate::descriptor::{GenericType, MethodSignature, Type};

use super::{
    Machine,
    expr::{Category, Expr, Source},
};

pub(super) struct GenericCall(Cow<'static, MethodSignature>);

impl GenericCall {
    pub(super) fn argument_fits(
        &self,
        index: usize,
        actual: &Expr,
        erased: &Type,
        machine: &Machine<'_, '_>,
    ) -> bool {
        let mut formal = self.0.parameters.get(index);
        if let Some(GenericType::Array { element, .. }) = formal {
            formal = Some(element);
        }
        matches!(formal, Some(GenericType::Variable(name))
            if self.0.type_parameters.iter().any(|parameter| parameter.name == *name))
            && Category::of(&actual.ty) == Some(Category::Ref)
            && !matches!(actual.source, Source::Null)
            && machine.known_assignable(&actual.ty, erased)
    }

    pub(super) fn return_type(&self, args: &[Expr]) -> Option<Type> {
        let GenericType::Variable(variable) = &self.0.return_type else {
            return None;
        };
        if !self
            .0
            .type_parameters
            .iter()
            .any(|parameter| parameter.name == *variable)
        {
            return None;
        }
        let mut candidates =
            self.0
                .parameters
                .iter()
                .zip(args)
                .filter_map(|(parameter, argument)| {
                    matches!(parameter, GenericType::Variable(name) if name == variable)
                        .then_some(argument)
                });
        let first = candidates.next()?;
        if Category::of(&first.ty) != Some(Category::Ref) || matches!(first.source, Source::Null) {
            return None;
        }
        candidates
            .all(|arg| arg.ty == first.ty && !matches!(arg.source, Source::Null))
            .then(|| first.ty.clone())
    }
}

impl Machine<'_, '_> {
    pub(super) fn generic_call(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
        is_static: bool,
    ) -> Option<GenericCall> {
        // Conservative until invocation overload resolution covers class and
        // interface inheritance. Restrict this inference to unique static
        // methods of a concrete class whose only superclass is Object.
        if !self.options.decompile_generics
            || !is_static
            || owner.starts_with('[')
            || name.starts_with('<')
        {
            return None;
        }
        let class = self
            .group
            .and_then(|group| group.get(owner))
            .or_else(|| (owner == self.owner).then_some(self.class));
        if let Some(class) = class {
            if class.super_class == 0
                || class.pool.class_name(class.super_class).ok()? != "java/lang/Object"
                || !class.interfaces.is_empty()
            {
                return None;
            }
            let pool = &class.pool;
            let mut methods = class.methods.iter().filter(|method| {
                pool.utf8(method.name_index)
                    .is_ok_and(|candidate| candidate == name)
            });
            let method = methods.next()?;
            if methods.next().is_some()
                || method.access_flags & 0x0008 == 0
                || pool.utf8(method.descriptor_index).ok()? != descriptor
            {
                return None;
            }
            let signature = method.signature(pool).ok()??;
            return MethodSignature::parse(signature).ok().map(|sig| GenericCall(Cow::Owned(sig)));
        }
        for path in [
            self.options.library_classpath.as_deref(),
            self.options.runtime_classpath.as_deref(),
        ]
        .into_iter()
        .flatten()
        {
            let Ok(Some(class)) = path.metadata(owner) else {
                continue;
            };
            if class.super_name.as_deref() != Some("java/lang/Object")
                || !class.interfaces.is_empty()
            {
                return None;
            }
            let mut methods = class.methods.iter().filter(|method| method.name == name);
            let method = methods.next()?;
            if methods.next().is_some()
                || method.access_flags & 0x0008 == 0
                || method.descriptor != descriptor
            {
                return None;
            }
            let signature = method.signature.as_deref()?;
            return MethodSignature::parse(signature).ok().map(|sig| GenericCall(Cow::Owned(sig)));
        }
        // The Java SE API has one asList declaration. A cast to the erased
        // Object[] prevents inference from a String[] even in fixed arity.
        if (owner, name, descriptor) == ("java/util/Arrays", "asList", "([Ljava/lang/Object;)Ljava/util/List;") {
            static SIGNATURE: OnceLock<MethodSignature> = OnceLock::new();
            let signature = SIGNATURE.get_or_init(|| {
                MethodSignature::parse("<T:Ljava/lang/Object;>([TT;)Ljava/util/List<TT;>;")
                    .expect("Java SE Arrays.asList signature")
            });
            return Some(GenericCall(Cow::Borrowed(signature)));
        }
        None
    }
}
