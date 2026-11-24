use std::{borrow::Cow, collections::HashSet, sync::Arc};

use crate::{
    classfile::ClassFile,
    classpath::ClassMetadata,
    descriptor::{GenericType, MethodDescriptor, MethodSignature, Type},
};

use super::{
    Machine,
    expr::{Category, Expr, Source},
};

const OBJECT: &str = "java/lang/Object";
const STRING: &str = "java/lang/String";
const EQUALS: &str = "(Ljava/lang/Object;)Z";
const PRIVATE: u16 = 0x0002;
const STATIC: u16 = 0x0008;
const FINAL: u16 = 0x0010;
const BRIDGE: u16 = 0x0040;
const VARARGS: u16 = 0x0080;
const INTERFACE: u16 = 0x0200;
const SYNTHETIC: u16 = 0x1000;
const ENUM: u16 = 0x4000;

enum DeclarationClass<'a, 'c> {
    Input(&'c ClassFile<'a>),
    Library(Arc<ClassMetadata>),
}

enum ImplicitArgument<'a> {
    Typed(Cow<'a, Type>),
    Null,
}

struct Invocation<'a> {
    name: &'a str,
    source_name: &'a str,
    descriptor: &'a str,
    parameters: &'a [Type],
    arguments: &'a [Expr],
    is_static: bool,
    found: bool,
}

impl<'a, 'c> Machine<'a, 'c> {
    pub(super) fn can_pass_argument_implicitly(&self, value: &Expr, formal: &Type) -> bool {
        self.implicit_argument_type(value, formal).is_some()
    }

    fn implicit_argument_type<'v>(
        &self,
        value: &'v Expr,
        formal: &Type,
    ) -> Option<ImplicitArgument<'v>> {
        if matches!(value.source, Source::Null) {
            return (Category::of(formal) == Some(Category::Ref)).then_some(ImplicitArgument::Null);
        }
        if let Source::WidenedPrimitive { operand_type, .. } = value.source
            && value.ty == *formal
        {
            let source = Type::Primitive(operand_type);
            return strict_conversion(self, &source, formal)
                .then_some(ImplicitArgument::Typed(Cow::Owned(source)));
        }
        if value.ty == *formal {
            return None;
        }
        let allowed = match (&value.ty, formal) {
            (Type::Primitive(_), Type::Primitive(_)) => {
                // A displayed literal need not have the type inferred for its
                // JVM slot (e.g. a small integer is not a byte in source).
                matches!(value.source, Source::Local(_))
                    && strict_conversion(self, &value.ty, formal)
            }
            _ => Category::of(&value.ty) == Some(Category::Ref)
                && Category::of(formal) == Some(Category::Ref)
                && !matches!(value.source, Source::New(_))
                && !self.local_argument_needs_erasure(value)
                && self.known_assignable(&value.ty, formal),
        };
        allowed.then_some(ImplicitArgument::Typed(Cow::Borrowed(&value.ty)))
    }

    /// Prove that the same fixed-arity JVM descriptor wins after omitting the
    /// source casts. `lookup_owner` is the rendered qualifier's
    /// static type, which can be more specific than the constant-pool owner.
    /// Other arguments must still be rendered at their descriptor types.
    pub(super) fn omit_invocation_casts(
        &self,
        lookup_owner: &str,
        (owner, name, descriptor): (&str, &str, &str),
        method: &MethodDescriptor,
        arguments: &[Expr],
        opcode: u8,
    ) -> bool {
        let constructor = name == "<init>";
        if lookup_owner.starts_with('[')
            || arguments.len() != method.parameters.len()
            || constructor && self.group.is_some_and(|group| group.is_attached(owner))
            || !arguments
                .iter()
                .zip(&method.parameters)
                .any(|(actual, formal)| self.can_pass_argument_implicitly(actual, formal))
        {
            return false;
        }
        let source_name = self.source_invocation_name(owner, name, descriptor);
        let platform_string_equals = owner == STRING
            && lookup_owner == STRING
            && opcode == 0xb6
            && name == "equals"
            && source_name == name
            && descriptor == EQUALS;
        let platform_value_of = owner == STRING
            && lookup_owner == STRING
            && opcode == 0xb8
            && name == "valueOf"
            && source_name == name
            && descriptor == "(Ljava/lang/Object;)Ljava/lang/String;"
            && matches!(arguments, [argument] if matches!(argument.ty, Type::Object(_))
                && !matches!(argument.source, Source::Null));
        let mut call = Invocation {
            name,
            source_name: &source_name,
            descriptor,
            parameters: &method.parameters,
            arguments,
            is_static: opcode == 0xb8,
            found: false,
        };
        let mut pending = vec![Cow::Borrowed(lookup_owner)];
        let mut visited = HashSet::new();
        while let Some(declaring) = pending.pop() {
            if visited.contains(&declaring) {
                continue;
            }
            let inherited = declaring != lookup_owner;
            let class = match self.overload_class(&declaring) {
                Ok(Some(class)) => class,
                Ok(None)
                    if declaring == OBJECT
                        && (!object_api_contains(&source_name) || platform_string_equals) =>
                {
                    continue;
                }
                // These Java SE String signatures are stable. A named object
                // cannot match valueOf(char[]) or a primitive overload in
                // the strict phase while valueOf(Object) is applicable.
                Ok(None)
                    if declaring == STRING && (platform_string_equals || platform_value_of) =>
                {
                    call.found = true;
                    pending.push(Cow::Borrowed(OBJECT));
                    continue;
                }
                _ => return false,
            };
            let flags = match &class {
                DeclarationClass::Input(class) => class.access_flags,
                DeclarationClass::Library(class) => class.access_flags,
            };
            if constructor && flags & ENUM != 0 {
                return false;
            }
            let inherited_excluded = if inherited {
                PRIVATE | if flags & INTERFACE != 0 { STATIC } else { 0 }
            } else {
                0
            };
            match class {
                DeclarationClass::Input(class) => {
                    let pool = &class.pool;
                    for method in &class.methods {
                        if method.access_flags & inherited_excluded != 0 {
                            continue;
                        }
                        let (Ok(name), Ok(descriptor)) = (
                            pool.utf8(method.name_index),
                            pool.utf8(method.descriptor_index),
                        ) else {
                            return false;
                        };
                        if !call.accepts(
                            self,
                            &declaring,
                            name,
                            descriptor,
                            method.access_flags,
                            || method.signature(pool).ok(),
                        ) {
                            return false;
                        }
                    }
                    if !constructor {
                        for index in class
                            .interfaces
                            .iter()
                            .copied()
                            .chain((class.super_class != 0).then_some(class.super_class))
                        {
                            let Ok(parent) = pool.class_name(index) else {
                                return false;
                            };
                            pending.push(Cow::Borrowed(parent));
                        }
                    }
                }
                DeclarationClass::Library(class) => {
                    for method in &class.methods {
                        if method.access_flags & inherited_excluded == 0
                            && !call.accepts(
                                self,
                                &declaring,
                                &method.name,
                                &method.descriptor,
                                method.access_flags,
                                || Some(method.signature.as_deref()),
                            )
                        {
                            return false;
                        }
                    }
                    if !constructor {
                        pending.extend(
                            class
                                .interfaces
                                .iter()
                                .chain(&class.super_name)
                                .cloned()
                                .map(Cow::Owned),
                        );
                    }
                }
            }
            visited.insert(declaring);
        }
        call.found
    }

    fn overload_class(
        &self,
        name: &str,
    ) -> Result<Option<DeclarationClass<'a, 'c>>, crate::classpath::ClassPathError> {
        if let Some(class) = (name == self.owner)
            .then_some(self.class)
            .or_else(|| self.group.and_then(|group| group.get(name)))
        {
            return Ok(Some(DeclarationClass::Input(class)));
        }
        for classpath in [
            self.options.library_classpath.as_deref(),
            self.options.runtime_classpath.as_deref(),
        ]
        .into_iter()
        .flatten()
        {
            if let Some(class) = classpath.metadata(name)? {
                return Ok(Some(DeclarationClass::Library(class)));
            }
        }
        Ok(None)
    }

    fn overload_final_class(&self, name: &str) -> bool {
        match self.overload_class(name) {
            Ok(Some(DeclarationClass::Input(class))) => class.access_flags & FINAL != 0,
            Ok(Some(DeclarationClass::Library(class))) => class.access_flags & FINAL != 0,
            Ok(None) => name == STRING,
            Err(_) => false,
        }
    }
}

impl Invocation<'_> {
    fn accepts<'s>(
        &mut self,
        machine: &Machine<'_, '_>,
        owner: &str,
        name: &str,
        descriptor: &str,
        flags: u16,
        signature: impl FnOnce() -> Option<Option<&'s str>>,
    ) -> bool {
        // Match the actual emitted name, including aliases and lambda helpers.
        if machine.source_invocation_name(owner, name, descriptor) != self.source_name {
            return true;
        }
        let selected = name == self.name
            && descriptor == self.descriptor
            && (flags & STATIC != 0) == self.is_static;
        if selected {
            if flags & (VARARGS | BRIDGE | SYNTHETIC) != 0
                || !signature().is_some_and(|signature| erased_formals(signature, self.parameters))
            {
                return false;
            }
            self.found = true;
            return true;
        }
        let Ok(candidate) = MethodDescriptor::parse(descriptor) else {
            return false;
        };
        if candidate.parameters.len() != self.parameters.len() {
            // With the selected declaration applicable in the strict phase,
            // variable-arity expansion (JLS 15.12.2.4) cannot beat it.
            return true;
        }
        if !signature().is_some_and(|signature| erased_formals(signature, &candidate.parameters)) {
            // Type inference or specialization can change applicability and
            // specificity; don't use erasure to rule out a generic overload.
            return false;
        }
        let mut less_specific = false;
        for ((actual, formal), competing) in self
            .arguments
            .iter()
            .zip(self.parameters)
            .zip(&candidate.parameters)
        {
            let applicable = match machine.implicit_argument_type(actual, formal) {
                Some(ImplicitArgument::Null) => Category::of(competing) == Some(Category::Ref),
                Some(ImplicitArgument::Typed(actual)) => {
                    potential_strict_conversion(machine, &actual, competing)
                }
                None => potential_strict_conversion(machine, formal, competing),
            };
            if !applicable {
                return true;
            }
            if formal != competing {
                less_specific = true;
            }
        }
        less_specific
            && self
                .parameters
                .iter()
                .zip(&candidate.parameters)
                .all(|(formal, competing)| strict_conversion(machine, formal, competing))
    }
}

fn erased_formals(signature: Option<&str>, descriptor: &[Type]) -> bool {
    let Some(signature) = signature else {
        return true;
    };
    MethodSignature::parse(signature).is_ok_and(|signature| {
        signature.type_parameters.is_empty()
            && signature.parameters.len() == descriptor.len()
            && signature
                .parameters
                .iter()
                .zip(descriptor)
                .all(|(source, erased)| reifiable_formal(source, erased))
    })
}

fn reifiable_formal(source: &GenericType, mut erased: &Type) -> bool {
    let source = if let GenericType::Array {
        element,
        dimensions,
    } = source
    {
        for _ in 0..*dimensions {
            let Type::Array(component) = erased else {
                return false;
            };
            erased = component;
        }
        element.as_ref()
    } else {
        source
    };
    match (source, erased) {
        (GenericType::Primitive(source), Type::Primitive(erased)) => source == erased,
        (GenericType::Class(source), Type::Object(erased)) => {
            source.internal_name == *erased
                && source.arguments.is_empty()
                && source.nested.is_empty()
        }
        _ => false,
    }
}

fn strict_conversion(machine: &Machine<'_, '_>, source: &Type, target: &Type) -> bool {
    match (source, target) {
        (Type::Primitive(source), Type::Primitive(target)) => source.widens_to(*target),
        _ => machine.known_assignable(source, target),
    }
}

fn potential_strict_conversion(machine: &Machine<'_, '_>, source: &Type, target: &Type) -> bool {
    match (source, target) {
        (Type::Primitive(_), Type::Primitive(_)) => strict_conversion(machine, source, target),
        // Strict invocation (JLS 15.12.2.2) does not box or unbox.
        (Type::Primitive(_), _) | (_, Type::Primitive(_)) => false,
        (Type::Array(source), Type::Array(target)) => match (source.as_ref(), target.as_ref()) {
            (Type::Primitive(_), _) | (_, Type::Primitive(_)) => source == target,
            _ => potential_strict_conversion(machine, source, target),
        },
        // Two distinct final classes cannot have a common subtype, including
        // through generic/poly expressions. A missing inheritance edge alone
        // would not be enough to assert inapplicability.
        (Type::Object(source), Type::Object(target)) if source != target => {
            !machine.overload_final_class(source) || !machine.overload_final_class(target)
        }
        _ => true,
    }
}

fn object_api_contains(name: &str) -> bool {
    // The Java SE Object API is the root of a source hierarchy. Missing root
    // metadata cannot introduce a competing *differently named* method.
    matches!(
        name,
        "clone"
            | "equals"
            | "finalize"
            | "getClass"
            | "hashCode"
            | "notify"
            | "notifyAll"
            | "toString"
            | "wait"
    )
}

#[cfg(test)]
mod tests;
