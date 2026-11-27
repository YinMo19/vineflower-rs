//! `struct.gen.generics.GenericType`: the type arguments, enclosing type and
//! wildcard of a [`VarType`], the parser of generic signatures, and the
//! assignability rules between parameterized types.
//!
//! Upstream reports a malformed signature by letting a string operation
//! throw and catching that where the attribute is read. Here the parser is
//! fallible instead: `try_` functions give `None` exactly where upstream
//! would throw, and [`VarType::parse`] is for signatures known to be valid.

use std::sync::Arc;

use arcstr::ArcStr;

use super::var_type::{CodeType, VarType};
use crate::decompiler::expr_processor;
use crate::engine::{Cx, import_collector};
use crate::util::jhash::{JHashMap, JHashSet};

/// `Map<VarType, VarType>`: type variables and what replaces them. A
/// variable can be mapped to `null`, an unbounded wildcard.
pub type GenericsMap = JHashMap<VarType, Option<VarType>>;

/// `Map<VarType, List<VarType>>`: the type variables in scope with their bounds.
pub type NamedGenerics = JHashMap<VarType, Vec<VarType>>;

/// What a `GenericType` object adds to a `VarType`.
#[derive(Debug)]
pub struct GenericType {
    parent: Option<VarType>,
    /// `None` is an unbounded wildcard.
    arguments: Vec<Option<VarType>>,
    wildcard: i32,
}

impl GenericType {
    pub const WILDCARD_EXTENDS: i32 = 1;
    pub const WILDCARD_SUPER: i32 = 2;
    pub const WILDCARD_UNBOUND: i32 = 3;
    pub const WILDCARD_NO: i32 = 4;

    /// `GenericType.DUMMY_VAR`: a type variable without a name.
    pub fn dummy_var() -> VarType {
        VarType::generic(
            CodeType::Genvar,
            0,
            Some(ArcStr::new()),
            None,
            Vec::new(),
            Self::WILDCARD_NO,
        )
    }

    pub(super) fn same(&self, other: &GenericType) -> bool {
        self.wildcard == other.wildcard
            && match (&self.parent, &other.parent) {
                (None, None) => true,
                (Some(a), Some(b)) => a.same(b),
                _ => false,
            }
            && self.arguments.len() == other.arguments.len()
            && self
                .arguments
                .iter()
                .zip(&other.arguments)
                .all(|pair| match pair {
                    (None, None) => true,
                    (Some(a), Some(b)) => a.same(b),
                    _ => false,
                })
    }
}

use GenericType as G;

impl VarType {
    /// `new GenericType(type, arrayDim, value, parent, arguments, wildcard)`.
    pub fn generic(
        ty: CodeType,
        array_dim: i32,
        value: Option<ArcStr>,
        parent: Option<VarType>,
        arguments: Vec<Option<VarType>>,
        wildcard: i32,
    ) -> VarType {
        let mut var_type = VarType::raw(ty, array_dim, value);
        var_type.generic = Some(Arc::new(GenericType {
            parent,
            arguments,
            wildcard,
        }));
        var_type
    }

    /// `GenericType.parse(signature)`, for a signature known to be well formed.
    pub fn parse(signature: &str) -> VarType {
        Self::parse_wildcard(signature, G::WILDCARD_NO)
    }

    /// `GenericType.parse(signature, wildcard)`.
    pub fn parse_wildcard(signature: &str, wildcard: i32) -> VarType {
        Self::try_parse(signature, wildcard)
            .unwrap_or_else(|| panic!("Invalid signature: {signature}"))
    }

    pub(super) fn try_parse(signature: &str, wildcard: i32) -> Option<VarType> {
        let mut ty = CodeType::Byte; // TODO: should be null!
        let mut array_dim = 0;
        let mut value: Option<ArcStr> = None;
        let mut params: Option<Vec<Option<VarType>>> = None;
        let mut parent: Option<VarType> = None;

        for (index, c) in signature.char_indices() {
            match c {
                '[' => array_dim += 1,
                'T' => {
                    ty = CodeType::Genvar;
                    value = Some(signature.get(index + 1..signature.len() - 1)?.into());
                    break;
                }
                'L' => {
                    ty = CodeType::Object;
                    let mut signature = signature.get(index + 1..signature.len() - 1)?;
                    let mut cl = get_next_class_signature(signature);

                    if cl.len() == signature.len() {
                        let (name, args) = split_arguments(cl)?;
                        value = Some(name.into());
                        params = match args {
                            Some(args) => Some(parse_arguments_list(args)?),
                            None => None,
                        };
                    } else {
                        let mut name_buff = String::new();
                        while !signature.is_empty() {
                            let (name, args) = split_arguments(cl)?;
                            if !name_buff.is_empty() {
                                name_buff.push('$');
                            }
                            name_buff.push_str(name);

                            value = Some(name_buff.as_str().into());
                            params = match args {
                                Some(args) => Some(parse_arguments_list(args)?),
                                None => None,
                            };

                            if cl.len() == signature.len() {
                                break;
                            }
                            parent = Some(if parent.is_none() && params.is_none() {
                                Self::try_parse(&format!("L{name_buff};"), G::WILDCARD_NO)?
                            } else {
                                Self::generic(
                                    CodeType::Object,
                                    0,
                                    value.clone(),
                                    parent,
                                    params.clone().unwrap_or_default(),
                                    wildcard,
                                )
                            });
                            signature = signature.get(cl.len() + 1..)?;
                            cl = get_next_class_signature(signature);
                        }
                    }
                    break;
                }
                _ => {
                    ty = Self::try_get_type(c)?;
                    value = Some(c.encode_utf8(&mut [0; 4]).into());
                }
            }
        }

        Some(match ty {
            CodeType::Genvar => Self::generic(ty, array_dim, value, None, Vec::new(), wildcard),
            CodeType::Object
                if parent.is_some() || params.is_some() || wildcard != G::WILDCARD_NO =>
            {
                Self::generic(
                    ty,
                    array_dim,
                    value,
                    parent,
                    params.unwrap_or_default(),
                    wildcard,
                )
            }
            _ => Self::raw(ty, array_dim, value),
        })
    }

    /// `GenericType.getNextType(value)`: the first type of a sequence of
    /// signatures, for a sequence known to be well formed.
    pub fn get_next_type(value: &str) -> &str {
        Self::try_get_next_type(value).unwrap_or_else(|| panic!("Invalid signature: {value}"))
    }

    pub(super) fn try_get_next_type(value: &str) -> Option<&str> {
        let mut counter = 0;
        let mut cont_mode = false;

        for (index, c) in value.char_indices() {
            let ends = match c {
                '*' => !cont_mode,
                'L' | 'T' => {
                    cont_mode = true;
                    false
                }
                '[' | '+' | '-' => false,
                '<' => {
                    counter += 1;
                    false
                }
                '>' => {
                    counter -= 1;
                    false
                }
                ';' => counter == 0,
                _ => !cont_mode,
            };
            if ends {
                return Some(&value[..index + c.len_utf8()]);
            }
        }

        None
    }

    pub fn with_wildcard(var: &VarType, wildcard: i32) -> VarType {
        let (parent, arguments) = if var.is_generic() {
            (var.parent().cloned(), var.arguments().to_vec())
        } else {
            (None, Vec::new())
        };
        Self::generic(
            var.ty,
            var.array_dim,
            var.value.clone(),
            parent,
            arguments,
            wildcard,
        )
    }

    /// `this instanceof GenericType`.
    pub fn is_generic_type(&self) -> bool {
        self.generic.is_some()
    }

    pub fn is_generic(&self) -> bool {
        self.generic.as_ref().is_some_and(|generic| {
            self.ty == CodeType::Genvar
                || !generic.arguments.is_empty()
                || generic.parent.is_some()
                || generic.wildcard != G::WILDCARD_NO
        })
    }

    /// `getParent()`: the enclosing type of an inner class type.
    pub fn parent(&self) -> Option<&VarType> {
        self.generic.as_ref()?.parent.as_ref()
    }

    /// `getArguments()`; a plain type has none.
    pub fn arguments(&self) -> &[Option<VarType>] {
        self.generic
            .as_ref()
            .map_or(&[], |generic| &generic.arguments)
    }

    /// `getWildcard()`; a plain type has `WILDCARD_NO`.
    pub fn wildcard(&self) -> i32 {
        self.generic
            .as_ref()
            .map_or(G::WILDCARD_NO, |generic| generic.wildcard)
    }

    pub fn get_cast_name(&self, cx: &mut Cx) -> String {
        let value = self.name();
        let cls_name = match self.parent() {
            None => import_collector::get_short_name(cx, &value.replace('/', ".")),
            Some(parent) if parent.is_generic() => {
                let inner = &value[parent.name().len() + 1..];
                format!("{}.{inner}", parent.get_cast_name(cx))
            }
            Some(parent) => {
                let outer = import_collector::get_short_name(cx, &parent.name().replace('/', "."));
                let inner = &value[value.rfind('.').map_or(0, |dot| dot + 1)..];
                format!("{outer}.{inner}")
            }
        };
        cls_name + &self.get_type_arguments(cx)
    }

    fn get_type_arguments(&self, cx: &mut Cx) -> String {
        let arguments = self.arguments();
        if arguments.is_empty() {
            return String::new();
        }

        let mut buffer = String::from("<");
        for (i, par) in arguments.iter().enumerate() {
            if i > 0 {
                buffer.push_str(", ");
            }

            match par {
                // Wildcard unbound
                None => buffer.push('?'),
                Some(gen_type) if gen_type.is_generic() => {
                    match gen_type.wildcard() {
                        G::WILDCARD_EXTENDS => buffer.push_str("? extends "),
                        G::WILDCARD_SUPER => buffer.push_str("? super "),
                        _ => {}
                    }
                    buffer.push_str(&super::generic_main::get_generic_cast_type_name(
                        cx, gen_type,
                    ));
                }
                Some(par) => buffer.push_str(&expr_processor::get_cast_type_name(cx, par)),
            }
        }
        buffer.push('>');
        buffer
    }

    /// `toString()` as dispatched on the Java object: a `GenericType` adds
    /// its wildcard and type arguments to the descriptor form.
    pub fn to_generic_string(&self, cx: &mut Cx) -> String {
        if !self.is_generic_type() {
            return self.to_string();
        }
        let wildcard = match self.wildcard() {
            G::WILDCARD_EXTENDS => "? extends ",
            G::WILDCARD_SUPER => "? super ",
            _ => "",
        };
        format!("{wildcard}{self}{}", self.get_type_arguments(cx))
    }

    /// The type with the variables of `map` replaced. The result is the same
    /// type (see [`VarType::same`]) when nothing in it is mapped, and `None`
    /// when it is mapped to `null`.
    pub fn remap(&self, map: &GenericsMap) -> Option<VarType> {
        match self.remap_changed(map, Self::same) {
            Some(changed) => changed,
            None => Some(self.clone()),
        }
    }

    /// Inference checks whether remapping returned the original Java object.
    /// For example, method `T` replaced by the enclosing class's `T` can
    /// retain the same spelling and give a qualifier more type information.
    pub(crate) fn remap_for_inference(&self, map: &GenericsMap) -> Option<VarType> {
        match self.remap_changed(map, Self::same_generic_reference) {
            Some(changed) => changed,
            None => Some(self.clone()),
        }
    }

    pub(crate) fn same_generic_reference(&self, other: &VarType) -> bool {
        match (&self.generic, &other.generic) {
            (Some(left), Some(right)) => self == other && Arc::ptr_eq(left, right),
            _ => self.same(other),
        }
    }

    /// `None` where upstream's `remap` returns `this`.
    fn remap_changed(
        &self,
        map: &GenericsMap,
        same_type: fn(&VarType, &VarType) -> bool,
    ) -> Option<Option<VarType>> {
        let main = self.base_remap_changed(map, same_type);
        if !self.is_generic_type() {
            return main;
        }

        if let Some(mut main) = main {
            if let Some(mapped) = &main {
                let wild = mapped.wildcard();
                if self.wildcard() != G::WILDCARD_NO && wild != self.wildcard() {
                    main = Some(Self::with_wildcard(mapped, self.wildcard()));
                }
            }
            return Some(main);
        }

        let mut changed = false;
        let mut parent = self.parent().cloned();
        if let Some(mapped) = parent.as_ref().and_then(|parent| map.get(parent)) {
            parent = mapped.clone();
            changed = true;
        }

        let new_args: Vec<Option<VarType>> = self
            .arguments()
            .iter()
            .map(|arg| {
                let arg = arg.as_ref()?;
                match arg.remap_changed(map, same_type) {
                    Some(new_arg) => {
                        changed = true;
                        new_arg
                    }
                    None => Some(arg.clone()),
                }
            })
            .collect();

        changed.then(|| {
            Some(Self::generic(
                self.ty,
                self.array_dim,
                self.value.clone(),
                parent,
                new_args,
                self.wildcard(),
            ))
        })
    }

    /// `VarType.remap`: looks up the type itself, without its array dimensions.
    fn base_remap_changed(
        &self,
        map: &GenericsMap,
        same_type: fn(&VarType, &VarType) -> bool,
    ) -> Option<Option<VarType>> {
        let ret = if self.array_dim == 0 {
            map.get(self)?
        } else {
            map.get(&self.resize_array_dim(0))?
        };
        let ret = match ret {
            Some(ret) if self.array_dim != 0 => {
                Some(ret.resize_array_dim(ret.array_dim + self.array_dim))
            }
            ret => ret.clone(),
        };
        // A type mapped to itself is the unchanged type.
        if ret.as_ref().is_some_and(|ret| same_type(ret, self)) {
            return None;
        }
        Some(ret)
    }

    pub fn equals_exact(&self, other: &VarType) -> bool {
        let Some(generic) = &self.generic else {
            return self == other;
        };
        if !other.is_generic_type() {
            return generic.parent.is_none()
                && generic.arguments.is_empty()
                && generic.wildcard == G::WILDCARD_NO
                && other == self;
        }
        self == other && generic.wildcard == other.wildcard() && self.arguments_equal(other)
    }

    // returns true if there's any genvars abound with empty names
    // TODO: this is a hack! check why genvars with empty names are made!
    pub fn is_type_unfinished(&self) -> bool {
        self.get_all_generic_vars()
            .iter()
            .any(|var| var.name().is_empty())
    }

    pub fn arguments_equal(&self, other: &VarType) -> bool {
        let (arguments, other_arguments) = (self.arguments(), other.arguments());
        arguments.len() == other_arguments.len()
            && arguments
                .iter()
                .zip(other_arguments)
                .all(|pair| match pair {
                    (None, None) => true,
                    (Some(t), Some(o)) => {
                        t.is_generic() == o.is_generic()
                            && t == o
                            && (!t.is_generic() || t.equals_exact(o))
                    }
                    _ => false,
                })
    }

    pub fn is_assignable(cx: &Cx, from: &VarType, to: &VarType, named: &NamedGenerics) -> bool {
        if from.array_dim != to.array_dim {
            return false;
        }

        if from.ty == CodeType::Object && from.ty == to.ty {
            if !cx.classes().instance_of(from.name(), to.name()) {
                return false;
            }
        } else if from != to {
            if from.ty == CodeType::Genvar && from.ty != to.ty && named.contains_key(from) {
                return named.get(from).unwrap().iter().any(|bound| {
                    let bound = super_type_if_generic(cx, bound, to);
                    Self::are_arguments_assignable(cx, &bound, to, named)
                });
            }
            return false;
        }

        let from = super_type_if_generic(cx, from, to);
        Self::are_arguments_assignable(cx, &from, to, named)
    }

    pub fn are_arguments_assignable(
        cx: &Cx,
        from: &VarType,
        to: &VarType,
        named: &NamedGenerics,
    ) -> bool {
        if !(from.is_generic() && to.is_generic()) {
            return true;
        }

        let (from_arguments, to_arguments) = (from.arguments(), to.arguments());
        if from_arguments.len() != to_arguments.len() {
            return from_arguments.is_empty() || to_arguments.is_empty();
        }

        for (i, (f, t)) in from_arguments.iter().zip(to_arguments).enumerate() {
            let Some(t) = t else {
                continue;
            };
            let t_wild = t.wildcard();

            let f = match f {
                None => {
                    let cls = cx.classes().get_class(from.name()).unwrap();
                    let bounds = cls.signature().unwrap().fbounds[i][0].clone();
                    if bounds == VarType::VARTYPE_OBJECT {
                        return false;
                    }
                    bounds
                }
                Some(f) if f.ty == CodeType::Genvar && f.ty != t.ty && named.contains_key(f) => {
                    named.get(f).unwrap()[0].clone()
                }
                Some(f) => f.clone(),
            };
            let f_wild = f.wildcard();

            if t_wild == G::WILDCARD_EXTENDS {
                if f_wild == G::WILDCARD_SUPER || !cx.classes().instance_of(f.name(), t.name())
                {
                    return false;
                }
            } else if t_wild == G::WILDCARD_SUPER {
                if f_wild == G::WILDCARD_EXTENDS
                    || !cx.classes().instance_of(t.name(), f.name())
                {
                    return false;
                }
            } else if (t_wild == G::WILDCARD_NO
                && f_wild != t_wild
                && from.wildcard() == to.wildcard())
                || Some(f.name()) != t.value.as_deref()
            {
                return false;
            }

            if !Self::are_arguments_assignable(cx, &f, t, named) {
                return false;
            }
        }

        true
    }

    pub fn get_all_generic_vars(&self) -> Vec<VarType> {
        if self.ty == CodeType::Genvar {
            return vec![self.resize_array_dim(0)];
        }

        self.arguments()
            .iter()
            .flatten()
            .filter(|arg| arg.is_generic())
            .flat_map(VarType::get_all_generic_vars)
            .collect()
    }

    // In certain cases, we after we map generic variables we *don't* want to lower known generics
    // to wildcards. This removes mappings where, for example, Type<T> is being mapped to Type<?>.
    // This can't be done generally as there are cases where we *do* want to map to a wildcard-
    // such as fields.
    pub fn clean_lowered_generic_types(
        temp_map: &mut GenericsMap,
        type1: &VarType,
        type2: &VarType,
        can_clean: Option<&JHashSet<VarType>>,
    ) {
        let (arguments1, arguments2) = (type1.arguments(), type2.arguments());
        if arguments1.len() != arguments2.len() {
            return;
        }
        for (arg1, arg2) in arguments1.iter().zip(arguments2) {
            // Don't lower the current type from a generic to a wildcard
            if let (Some(arg1), None) = (arg1, arg2)
                && can_clean.is_none_or(|can_clean| can_clean.contains(arg1))
            {
                temp_map.remove(arg1);
            }
        }
    }

    // In the case where Type is defined as "class Type<T>", and the in type is "Type<?>", find the
    // base (un-remapped) type "Type<T>" out of it. Essentially a wrapper to do a class lookup to
    // find the generic class type descriptor.
    // Returns null if there is a failure at any point.
    pub fn find_base_type(&self, cx: &Cx) -> Option<VarType> {
        let cl = cx.classes().get_class(self.name())?;
        Some(cl.signature()?.generic_type.clone())
    }

    pub fn map_gen_vars_to(&self, cx: &Cx, other: &VarType, map: &mut GenericsMap) {
        let (arguments, other_arguments) = (self.arguments(), other.arguments());
        if arguments.len() != other_arguments.len() {
            return;
        }

        let dummy_var = G::dummy_var();
        for (this_arg, other_arg) in arguments.iter().zip(other_arguments) {
            let Some(this_arg) = this_arg else {
                continue;
            };
            if other_arg.as_ref() == Some(&dummy_var) {
                continue;
            }

            if this_arg.ty == CodeType::Genvar {
                let mut this_arg = this_arg.clone();
                let mut other_arg = other_arg.clone();
                let t_wild = this_arg.wildcard();
                let o_wild = other_arg.as_ref().map_or(G::WILDCARD_NO, VarType::wildcard);

                if t_wild == o_wild && t_wild != G::WILDCARD_NO {
                    this_arg = Self::with_wildcard(&this_arg, G::WILDCARD_NO);
                    other_arg = other_arg.map(|arg| Self::with_wildcard(&arg, G::WILDCARD_NO));
                }

                match other_arg {
                    None => {
                        if this_arg.array_dim == 0 && !map.contains_key(&this_arg) {
                            map.insert(this_arg, None);
                        }
                    }
                    Some(mut other_arg) if this_arg.array_dim <= other_arg.array_dim => {
                        if this_arg.array_dim > 0 {
                            other_arg = other_arg
                                .resize_array_dim(other_arg.array_dim - this_arg.array_dim);
                            this_arg = this_arg.resize_array_dim(0);
                        }

                        match map.get(&this_arg) {
                            None => {
                                map.insert(this_arg, Some(other_arg));
                            }
                            Some(curr) => {
                                let c_wild =
                                    curr.as_ref().map_or(G::WILDCARD_NO, VarType::wildcard);
                                if o_wild != c_wild {
                                    let lowered = Self::with_wildcard(&other_arg, G::WILDCARD_NO);
                                    map.insert(this_arg, Some(lowered));
                                }
                            }
                        }
                    }
                    Some(_) => {}
                }
            } else if this_arg.is_generic()
                && let Some(other_arg) = other_arg
                && other_arg.is_generic()
            {
                this_arg.map_gen_vars_to(cx, other_arg, map);
            }
        }

        if let Some(other_parent) = other.parent()
            && other_parent.is_generic()
        {
            let parent = match self.parent() {
                Some(parent) if parent.is_generic() => Some(parent.clone()),
                _ => cx
                    .classes()
                    .get_class(other_parent.name())
                    .map(|cls| cls.signature().unwrap().generic_type.clone()),
            };
            if let Some(parent) = parent {
                parent.map_gen_vars_to(cx, other_parent, map);
            }
        }
    }

    pub fn has_unknown_generic_type(&self, named_generics: &JHashSet<VarType>) -> bool {
        if self.ty == CodeType::Genvar {
            return !named_generics.contains(&self.resize_array_dim(0));
        }

        self.arguments()
            .iter()
            .flatten()
            .any(|arg| arg.is_generic() && arg.has_unknown_generic_type(named_generics))
    }

    /// `derived_type` seen as `super_type`'s class, with that class's type
    /// parameters replaced by what the derived type supplies for them; the
    /// derived type itself if the two classes are unrelated or unknown.
    pub fn get_generic_super_type(
        cx: &Cx,
        derived_type: &VarType,
        super_type: &VarType,
    ) -> VarType {
        let class_of = |ty: &VarType| cx.classes().get_class(ty.value.as_deref()?);
        let (Some(dcls), Some(scls)) = (class_of(derived_type), class_of(super_type)) else {
            return derived_type.clone();
        };

        let hierarchy = dcls.get_all_generics(cx);
        let (Some(super_generics), Some(super_signature)) =
            (hierarchy.get(&scls.qualified_name), scls.signature())
        else {
            return derived_type.clone();
        };

        let mut temp_map = GenericsMap::new();
        if derived_type.is_generic()
            && let Some(signature) = dcls.signature()
        {
            signature
                .generic_type
                .map_gen_vars_to(cx, derived_type, &mut temp_map);
            Self::clean_lowered_generic_types(
                &mut temp_map,
                &signature.generic_type,
                derived_type,
                None,
            );
            // Given MyClass<T extends MyClass<T>> implements MyInterface<T>
            // converting MyClass<?> to MyInterface should produce MyInterface<MyClass<?>> not MyInterface<?>
            for (fparameter, bounds) in signature.fparameters.iter().zip(&signature.fbounds) {
                let param = Self::parse(&format!("T{fparameter};"));
                if matches!(temp_map.get(&param), None | Some(None))
                    && let Some(bound) = bounds.first()
                {
                    let replacement = bound.remap(&temp_map);
                    if replacement != Some(VarType::VARTYPE_OBJECT) {
                        temp_map.insert(param, replacement);
                    }
                }
            }
        }

        super_signature
            .generic_type
            .remap(super_generics)
            .unwrap()
            .remap(&temp_map)
            .unwrap()
    }
}

/// `from` converted to the class of the generic type `to`, when that gives a
/// generic type; `from` itself otherwise.
fn super_type_if_generic(cx: &Cx, from: &VarType, to: &VarType) -> VarType {
    if to.is_generic() && Some(from.name()) != to.value.as_deref() {
        let super_type = VarType::get_generic_super_type(cx, from, to);
        if super_type.is_generic() {
            return super_type;
        }
    }
    from.clone()
}

/// For generic types `t` and `other`, should we check the base type to
/// determine if `t <: other`? E.g. `List<Type> <: Collection<Type>`.
pub(super) fn should_check_generic_base(t: &VarType, other: &VarType) -> bool {
    if t.arguments_equal(other) {
        return t.wildcard() == other.wildcard();
    }

    // Arguments not equal. Check them, one by one.
    let (arguments, other_arguments) = (t.arguments(), other.arguments());
    arguments.len() == other_arguments.len()
        && arguments.iter().zip(other_arguments).any(|pair| {
            // List<? extends Type> <: Collection<Type>
            // List<? super Type> <: Collection<Type>
            matches!(pair, (Some(a1), Some(a2))
                if a1.wildcard() != G::WILDCARD_NO
                    && Some(a1.name()) == a2.value.as_deref()
                    && !a2.is_generic())
        })
}

/// The first class of a possibly nested class signature such as
/// `Outer<TT;>.Inner`.
fn get_next_class_signature(value: &str) -> &str {
    let mut counter = 0;
    for (index, c) in value.char_indices() {
        match c {
            '<' => counter += 1,
            '>' => counter -= 1,
            '.' if counter == 0 => return &value[..index],
            _ => {}
        }
    }
    value
}

/// A class name and, if it has any, the text between its angle brackets.
fn split_arguments(cl: &str) -> Option<(&str, Option<&str>)> {
    Some(match cl.find('<') {
        Some(arg_start) => (&cl[..arg_start], Some(cl.get(arg_start + 1..cl.len() - 1)?)),
        None => (cl, None),
    })
}

fn parse_arguments_list(mut value: &str) -> Option<Vec<Option<VarType>>> {
    let mut args = Vec::new();

    while !value.is_empty() {
        let type_str = VarType::try_get_next_type(value)?;
        let (wildcard, bound) = match type_str.as_bytes()[0] {
            b'*' => (G::WILDCARD_UNBOUND, &type_str[1..]),
            b'+' => (G::WILDCARD_EXTENDS, &type_str[1..]),
            b'-' => (G::WILDCARD_SUPER, &type_str[1..]),
            _ => (G::WILDCARD_NO, type_str),
        };

        args.push(if bound.is_empty() {
            None
        } else {
            Some(VarType::try_parse(bound, wildcard)?)
        });

        value = &value[type_str.len()..];
    }

    Some(args)
}
