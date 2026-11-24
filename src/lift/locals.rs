// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{
    cell::RefCell,
    collections::{HashMap, hash_map::Entry},
    fmt::Write,
    rc::Rc,
};

use crate::{
    bytecode::Instruction,
    classfile::{ClassFile, Code, Constant, LocalTypeRange, LocalVariable, Member},
    descriptor::{
        ClassSignature, FieldSignature, GenericType, MethodDescriptor, MethodSignature, Type,
        TypeArgument, TypeParameter,
    },
    naming::{VariableNamer, VariableRenamer, is_valid_local_identifier},
    options::Options,
    source_text::Document,
};

use super::{
    CodeTypeSite, Effect, LiftError, Machine,
    assignment_expr::LocalWrite,
    expr::{AnonymousOrigin, Category, Expr, INT, IntFits, Order, Source},
};

#[path = "instanceof_locals.rs"]
mod instanceof_locals;
pub(crate) use instanceof_locals::IfPatternLocal;

#[path = "joins.rs"]
mod joins;
#[path = "lambda_locals.rs"]
mod lambda_locals;
#[path = "local_tokens.rs"]
mod local_tokens;

use local_tokens::LocalTokenIndices;

#[derive(Clone, Debug)]
struct Local {
    name: String,
    ty: Type,
    /// An initialized `var` binds one exact, otherwise unnameable type.
    anonymous_site: Option<AnonymousOrigin>,
    generic: Option<Rc<LocalSignature>>,
    debug_range: Option<(u16, u16)>,
    receiver: bool,
    token_index: Option<u32>,
    int_fits: IntFits,
}

impl PartialEq for Local {
    fn eq(&self, other: &Self) -> bool {
        // Optional token metadata does not decide whether a binding can be
        // represented by the same declaration at a control-flow join.
        self.name == other.name
            && self.ty == other.ty
            && self.anonymous_site == other.anonymous_site
            && self.generic == other.generic
            && self.debug_range == other.debug_range
            && self.receiver == other.receiver
    }
}

impl Eq for Local {}

#[derive(Clone, Default)]
pub(crate) struct Names {
    used: HashMap<String, NameUse>,
    suffix: u32,
    version: u16,
    namer: Option<VariableNamer>,
    token_indices: Option<LocalTokenIndices>,
}

#[derive(Clone, Copy)]
enum NameUse {
    Reserved,
    Local,
}

#[derive(Clone)]
pub(crate) struct LexicalNames {
    names: Rc<RefCell<Names>>,
    parent: Option<Rc<Self>>,
}

impl LexicalNames {
    pub(crate) fn binds(&self, name: &str) -> bool {
        matches!(self.names.borrow().used.get(name), Some(NameUse::Local))
            || self.parent.as_deref().is_some_and(|parent| parent.binds(name))
    }
}

impl Names {
    fn fresh(&mut self, name: &str) -> String {
        self.fresh_owned(name.into())
    }

    fn fresh_owned(&mut self, mut name: String) -> String {
        if !self.used.contains_key(&name) {
            self.used.insert(name.clone(), NameUse::Local);
            return name;
        }
        if self.namer.is_some() {
            while self.used.contains_key(&name) {
                name.push('x');
            }
            self.used.insert(name.clone(), NameUse::Local);
            return name;
        }
        loop {
            self.suffix += 1;
            let candidate = format!("{name}_{}", self.suffix);
            if let Entry::Vacant(entry) = self.used.entry(candidate) {
                return entry.insert_entry(NameUse::Local).key().clone();
            }
        }
    }

    fn binding(
        &mut self,
        parameter: bool,
        index: u16,
        ty: &Type,
        debug_names: [Option<&str>; 2],
        cast_name: impl FnOnce() -> Option<String>,
        fallback: impl FnOnce() -> String,
    ) -> String {
        let proposed = self.namer.as_mut().and_then(|namer| {
            if parameter {
                if !namer.renames_parameters() {
                    return None;
                }
                namer.rename_parameter(index, ty, cast_name().as_deref())
            } else {
                namer.rename_local(ty, cast_name().as_deref())
            }
        });
        let name = proposed
            .filter(|name| is_valid_local_identifier(name, self.version))
            .or_else(|| {
                debug_names
                    .into_iter()
                    .flatten()
                    .find(|name| is_valid_local_identifier(name, self.version))
                    .map(str::to_owned)
            })
            .unwrap_or_else(fallback);
        self.fresh_owned(name)
    }
}

type LocalKey<'a> = (u16, u16, u16, &'a str);
type GenericSignatures<'a> = HashMap<LocalKey<'a>, Rc<LocalSignature>>;

#[derive(Debug, Eq, PartialEq)]
struct LocalSignature {
    erased: Type,
    ty: GenericType,
    intersection: bool,
}

fn local_key<'a>(entry: &LocalVariable<'a>) -> LocalKey<'a> {
    (entry.index, entry.start_pc, entry.length, entry.name)
}

#[derive(Clone)]
pub(super) struct Locals<'a> {
    slots: Vec<Option<Local>>,
    debug: Rc<[LocalVariable<'a>]>,
    generic: Option<Rc<GenericSignatures<'a>>>,
    decompile_generics: bool,
    use_debug_names: bool,
    names: Rc<RefCell<Names>>,
    lambda_enclosing: Option<Rc<LexicalNames>>,
    parameter_names: Rc<[String]>,
    tokens: Option<local_tokens::LocalTokens<'a>>,
    track_int_fits: bool,
}

impl<'a> Locals<'a> {
    pub(super) fn new<'input>(
        class: &'a ClassFile<'input>,
        method: &Member<'input>,
        code: &Code<'input>,
        descriptor: &MethodDescriptor,
        options: &Options,
        owner: &str,
    ) -> Result<Self, LiftError> {
        let namer = VariableRenamer::select(
            options.variable_renaming.as_deref(),
            options.jad_style_variable_naming,
        )
        .map(|renamer| {
            renamer.for_method(
                options.rename_parameters,
                options.jad_style_parameter_naming,
                class.major_version,
            )
        });
        let custom_names = namer.is_some();
        let mut names = Names {
            version: class.major_version,
            namer,
            ..Names::default()
        };
        for constant in class.pool.iter() {
            if let Constant::Class(index) = constant {
                let name = class.pool.utf8(*index)?;
                let name = if name.starts_with('[') {
                    name.trim_start_matches('[')
                        .trim_start_matches('L')
                        .trim_end_matches(';')
                } else {
                    name
                };
                let leaf = name.rsplit('/').next().unwrap_or(name);
                names.used.insert(
                    leaf.split('$').next().unwrap_or(leaf).into(),
                    NameUse::Reserved,
                );
                if let Some((package, _)) = name.split_once('/') {
                    names.used.insert(package.into(), NameUse::Reserved);
                }
            }
        }
        for field in &class.fields {
            if custom_names || field.access_flags & 0x0018 == 0x0018 {
                names
                    .used
                    .insert(class.pool.utf8(field.name_index)?.into(), NameUse::Reserved);
            }
        }
        let debug = code.local_variables(&class.pool)?;
        let (generic, signature) = (options.decompile_generics || custom_names)
            .then(|| local_signatures(class, method, code, descriptor, &debug))
            .flatten()
            .map_or((None, None), |(locals, signature)| (Some(Rc::new(locals)), signature));
        let mut result = Self {
            slots: vec![None; usize::from(code.max_locals)],
            debug: debug.into(),
            decompile_generics: options.decompile_generics,
            generic,
            use_debug_names: options.use_debug_names,
            names: Rc::new(RefCell::new(names)),
            lambda_enclosing: None,
            parameter_names: Rc::default(),
            tokens: None,
            track_int_fits: false,
        };
        let mut index = 0;
        if method.access_flags & 0x0008 == 0 {
            if result.slots.is_empty() {
                return Err(LiftError::InvalidLocal {
                    offset: 0,
                    index: 0,
                    reason: "receiver exceeds max_locals",
                });
            }
            result.slots[0] = Some(Local {
                name: "this".into(),
                ty: Type::Object(owner.into()),
                generic: None,
                anonymous_site: None,
                debug_range: None,
                receiver: true,
                token_index: None,
                int_fits: IntFits::default(),
            });
            index = 1;
        }
        let parameters = if options.use_method_parameters {
            method.method_parameters(&class.pool)?
        } else {
            Vec::new()
        };
        let mut parameter_names = Vec::with_capacity(descriptor.parameters.len());
        for (ordinal, ty) in descriptor.parameters.iter().enumerate() {
            if usize::from(index) + usize::from(ty.slots()) > result.slots.len() {
                return Err(LiftError::InvalidLocal {
                    offset: 0,
                    index,
                    reason: "parameter exceeds max_locals",
                });
            }
            let debug = result.debug_at(index, 0);
            let marked_name = match parameters.get(ordinal) {
                Some(parameter)
                    if parameters.len() == descriptor.parameters.len()
                        && parameter.name_index != 0 =>
                {
                    Some(class.pool.utf8(parameter.name_index)?)
                }
                _ => None,
            };
            let name = result.names.borrow_mut().binding(
                true,
                index,
                ty,
                [marked_name, result.debug_name(debug)],
                || result.generic_cast(ty, debug),
                || format!("var{index}"),
            );
            let debug_range = debug.map(|entry| (entry.start_pc, entry.length));
            parameter_names.push(name.clone());
            result.slots[usize::from(index)] = Some(Local {
                name,
                ty: ty.clone(),
                generic: result.declaration_signature(ty, debug).filter(|generic| {
                    signature.as_ref().and_then(|sig| sig.parameters.get(ordinal))
                        == Some(&generic.ty)
                }),
                anonymous_site: None,
                debug_range,
                receiver: false,
                token_index: None,
                int_fits: IntFits::default(),
            });
            index += ty.slots();
        }
        result.parameter_names = parameter_names.into();
        if options.dump_text_tokens {
            result.tokens = Some(local_tokens::LocalTokens::new(
                class.pool.utf8(method.descriptor_index)?,
                index,
            ));
            result.names.borrow_mut().token_indices = Some(LocalTokenIndices::new(&result.slots));
        }
        Ok(result)
    }

    pub(super) fn parameters(&self) -> &[String] {
        &self.parameter_names
    }

    pub(super) fn lexical_names(&self) -> LexicalNames {
        LexicalNames {
            names: Rc::clone(&self.names),
            parent: self.lambda_enclosing.clone(),
        }
    }

    pub(super) fn reserve_capture_name(&self, name: &str) {
        let mut names = self.names.borrow_mut();
        if !names.used.contains_key(name) {
            names.used.insert(name.into(), NameUse::Reserved);
        }
    }

    pub(super) fn reserve_unshadowed_field(&self, name: &str, in_lambda: bool) -> bool {
        // A debug variable can begin at the store following this load, and a
        // control-flow join may hoist its declaration. Check the whole table
        // rather than only the scope at the instruction being lifted.
        if self.use_debug_names && self.debug.iter().any(|entry| entry.name == name)
            || self.slots.iter().flatten().any(|local| local.name == name)
        {
            return false;
        }
        let mut names = self.names.borrow_mut();
        match names.used.get(name) {
            Some(NameUse::Local) => false,
            Some(NameUse::Reserved) => true,
            // An inline lambda uses a copy of its enclosing name registry.
            // It cannot reserve a new identifier against future outer locals.
            None if in_lambda => false,
            None => {
                names.used.insert(name.to_owned(), NameUse::Reserved);
                true
            }
        }
    }

    pub(super) fn same_as(&self, other: &Self) -> bool {
        self.slots == other.slots
    }

    pub(super) fn keeps(&self, baseline: &Self) -> bool {
        self.slots.len() == baseline.slots.len()
            && baseline
                .slots
                .iter()
                .zip(&self.slots)
                .all(|(before, after)| before.is_none() || before == after)
    }

    pub(super) fn discard_branch_only(&mut self, baseline: &Self) -> bool {
        if !self.keeps(baseline) {
            return false;
        }
        self.slots.clone_from(&baseline.slots);
        true
    }

    pub(super) fn temporary(&self, offset: u32) -> String {
        self.names
            .borrow_mut()
            .fresh_owned(format!("stack{offset}"))
    }

    fn debug_at(&self, index: u16, offset: u32) -> Option<&LocalVariable<'a>> {
        self.debug
            .iter()
            .filter(|entry| {
                let start = u32::from(entry.start_pc);
                entry.index == index && start <= offset && offset < start + u32::from(entry.length)
            })
            .max_by_key(|entry| entry.start_pc)
    }

    fn debug_name(&self, debug: Option<&LocalVariable<'a>>) -> Option<&'a str> {
        self.use_debug_names.then_some(debug?.name)
    }

    fn generic_signature(&self, ty: &Type, debug: Option<&LocalVariable<'a>>) -> Option<&Rc<LocalSignature>> {
        let signature = self.generic.as_ref()?.get(&local_key(debug?))?;
        (signature.erased == *ty).then_some(signature)
    }

    fn declaration_signature(&self, ty: &Type, debug: Option<&LocalVariable<'a>>) -> Option<Rc<LocalSignature>> {
        if !self.decompile_generics {
            return None;
        }
        self.generic_signature(ty, debug).cloned()
    }

    fn generic_cast(&self, ty: &Type, debug: Option<&LocalVariable<'a>>) -> Option<String> {
        Some(generic_cast_name(&self.generic_signature(ty, debug)?.ty))
    }

    fn local_name(&self, index: u16, ty: &Type, debug: Option<&LocalVariable<'a>>) -> String {
        self.names.borrow_mut().binding(
            false,
            index,
            ty,
            [self.debug_name(debug), None],
            || self.generic_cast(ty, debug),
            || format!("var{index}"),
        )
    }
}

fn local_signatures<'a, 'input>(
    class: &'a ClassFile<'input>,
    method: &Member<'input>,
    code: &Code<'input>,
    descriptor: &MethodDescriptor,
    debug: &[LocalVariable<'a>],
) -> Option<(GenericSignatures<'a>, Option<MethodSignature>)> {
    if debug.is_empty() {
        return None;
    }
    let mut exact = HashMap::new();
    for entry in code.local_variable_types(&class.pool).ok()? {
        if entry.length == 0 || entry.index >= code.max_locals
            || usize::from(entry.start_pc) + usize::from(entry.length) > code.bytes.len()
        {
            continue;
        }
        exact.entry(local_key(&entry))
            .and_modify(|prior| {
                if *prior != Some(entry.descriptor) {
                    *prior = None;
                }
            })
            .or_insert(Some(entry.descriptor));
    }
    if exact.is_empty() {
        return None;
    }
    let class_parameters = (method.access_flags & 0x0008 == 0)
        .then(|| class.signature().ok().flatten())
        .flatten()
        .and_then(|signature| ClassSignature::parse(signature).ok())
        .map_or_else(Vec::new, |signature| signature.type_parameters);
    let method_signature = method.signature(&class.pool).ok().flatten()
        .and_then(|signature| MethodSignature::parse(signature).ok())
        .filter(|signature| signature.parameters.len() == descriptor.parameters.len());
    let scope = SignatureScope {
        class: &class_parameters,
        method: method_signature.as_ref().map_or(&[], |signature| signature.type_parameters.as_slice()),
        version: class.major_version,
    };
    let signatures: GenericSignatures<'a> = debug.iter().filter_map(|entry| {
        let key = local_key(entry);
        let signature = FieldSignature::parse((*exact.get(&key)?)?).ok()?.field_type;
        let erasure = Type::parse(entry.descriptor).ok()?;
        (is_generic_type(&signature) && scope.resolves(&signature)
            && scope.matches_erasure(&signature, &erasure))
            .then(|| (key, Rc::new(LocalSignature {
                erased: erasure,
                intersection: match &signature {
                    GenericType::Variable(name) => scope.variable_erasure(name)
                        .is_some_and(|(_, intersection)| intersection),
                    _ => false,
                },
                ty: signature,
            })))
    }).collect();
    (!signatures.is_empty()).then_some((signatures, method_signature))
}

struct SignatureScope<'a> {
    class: &'a [TypeParameter],
    method: &'a [TypeParameter],
    version: u16,
}

impl SignatureScope<'_> {
    fn resolves(&self, ty: &GenericType) -> bool {
        match ty {
            GenericType::Variable(name) => self.variable_erasure(name).is_some(),
            GenericType::Array { element, .. } => self.resolves(element),
            GenericType::Class(class) => class.arguments.iter()
                .chain(class.nested.iter().flat_map(|part| &part.arguments))
                .all(|argument| match argument {
                    TypeArgument::Any => true,
                    TypeArgument::Exact(ty) | TypeArgument::Extends(ty) | TypeArgument::Super(ty) =>
                        self.resolves(ty),
                }),
            GenericType::Primitive(_) => true,
            GenericType::Void => false,
        }
    }

    fn matches_erasure(&self, generic: &GenericType, erased: &Type) -> bool {
        match generic {
            GenericType::Variable(name) => {
                matches!(erased, Type::Object(actual)
                    if self.variable_erasure(name).is_some_and(|(bound, _)| bound.as_ref() == actual.as_str()))
            }
            GenericType::Class(class) => {
                matches!(erased, Type::Object(actual) if class.binary_name().as_ref() == actual.as_str())
            }
            GenericType::Array { dimensions, element } => {
                let mut component = erased;
                for _ in 0..*dimensions {
                    let Type::Array(next) = component else { return false };
                    component = next;
                }
                self.matches_erasure(element, component)
            }
            GenericType::Primitive(kind) => matches!(erased, Type::Primitive(actual) if kind == actual),
            GenericType::Void => false,
        }
    }

    fn variable_erasure<'a>(&'a self, mut name: &'a str) -> Option<(std::borrow::Cow<'a, str>, bool)> {
        let mut methods = self.method;
        let mut intersection = false;
        for _ in 0..self.method.len() + self.class.len() {
            if !is_valid_local_identifier(name, self.version) {
                return None;
            }
            let parameter = if let Some(parameter) = methods.iter().find(|param| param.name == name) {
                parameter
            } else {
                // A class bound's variables are not shadowed by the method.
                methods = &[];
                self.class.iter().find(|param| param.name == name)?
            };
            intersection |= parameter.interface_bounds.len() > usize::from(parameter.class_bound.is_none());
            match parameter.class_bound.as_ref().or_else(|| parameter.interface_bounds.first()) {
                Some(GenericType::Class(class)) => return Some((class.binary_name(), intersection)),
                Some(GenericType::Variable(next)) => name = next,
                None => return Some(("java/lang/Object".into(), intersection)),
                _ => return None,
            }
        }
        None // cyclic formal bounds
    }
}

fn is_generic_type(ty: &GenericType) -> bool {
    match ty {
        GenericType::Variable(_) => true,
        GenericType::Array { element, .. } => is_generic_type(element),
        GenericType::Class(class) => !class.arguments.is_empty()
            || class.nested.iter().any(|part| !part.arguments.is_empty()),
        GenericType::Primitive(_) | GenericType::Void => false,
    }
}

fn is_variable_type(ty: &GenericType) -> bool {
    match ty {
        GenericType::Variable(_) => true,
        GenericType::Array { element, .. } => is_variable_type(element),
        _ => false,
    }
}

fn unbounded_generic(ty: &GenericType) -> bool {
    match ty {
        GenericType::Array { element, .. } => unbounded_generic(element),
        GenericType::Class(class) => class.nested.is_empty()
            && !class.arguments.is_empty()
            && class.arguments.iter().all(|argument| matches!(argument, TypeArgument::Any)),
        _ => false,
    }
}

// Both providers discard the type arguments before looking for the leaf name.
// Avoid rendering generic arguments that do not contribute to the name.
fn generic_cast_name(ty: &GenericType) -> String {
    let (element, array) = match ty {
        GenericType::Array { element, .. } => (element.as_ref(), true),
        _ => (ty, false),
    };
    let (name, has_arguments) = match element {
        GenericType::Class(class) => {
            let mut leaf = class.internal_name.rsplit('/').next().unwrap_or(&class.internal_name);
            let mut has_arguments = !class.arguments.is_empty();
            for nested in &class.nested {
                if has_arguments {
                    break;
                }
                leaf = &nested.name;
                has_arguments = !nested.arguments.is_empty();
            }
            (leaf, has_arguments)
        }
        GenericType::Variable(name) => (name.as_str(), false),
        GenericType::Primitive(primitive) => (primitive.java_name(), false),
        GenericType::Void | GenericType::Array { .. } => {
            unreachable!("parsed field signatures have one array node and no void")
        }
    };
    let mut name = name.to_owned();
    if array && !has_arguments {
        name.push_str("[]");
    }
    name
}

impl<'c> Machine<'_, 'c> {
    pub(crate) fn resource_local(&self, index: u16) -> Option<(String, &str)> {
        let local = self.locals.slots.get(usize::from(index))?.as_ref()?;
        let Type::Object(class) = &local.ty else {
            return None;
        };
        if local.receiver || !self.is_auto_closeable(class) {
            return None;
        }
        Some((self.declared_local_type(index, local).ok()?.to_string(), &local.name))
    }

    pub(crate) fn existing_resource_local(&self, source: u16, alias: u16) -> Option<(&str, bool)> {
        if source == alias || self.class.major_version < 53 {
            return None;
        }
        let source_binding = self.locals.slots.get(usize::from(source))?.as_ref()?;
        let alias_binding = self.locals.slots.get(usize::from(alias))?.as_ref()?;
        let Type::Object(class) = &source_binding.ty else {
            return None;
        };
        if source_binding.receiver
            || alias_binding.debug_range.is_some()
            || !self.is_auto_closeable(class)
        {
            return None;
        }
        let parameter_limit = u16::from(self.method.access_flags & 0x0008 == 0)
            + self.descriptor.parameters.iter().map(Type::slots).sum::<u16>();
        Some((&source_binding.name, source < parameter_limit))
    }

    pub(crate) fn forget_resource_local(&mut self, index: u16) {
        if let Some(local) = self.locals.slots.get_mut(usize::from(index)) {
            *local = None;
        }
    }

    pub(crate) fn bind_caught_exception(
        &mut self,
        catch_type: u16,
        store: &Instruction,
    ) -> Result<(String, Document), LiftError> {
        self.offset = store.offset;
        self.opcode = store.opcode;
        if !self.stack_is_empty() || !self.initialized_this {
            return Err(
                self.invalid_stack("catch handler must begin at an initialized stack boundary")
            );
        }
        if catch_type == 0 {
            return Err(self.unsupported("catch-all requires finally reconstruction"));
        }
        let ty = self.class_type(catch_type)?;
        if !matches!(ty, Type::Object(_)) {
            return Err(self.invalid_operand("catch type must be a class"));
        }
        let index = match store.opcode {
            0x3a => self.local_index(store)?,
            0x4b..=0x4e => u16::from(store.opcode - 0x4b),
            _ => return Err(self.unsupported("a catch handler must begin with astore")),
        };
        let slot = usize::from(index);
        let binding = self
            .locals
            .slots
            .get(slot)
            .ok_or_else(|| self.invalid_local(index, "catch slot exceeds max_locals"))?;
        if binding.is_some()
            || slot > 0
                && self.locals.slots[slot - 1]
                    .as_ref()
                    .is_some_and(|local| local.ty.slots() == 2)
        {
            return Err(self.unsupported("catch declaration overlaps an existing local"));
        }
        let end = self.debug_offset(store.offset + store.len - 1) + 1;
        let debug = self
            .locals
            .debug_at(index, end)
            .or_else(|| self.locals.debug_at(index, self.debug_offset(store.offset)));
        let range = debug.map(|entry| (entry.start_pc, entry.length));
        let name = self.locals.local_name(index, &ty, debug);
        let display_type = self.render_type(&ty);
        let local = Local {
            name,
            ty,
            generic: None,
            anonymous_site: None,
            debug_range: range,
            receiver: false,
            token_index: self.locals.new_local_token_index(index),
            int_fits: IntFits::default(),
        };
        let name = self.local_binding_document(index, &local, true);
        self.locals.slots[slot] = Some(local);
        Ok((display_type, name))
    }

    pub(crate) fn local_name_checkpoint(&self) -> Names {
        self.locals.names.borrow().clone()
    }

    pub(crate) fn restore_local_names(&self, names: Names) {
        *self.locals.names.borrow_mut() = names;
    }

    pub(crate) fn local_capture_binding(
        &self,
        index: u16,
        name: &str,
    ) -> Option<(Option<(u16, u16)>, bool)> {
        let local = self.locals.slots.get(usize::from(index))?.as_ref()?;
        if local.receiver || local.name != name {
            return None;
        }
        Some((
            local.debug_range,
            self.locals
                .parameters()
                .iter()
                .any(|parameter| parameter == name),
        ))
    }

    /// Facts from slot assignments are valid without a dataflow merge only
    /// when the method consists of one straight-line block.
    pub(crate) fn track_straight_line_ints(&mut self) {
        self.locals.track_int_fits = true;
    }

    pub(super) fn load(&mut self, op: &Instruction, index: u16, category: Category) -> Result<(), LiftError> {
        let local = self
            .locals
            .slots
            .get(usize::from(index))
            .and_then(Option::as_ref)
            .ok_or_else(|| self.invalid_local(index, "load from an unbound slot"))?;
        if Category::of(&local.ty) != Some(category) {
            return Err(
                self.invalid_local(index, "load opcode does not match the bound slot's type")
            );
        }
        if let Some(expr) = self.lexical_parameter(index) {
            return self.push(expr);
        }
        let mut expr = Expr::atom(
            local.ty.clone(),
            self.local_binding_document(index, local, false),
        );
        if local.receiver {
            expr.source = Source::This;
        } else {
            expr.source = Source::Local(index);
            expr.order = Some(Order::at(self.offset));
            expr.int_fits = local.int_fits;
        }
        self.push_leaf(op, expr)
    }

    pub(super) fn store(
        &mut self,
        op: &Instruction,
        index: u16,
        category: Category,
    ) -> Result<Effect, LiftError> {
        let value = self.pop_category(category)?;
        let target = LocalWrite { index, category };
        let (ty, debug, same) = self.resolve_local_store(op, target, &value)?;
        let slot = usize::from(index);
        let generic = if same { None } else { self.locals.declaration_signature(&ty, debug.as_ref()) };
        let signature = if same {
            self.locals.slots[slot].as_ref().and_then(|local| local.generic.as_deref())
        } else {
            generic.as_deref()
        };
        let origin = if same {
            if let Some(origin) = self.locals.slots[slot].as_ref().and_then(|local| local.anonymous_site) {
                self.require_anonymous_assignment(&ty, origin, &value)?;
            }
            None
        } else {
            self.inferred_anonymous_origin(&ty, &value)?
        };
        if origin.is_some() {
            let annotation = if let Some(entry) = debug {
                self.annotated_local_type(index, (entry.start_pc, entry.length), (&ty).into())?
                    .is_some()
            } else {
                false
            };
            if signature.is_some() || annotation {
                return Err(self.unsupported("inferred anonymous local cannot have an explicit source type"));
            }
        }
        let source = signature.and_then(|_| self.local_source_signature(&value)).map(Rc::as_ref);
        let value = self.coerce_local_assignment(value, &ty, signature, source)?;
        self.before_statement(value.order)?;
        let mut local = if same {
            self.locals.slots[slot].as_ref().expect("checked active binding").clone()
        } else {
            self.bind_local_store(index, ty, debug, generic, origin)
        };
        if self.locals.track_int_fits {
            local.int_fits = value.int_fits();
        }
        let mut text = if same {
            self.local_binding_document(index, &local, false)
        } else if origin.is_some() {
            let mut text = Document::from("var ");
            self.append_local_binding(&mut text, index, &local, true);
            text
        } else {
            self.declared_local_document(index, &local)?
        };
        self.locals.slots[slot] = Some(local);
        text.push_str(" = ");
        text.append(value.text);
        text.push(';');
        Ok(Effect::Statement(text))
    }

    pub(super) fn assignment_local_destination(
        &self,
        op: &Instruction,
        target: LocalWrite,
        value: &Expr,
    ) -> Option<bool> {
        let (ty, debug, same) = self.resolve_local_store(op, target, value).ok()?;
        // An assignment expression may need a blank declaration, for which
        // neither the anonymous binary name nor `var` is a Java type.
        if self.has_anonymous_type(&ty) {
            return None;
        }
        if same {
            if self.locals.slots[usize::from(target.index)].as_ref()?.generic.is_some() {
                return None;
            }
        } else if self.locals.declaration_signature(&ty, debug.as_ref()).is_some()
            || debug.is_some_and(|entry| {
                !matches!(self.annotated_local_type(
                    target.index, (entry.start_pc, entry.length), (&ty).into(),
                ), Ok(None))
            })
        {
            // A source assignment expression would have the refined type,
            // not the type of the JVM's duplicated value.
            return None;
        }
        // The duplicated JVM value's type also controls overload resolution
        // and numeric promotion in its enclosing Java expression.
        (ty == value.ty).then_some(!same)
    }

    pub(super) fn define_pattern_local(
        &mut self,
        store: &Instruction,
        index: u16,
        tested: &Type,
        selector: Option<&Type>,
    ) -> Result<Document, LiftError> {
        let value = Expr::atom(tested.clone(), Document::new());
        let target = LocalWrite { index, category: Category::Ref };
        let (ty, debug, same) = self.resolve_local_store(store, target, &value)?;
        let generic = self.locals.declaration_signature(&ty, debug.as_ref());
        if same || !self.preserves_pattern_binding_type(
            selector, tested, &ty, generic.as_ref().map(|signature| &signature.ty),
        ) {
            return Err(self.unsupported("pattern store does not declare a compatible fresh binding"));
        }
        let local = self.bind_local_store(index, ty, debug, generic, None);
        let declaration = self.declared_local_document(index, &local)?;
        self.locals.slots[usize::from(index)] = Some(local);
        Ok(declaration)
    }

    pub(super) fn commit_assignment_local(
        &mut self,
        op: &Instruction,
        target: LocalWrite,
        ty: &Type,
        declaration: bool,
    ) -> (Document, Option<Document>) {
        let index = target.index;
        let slot = usize::from(index);
        if !declaration {
            self.locals.slots[slot].as_mut().expect("verified local binding").int_fits = IntFits::default();
            let local = self.locals.slots[slot].as_ref().expect("verified local binding");
            return (self.local_binding_document(index, local, false), None);
        }
        let debug = self.store_debug(op, index);
        let local = self.bind_local_store(index, ty.clone(), debug, None, None);
        let mut blank = self.local_type_document(&local.ty);
        blank.push(' ');
        self.append_local_binding(&mut blank, index, &local, true);
        blank.push(';');
        let access = self.local_binding_document(index, &local, false);
        self.locals.slots[slot] = Some(local);
        (access, Some(blank))
    }

    fn declared_local_document(&self, index: u16, local: &Local) -> Result<Document, LiftError> {
        let mut text = self.declared_local_type(index, local)?;
        text.push(' ');
        self.append_local_binding(&mut text, index, local, true);
        Ok(text)
    }

    fn declared_local_type(&self, index: u16, local: &Local) -> Result<Document, LiftError> {
        self.require_denotable_type(&local.ty)?;
        let generic = local.generic.as_ref().map(|signature| &signature.ty);
        if let Some(range) = local.debug_range
            && let Some(annotated) = self.annotated_local_type(
                index, range, generic.map_or_else(|| (&local.ty).into(), Into::into),
            )?
        {
            return Ok(annotated);
        }
        Ok(generic.map_or_else(|| self.local_type_document(&local.ty), |ty| self.generic_type_document(ty)))
    }

    fn generic_type_document(&self, ty: &GenericType) -> Document {
        crate::emit::type_annotations::render_generic_type(ty, self.class_name, self.options.dump_text_tokens)
    }

    fn annotated_local_type(
        &self,
        index: u16,
        (start_pc, length): (u16, u16),
        ty: crate::emit::type_annotations::RenderType<'_>,
    ) -> Result<Option<Document>, LiftError> {
        self.render_code_type_at(ty, CodeTypeSite::Local(LocalTypeRange { start_pc, length, index }))
    }

    fn source_local(&self, value: &Expr) -> Option<&Local> {
        let Source::Local(slot) = value.source else { return None };
        let local = self.locals.slots.get(usize::from(slot))?.as_ref()?;
        (value.ty == local.ty && value.text == local.name).then_some(local)
    }

    fn anonymous_origin(&self, value: &Expr) -> Option<AnonymousOrigin> {
        if let Source::Anonymous(origin) = value.source {
            Some(origin)
        } else {
            self.source_local(value)?.anonymous_site
        }
    }

    pub(super) fn inferred_anonymous_origin(
        &self,
        ty: &Type,
        value: &Expr,
    ) -> Result<Option<AnonymousOrigin>, LiftError> {
        if !self.has_anonymous_type(ty) {
            return Ok(None);
        }
        if self.class.major_version < 54 {
            return Err(self.unsupported("anonymous local type inference requires Java 10"));
        }
        if matches!(ty, Type::Object(_))
            && value.ty == *ty
            && let Some(origin) = self.anonymous_origin(value)
        {
            return Ok(Some(origin));
        }
        Err(self.unsupported("anonymous local requires an initializer of its exact type"))
    }

    fn require_anonymous_assignment(
        &self,
        ty: &Type,
        origin: AnonymousOrigin,
        value: &Expr,
    ) -> Result<(), LiftError> {
        if matches!(value.source, Source::Null)
            || value.ty == *ty && self.anonymous_origin(value) == Some(origin)
        {
            return Ok(());
        }
        Err(self.unsupported("incompatible anonymous source types in assignment"))
    }

    fn local_source_signature(&self, value: &Expr) -> Option<&Rc<LocalSignature>> {
        self.source_local(value)?.generic.as_ref()
    }

    pub(super) fn local_argument_needs_erasure(&self, value: &Expr) -> bool {
        self.local_source_signature(value).is_some_and(|signature| signature.intersection)
    }

    pub(super) fn local_receiver_needs_erasure(
        &self,
        value: &Expr,
        (owner, name, raw): (&str, &str, &str),
        descriptor: &MethodDescriptor,
    ) -> bool {
        self.source_local(value).is_some_and(|local| {
            local.generic.as_ref().is_some_and(|signature| {
                !self.locals.parameters().contains(&local.name)
                    && (signature.intersection || (descriptor.parameters.iter()
                        .chain([&descriptor.return_type])
                        .any(|ty| Category::of(ty) == Some(Category::Ref))
                        && !self.local_receiver_member_is_erased(owner, name, raw)))
            })
        })
    }

    fn local_receiver_member_is_erased(&self, owner: &str, name: &str, raw: &str) -> bool {
        let class = (owner == self.owner).then_some(self.class)
            .or_else(|| self.group.and_then(|group| group.get(owner)));
        if let Some(class) = class
            && class.interfaces.is_empty()
            && class.pool.class_name(class.super_class).ok() == Some("java/lang/Object")
        {
            let mut methods = class.methods.iter().filter(|method| {
                class.pool.utf8(method.name_index).ok() == Some(name)
            });
            return methods.next().is_some_and(|method| {
                methods.next().is_none()
                    && class.pool.utf8(method.descriptor_index).ok() == Some(raw)
                    && matches!(method.signature(&class.pool), Ok(None))
            });
        }
        false
    }

    fn coerce_local_assignment(
        &self,
        value: Expr,
        ty: &Type,
        signature: Option<&LocalSignature>,
        source: Option<&LocalSignature>,
    ) -> Result<Expr, LiftError> {
        let Some(signature) = signature else { return self.coerce_assignment(value, ty) };
        if matches!(value.source, Source::Null)
            || source.is_some_and(|source| source.ty == signature.ty)
            || unbounded_generic(&signature.ty)
        {
            return self.coerce_assignment(value, ty);
        }
        if is_variable_type(&signature.ty) {
            return self.reference_cast_with_name(
                value, ty.clone(), false, Some(self.generic_type_document(&signature.ty)),
            );
        }
        let erase_rhs = (source.is_some()
            || value.observable && !value.text.starts_with("new "))
            && self.known_assignable(&value.ty, ty);
        let mut value = self.coerce_assignment(value, ty)?;
        if let Source::FunctionalCast(prefix) = value.source
            && let Some(cast) = value.text.as_flat().get(1..prefix - 1)
        {
            let rendered = signature.ty.render(self.class_name);
            if cast == rendered {
                // The initializer's exact target already comes from the declaration.
                value.text.replace_literal_prefix(prefix, "");
                value.source = Source::Plain;
                return Ok(value);
            }
        }
        if erase_rhs || matches!(value.source, Source::FunctionalCast(_)) {
            // Parameterized references of the same erasure can be provably
            // distinct in Java. Assignment through the erased type is legal.
            return self.cast(value, ty.clone(), false);
        }
        Ok(value)
    }

    fn store_debug(&self, op: &Instruction, index: u16) -> Option<LocalVariable<'c>> {
        let end = self.debug_offset(op.offset + op.len - 1) + 1;
        self.locals.debug_at(index, end)
            .or_else(|| self.locals.debug_at(index, self.debug_offset(op.offset)))
            .copied()
    }

    fn resolve_local_store(
        &self,
        op: &Instruction,
        LocalWrite { index, category }: LocalWrite,
        value: &Expr,
    ) -> Result<(Type, Option<LocalVariable<'c>>, bool), LiftError> {
        let slot = usize::from(index);
        if slot + usize::from(value.ty.slots()) > self.locals.slots.len() {
            return Err(self.invalid_local(index, "store exceeds max_locals"));
        }
        let debug = self.store_debug(op, index);
        let debug_ty = debug
            .and_then(|entry| Type::parse(entry.descriptor).ok())
            .filter(|ty| {
                Category::of(ty) == Some(category)
                    && (category != Category::Int || value.fits_int_local(ty))
            });
        let debug = debug.filter(|_| debug_ty.is_some());
        let range = debug.map(|entry| (entry.start_pc, entry.length));
        let previous = self.locals.slots[slot].as_ref();
        // The debug range separates consecutive source locals that reuse one
        // slot. Without a range, keep compatible bindings but never reassign `this`.
        let same = previous.is_some_and(|local| {
            !local.receiver
                && Category::of(&local.ty) == Some(category)
                && range == local.debug_range
                && (category != Category::Int || value.fits_int_local(&local.ty))
                && (debug.is_some()
                    || category != Category::Ref
                    || matches!(value.source, Source::Null)
                    || self.known_assignable(&value.ty, &local.ty))
        });
        let ty = if same {
            previous.expect("checked active binding").ty.clone()
        } else {
            debug_ty.unwrap_or_else(|| value.ty.clone())
        };
        Ok((ty, debug, same))
    }

    fn bind_local_store(
        &mut self,
        index: u16,
        ty: Type,
        debug: Option<LocalVariable<'c>>,
        generic: Option<Rc<LocalSignature>>,
        anonymous_site: Option<AnonymousOrigin>,
    ) -> Local {
        let slot = usize::from(index);
        let width = usize::from(ty.slots());
        if slot > 0
            && self.locals.slots[slot - 1]
                .as_ref()
                .is_some_and(|local| local.ty.slots() == 2)
        {
            self.locals.slots[slot - 1] = None;
        }
        if width == 2 {
            self.locals.slots[slot + 1] = None;
        }
        Local {
            name: self.locals.local_name(index, &ty, debug.as_ref()),
            generic,
            ty,
            anonymous_site,
            debug_range: debug.map(|entry| (entry.start_pc, entry.length)),
            receiver: false,
            token_index: self.locals.new_local_token_index(index),
            int_fits: IntFits::default(),
        }
    }

    pub(super) fn increment(&mut self, index: u16, amount: i16) -> Result<Effect, LiftError> {
        let slot = usize::from(index);
        let local = self
            .locals
            .slots
            .get(slot)
            .and_then(Option::as_ref)
            .ok_or_else(|| self.invalid_local(index, "increment of an unbound slot"))?;
        if local.ty != INT {
            return Err(self.invalid_local(index, "iinc requires an int local"));
        }
        if matches!(amount, -1 | 1)
            && self.stack.last().is_some_and(|value| {
                matches!(value.source, Source::Local(slot) if slot == index)
                    && value.text == local.name
                    && value.ty == INT
            })
        {
            self.locals.slots[slot].as_mut().expect("checked binding").int_fits = IntFits::default();
            let mut value = self.pop_category(Category::Int)?;
            value.order = Some(self.join_order(value.order, Order::at(self.offset))?);
            value.text.push_str(if amount == 1 { "++" } else { "--" });
            value.source = Source::Plain;
            value.observable = true;
            value.statement = true;
            self.push(value)?;
            return Ok(Effect::None);
        }
        if amount == 0 {
            return Ok(Effect::None);
        }
        let mut text = self.local_binding_document(index, local, false);
        match amount {
            1 => text.push_str("++;"),
            -1 => text.push_str("--;"),
            2.. => write!(text, " += {amount};").unwrap(),
            _ => write!(text, " -= {};", amount.unsigned_abs()).unwrap(),
        }
        self.locals.slots[slot].as_mut().expect("checked binding").int_fits = IntFits::default();
        self.before_statement(Some(Order::at(self.offset)))?;
        Ok(Effect::Statement(text))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{bytecode::decode, classfile::Attribute};

    #[test]
    fn plugin_names_keep_debug_parameters_and_avoid_generated_name_collisions() {
        const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x34\0\x0b\
            \x01\0\x09Collision\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
            \x01\0\x04test\x01\0\x04(I)I\x01\0\x12LocalVariableTable\
            \x01\0\x01i\x01\0\x07ignored\x01\0\x01I\
            \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";
        const BYTES: &[u8] = &[0x04, 0x3c, 0x1a, 0x1b, 0x60, 0xac];
        let class = ClassFile::parse(CLASS).unwrap();
        let method = Member {
            access_flags: 0x0008,
            name_index: 5,
            descriptor_index: 6,
            attributes: Vec::new(),
        };
        let code = Code {
            max_stack: 2,
            max_locals: 2,
            bytes: BYTES,
            exceptions: Vec::new(),
            attributes: vec![Attribute {
                name_index: 7,
                data: b"\0\x02\0\0\0\x06\0\x08\0\x0a\0\0\0\x02\0\x04\0\x09\0\x0a\0\x01",
            }],
        };
        let descriptor = MethodDescriptor::parse("(I)I").unwrap();
        let instructions = decode(BYTES).unwrap();
        for (rename_parameters, expected) in [(false, "ix"), (true, "j")] {
            let mut options = Options::default();
            options.variable_renaming = Some("jad".into());
            options.rename_parameters = rename_parameters;
            let mut machine = Machine::new(
                &class,
                &method,
                &code,
                &descriptor,
                &options,
                &str::to_owned,
            )
            .unwrap();
            assert_eq!(machine.parameter_names(), ["i"]);
            machine.step(&instructions[0]).unwrap();
            match machine.step(&instructions[1]).unwrap() {
                Effect::Statement(text) => assert_eq!(text, format!("int {expected} = 1;")),
                _ => panic!("expected local declaration"),
            }
            for instruction in &instructions[2..5] {
                machine.step(instruction).unwrap();
            }
            match machine.step(&instructions[5]).unwrap() {
                Effect::Return(Some(text)) => assert_eq!(text, format!("i + {expected}")),
                _ => panic!("expected value return"),
            }
            let ty = Type::Object("pkg/Stack10".into());
            assert_eq!(machine.locals.temporary(10), "stack10");
            assert_eq!(machine.locals.local_name(1, &ty, None), "stack10x");
            assert_eq!(machine.locals.temporary(10), "stack10xx");
        }
    }

    #[test]
    fn anonymous_temporaries_require_a_proven_initializer_and_cannot_be_blank() {
        let mut builder = crate::ClassGroupBuilder::new();
        let owner = builder
            .add(include_bytes!("../../tests/smoke/java11/TestNestedGenerics2.class"))
            .unwrap();
        builder
            .add(include_bytes!("../../tests/smoke/java11/TestNestedGenerics2$1.class"))
            .unwrap();
        let group = builder.build().unwrap();
        let class = group.get(&owner).unwrap();
        let method = class.methods.iter()
            .find(|method| class.pool.utf8(method.name_index).unwrap() == "test")
            .unwrap();
        let descriptor = MethodDescriptor::parse(class.pool.utf8(method.descriptor_index).unwrap())
            .unwrap();
        let code = method.code(&class.pool).unwrap().unwrap();
        let instructions = decode(code.bytes).unwrap();
        let options = Options::default();
        let class_name = |name: &str| name.rsplit('/').next().unwrap().into();
        let mut baseline = Machine::new(class, method, &code, &descriptor, &options, &class_name)
            .unwrap()
            .with_group(&group);
        baseline.set_anonymous_sites(Rc::new(RefCell::new(Default::default())));

        let mut initialized = baseline.clone();
        let mut duplicate = baseline.clone();
        // The fixture starts with new, dup, and invokespecial, before astore.
        for op in &instructions[..3] {
            initialized.step(op).unwrap();
            duplicate.step(op).unwrap();
        }
        let mut null = baseline.clone();
        null.step(&decode(&[0x01]).unwrap()[0]).unwrap();
        assert!(matches!(
            baseline.merge_stack(&[&initialized, &null], 7),
            Err(LiftError::Unsupported { .. })
        ));

        let mut named = initialized.clone();
        assert!(matches!(
            named.step(&instructions[3]).unwrap(),
            Effect::Statement(text) if text.starts_with("var instance = new Object()")
        ));
        named.step(&instructions[4]).unwrap();
        let loaded = named.pop_raw().unwrap();
        let origin = named.anonymous_origin(&loaded).unwrap();
        let other = duplicate.pop_raw().unwrap();
        assert_eq!(loaded.ty, other.ty);
        assert!(named.require_anonymous_assignment(&loaded.ty, origin, &other).is_err());

        let mut value = initialized.pop_raw().unwrap();
        let mut unproved = Expr::atom(value.ty.clone(), "unproved".into());
        assert!(initialized.spill(&mut unproved).is_err());
        initialized.spill(&mut value).unwrap();
        let statements = initialized.take_prelude();
        assert_eq!(statements.len(), 1);
        assert!(statements[0].starts_with("var stack"));
        assert!(statements[0].contains(" = new Object()"));
        assert_eq!(initialized.inferred_anonymous_origin(&value.ty, &value).unwrap(), Some(origin));
    }

    #[test]
    fn local_generic_cast_stops_at_first_type_argument_list() {
        for (signature, name) in [
            ("[[TT;", "T[]"),
            ("[Lpkg/Outer<TT;>.Inner<TT;>;", "Outer"),
            ("Lpkg/Outer.Inner<TT;>;", "Inner"),
        ] {
            let ty = FieldSignature::parse(signature).unwrap().field_type;
            assert_eq!(generic_cast_name(&ty), name);
        }
    }
}
