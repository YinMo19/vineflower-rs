// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Write,
    rc::Rc,
};

use crate::{
    bytecode::Instruction,
    classfile::{ClassFile, Code, Constant, LocalVariable, Member},
    descriptor::{FieldSignature, GenericType, MethodDescriptor, Type},
    naming::{VariableNamer, VariableRenamer, is_valid_local_identifier},
    options::Options,
    source_text::Document,
};

use super::{
    Effect, LiftError, Machine,
    expr::{Category, Expr, INT, Order, Source},
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
    debug_range: Option<(u16, u16)>,
    receiver: bool,
    token_index: Option<u32>,
}

impl PartialEq for Local {
    fn eq(&self, other: &Self) -> bool {
        // Optional token metadata does not decide whether a binding can be
        // represented by the same declaration at a control-flow join.
        self.name == other.name
            && self.ty == other.ty
            && self.debug_range == other.debug_range
            && self.receiver == other.receiver
    }
}

impl Eq for Local {}

#[derive(Clone, Default)]
pub(crate) struct Names {
    used: HashSet<String>,
    suffix: u32,
    version: u16,
    namer: Option<VariableNamer>,
    token_indices: Option<LocalTokenIndices>,
}

impl Names {
    fn fresh(&mut self, name: &str) -> String {
        self.fresh_owned(name.into())
    }

    fn fresh_owned(&mut self, mut name: String) -> String {
        if !self.used.contains(&name) {
            self.used.insert(name.clone());
            return name;
        }
        if self.namer.is_some() {
            while self.used.contains(&name) {
                name.push('x');
            }
            self.used.insert(name.clone());
            return name;
        }
        loop {
            self.suffix += 1;
            let candidate = format!("{name}_{}", self.suffix);
            if self.used.insert(candidate.clone()) {
                return candidate;
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

type GenericSignatures<'a> = HashMap<(u16, u16, u16), &'a str>;

#[derive(Clone)]
pub(super) struct Locals<'a> {
    slots: Vec<Option<Local>>,
    debug: Rc<[LocalVariable<'a>]>,
    generic: Option<Rc<GenericSignatures<'a>>>,
    use_debug_names: bool,
    names: Rc<RefCell<Names>>,
    parameter_names: Rc<[String]>,
    tokens: Option<local_tokens::LocalTokens<'a>>,
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
                names
                    .used
                    .insert(leaf.split('$').next().unwrap_or(leaf).into());
                if let Some((package, _)) = name.split_once('/') {
                    names.used.insert(package.into());
                }
            }
        }
        for field in &class.fields {
            if custom_names || field.access_flags & 0x0018 == 0x0018 {
                names.used.insert(class.pool.utf8(field.name_index)?.into());
            }
        }
        let debug = if options.use_debug_names || custom_names {
            code.local_variables(&class.pool)?
        } else {
            Vec::new()
        };
        let generic = if custom_names && !debug.is_empty() {
            let entries = code.local_variable_types(&class.pool)?;
            (!entries.is_empty()).then(|| {
                Rc::new(
                    entries
                        .into_iter()
                        .map(|entry| {
                            (
                                (entry.index, entry.start_pc, entry.length),
                                entry.descriptor,
                            )
                        })
                        .collect(),
                )
            })
        } else {
            None
        };
        let mut result = Self {
            slots: vec![None; usize::from(code.max_locals)],
            debug: debug.into(),
            generic,
            use_debug_names: options.use_debug_names,
            names: Rc::new(RefCell::new(names)),
            parameter_names: Rc::default(),
            tokens: None,
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
                debug_range: None,
                receiver: true,
                token_index: None,
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
                || result.generic_cast(debug),
                || format!("var{index}"),
            );
            let debug_range = debug.map(|entry| (entry.start_pc, entry.length));
            parameter_names.push(name.clone());
            result.slots[usize::from(index)] = Some(Local {
                name,
                ty: ty.clone(),
                debug_range,
                receiver: false,
                token_index: None,
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

    fn generic_cast(&self, debug: Option<&LocalVariable<'a>>) -> Option<String> {
        let entry = debug?;
        let signature = self
            .generic
            .as_ref()?
            .get(&(entry.index, entry.start_pc, entry.length))?;
        let signature = FieldSignature::parse(signature).ok()?;
        Some(generic_cast_name(signature.field_type))
    }

    fn local_name(&self, index: u16, ty: &Type, debug: Option<&LocalVariable<'a>>) -> String {
        self.names.borrow_mut().binding(
            false,
            index,
            ty,
            [self.debug_name(debug), None],
            || self.generic_cast(debug),
            || format!("var{index}"),
        )
    }
}

// Both providers discard the type arguments before looking for the leaf name.
// Avoid rendering generic arguments that do not contribute to the name.
fn generic_cast_name(ty: GenericType) -> String {
    let (element, array) = match ty {
        GenericType::Array { element, .. } => (*element, true),
        _ => (ty, false),
    };
    let (mut name, has_arguments) = match element {
        GenericType::Class(class) => {
            let mut leaf = class.internal_name;
            let mut has_arguments = !class.arguments.is_empty();
            for nested in class.nested {
                if has_arguments {
                    break;
                }
                leaf = nested.name;
                has_arguments = !nested.arguments.is_empty();
            }
            if let Some(index) = leaf.rfind('/') {
                leaf.drain(..=index);
            }
            (leaf, has_arguments)
        }
        GenericType::Variable(name) => (name, false),
        GenericType::Primitive(primitive) => (primitive.java_name().into(), false),
        GenericType::Void | GenericType::Array { .. } => {
            unreachable!("parsed field signatures have one array node and no void")
        }
    };
    if array && !has_arguments {
        name.push_str("[]");
    }
    name
}

impl Machine<'_, '_> {
    pub(crate) fn resource_local(&self, index: u16) -> Option<(String, &str)> {
        let local = self.locals.slots.get(usize::from(index))?.as_ref()?;
        let Type::Object(class) = &local.ty else {
            return None;
        };
        if local.receiver || !self.is_auto_closeable(class) {
            return None;
        }
        Some((self.render_type(&local.ty), &local.name))
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
            debug_range: range,
            receiver: false,
            token_index: self.locals.new_local_token_index(index),
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

    pub(super) fn load(&mut self, index: u16, category: Category) -> Result<(), LiftError> {
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
        }
        self.push(expr)
    }

    pub(super) fn store(
        &mut self,
        op: &Instruction,
        index: u16,
        category: Category,
    ) -> Result<Effect, LiftError> {
        let value = self.pop_category(category)?;
        let slot = usize::from(index);
        let width = usize::from(value.ty.slots());
        if slot + width > self.locals.slots.len() {
            return Err(self.invalid_local(index, "store exceeds max_locals"));
        }
        let end = self.debug_offset(op.offset + op.len - 1) + 1;
        let debug = self
            .locals
            .debug_at(index, end)
            .or_else(|| self.locals.debug_at(index, self.debug_offset(op.offset)));
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
        let (ty, name, token_index) = if same {
            let local = previous.expect("checked active binding");
            (local.ty.clone(), local.name.clone(), local.token_index)
        } else {
            let ty = debug_ty.unwrap_or_else(|| value.ty.clone());
            let name = self.locals.local_name(index, &ty, debug);
            (ty, name, None)
        };
        let value = self.coerce(value, &ty, false)?;
        self.before_statement(value.order)?;
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
        let token_index = if same {
            token_index
        } else {
            self.locals.new_local_token_index(index)
        };
        let local = Local {
            name,
            ty,
            debug_range: range,
            receiver: false,
            token_index,
        };
        let mut text = if same {
            Document::new()
        } else {
            let mut ty = self.local_type_document(&local.ty);
            ty.push(' ');
            ty
        };
        self.append_local_binding(&mut text, index, &local, !same);
        self.locals.slots[slot] = Some(local);
        text.push_str(" = ");
        text.append(value.text);
        text.push(';');
        Ok(Effect::Statement(text))
    }

    pub(super) fn increment(&mut self, index: u16, amount: i16) -> Result<Effect, LiftError> {
        let local = self
            .locals
            .slots
            .get(usize::from(index))
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
    fn local_generic_cast_stops_at_first_type_argument_list() {
        for (signature, name) in [
            ("[[TT;", "T[]"),
            ("[Lpkg/Outer<TT;>.Inner<TT;>;", "Outer"),
            ("Lpkg/Outer.Inner<TT;>;", "Inner"),
        ] {
            let ty = FieldSignature::parse(signature).unwrap().field_type;
            assert_eq!(generic_cast_name(ty), name);
        }
    }
}
