// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{cell::RefCell, collections::HashSet, rc::Rc};

use crate::{
    bytecode::Instruction,
    classfile::{ClassFile, Code, Constant, LocalVariable, Member},
    descriptor::{MethodDescriptor, Type},
    options::Options,
};

use super::{
    Effect, LiftError, Machine,
    expr::{Category, Expr, INT, Order, Source},
};

#[derive(Clone, Debug, Eq, PartialEq)]
struct Local {
    name: String,
    ty: Type,
    debug_range: Option<(u16, u16)>,
    receiver: bool,
}

#[derive(Default)]
struct Names {
    used: HashSet<String>,
    suffix: u32,
}

impl Names {
    fn fresh(&mut self, name: &str) -> String {
        if self.used.insert(name.to_owned()) {
            return name.to_owned();
        }
        loop {
            self.suffix += 1;
            let candidate = format!("{name}_{}", self.suffix);
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

#[derive(Clone)]
pub(super) struct Locals<'a> {
    slots: Vec<Option<Local>>,
    debug: Rc<[LocalVariable<'a>]>,
    names: Rc<RefCell<Names>>,
    parameter_names: Rc<[String]>,
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
        let mut names = Names::default();
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
            if field.access_flags & 0x0018 == 0x0018 {
                names.used.insert(class.pool.utf8(field.name_index)?.into());
            }
        }
        let debug = if options.use_debug_names {
            code.local_variables(&class.pool)?
        } else {
            Vec::new()
        };
        let mut result = Self {
            slots: vec![None; usize::from(code.max_locals)],
            debug: debug.into(),
            names: Rc::new(RefCell::new(names)),
            parameter_names: Rc::default(),
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
            let fallback = format!("param{ordinal}");
            let name = result.names.borrow_mut().fresh(
                marked_name
                    .filter(|name| identifier(name))
                    .or_else(|| {
                        debug
                            .map(|entry| entry.name)
                            .filter(|name| identifier(name))
                    })
                    .unwrap_or(&fallback),
            );
            let debug_range = debug.map(|entry| (entry.start_pc, entry.length));
            parameter_names.push(name.clone());
            result.slots[usize::from(index)] = Some(Local {
                name,
                ty: ty.clone(),
                debug_range,
                receiver: false,
            });
            index += ty.slots();
        }
        result.parameter_names = parameter_names.into();
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
        self.names.borrow_mut().fresh(&format!("stack{offset}"))
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
}

impl Machine<'_, '_> {
    pub(crate) fn bind_caught_exception(
        &mut self,
        catch_type: u16,
        store: &Instruction,
    ) -> Result<(String, String), LiftError> {
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
        let debug = self.locals.debug_at(index, store.offset + store.len);
        let range = debug.map(|entry| (entry.start_pc, entry.length));
        let fallback = format!("var{index}");
        let name = self.locals.names.borrow_mut().fresh(
            debug
                .map(|entry| entry.name)
                .filter(|name| identifier(name))
                .unwrap_or(&fallback),
        );
        let display_type = self.render_type(&ty);
        self.locals.slots[slot] = Some(Local {
            name: name.clone(),
            ty,
            debug_range: range,
            receiver: false,
        });
        Ok((display_type, name))
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
        let mut expr = Expr::atom(local.ty.clone(), local.name.clone());
        if local.receiver {
            expr.source = Source::This;
        } else {
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
        let debug = self
            .locals
            .debug_at(index, op.offset + op.len)
            .or_else(|| self.locals.debug_at(index, op.offset));
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
        let (ty, name, prefix) = if same {
            let local = previous.expect("checked active binding");
            (local.ty.clone(), local.name.clone(), String::new())
        } else {
            let ty = debug_ty.unwrap_or_else(|| value.ty.clone());
            let fallback = format!("var{index}");
            let name = self.locals.names.borrow_mut().fresh(
                debug
                    .map(|entry| entry.name)
                    .filter(|name| identifier(name))
                    .unwrap_or(&fallback),
            );
            let prefix = format!("{} ", self.render_type(&ty));
            (ty, name, prefix)
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
        self.locals.slots[slot] = Some(Local {
            name: name.clone(),
            ty,
            debug_range: range,
            receiver: false,
        });
        Ok(Effect::Statement(format!(
            "{prefix}{name} = {};",
            value.text
        )))
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
        let text = match amount {
            1 => format!("{}++;", local.name),
            -1 => format!("{}--;", local.name),
            0 => return Ok(Effect::None),
            2.. => format!("{} += {amount};", local.name),
            _ => format!("{} -= {};", local.name, amount.unsigned_abs()),
        };
        self.before_statement(Some(Order::at(self.offset)))?;
        Ok(Effect::Statement(text))
    }
}

fn identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|ch| ch.is_alphabetic() || matches!(ch, '$' | '_'))
        && chars.all(|ch| ch.is_alphanumeric() || matches!(ch, '$' | '_'))
        && !matches!(
            name,
            "abstract"
                | "assert"
                | "boolean"
                | "break"
                | "byte"
                | "case"
                | "catch"
                | "char"
                | "class"
                | "const"
                | "continue"
                | "default"
                | "do"
                | "double"
                | "else"
                | "enum"
                | "extends"
                | "false"
                | "final"
                | "finally"
                | "float"
                | "for"
                | "goto"
                | "if"
                | "implements"
                | "import"
                | "instanceof"
                | "int"
                | "interface"
                | "long"
                | "native"
                | "new"
                | "null"
                | "package"
                | "permits"
                | "private"
                | "protected"
                | "public"
                | "record"
                | "return"
                | "sealed"
                | "short"
                | "static"
                | "strictfp"
                | "super"
                | "switch"
                | "synchronized"
                | "this"
                | "throw"
                | "throws"
                | "transient"
                | "true"
                | "try"
                | "var"
                | "void"
                | "volatile"
                | "while"
                | "yield"
                | "_"
        )
}
