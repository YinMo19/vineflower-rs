// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{collections::BTreeMap, ops::Range, rc::Rc};

use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::{ClassError, ClassFile, find_attribute},
    context::{ClassGroup, NestedKind},
    descriptor::{MethodDescriptor, Type},
};

use super::super::{LiftError, Machine, expr::Expr};
use super::{
    AnonymousBindings, Capture, CaptureFrame,
    capture::{CaptureOrigin, CaptureStore, capture_store},
    loaded_parameter, writes_local,
};

pub(crate) struct LocalSite {
    class: Rc<str>,
    offset: u32,
    plan: Rc<LocalPlan>,
    bindings: Rc<[Capture]>,
    enclosing_names: crate::lift::locals::LexicalNames,
}

impl LocalSite {
    pub(crate) fn class(&self) -> &str {
        &self.class
    }

    pub(crate) fn offset(&self) -> u32 {
        self.offset
    }

    pub(crate) fn same_bindings(&self, other: &Self) -> bool {
        self.bindings
            .iter()
            .zip(other.bindings.iter())
            .all(|(a, b)| a.same_field(b) && a.same_lexical_binding(b))
            && self.bindings.len() == other.bindings.len()
    }

    pub(crate) fn declarations(&self) -> impl Iterator<Item = u32> {
        self.bindings.iter().filter_map(Capture::declaration)
    }

    pub(crate) fn bindings(&self, parent: Option<AnonymousBindings>) -> AnonymousBindings {
        CaptureFrame::named(
            Rc::clone(&self.class),
            Rc::clone(&self.bindings),
            Rc::clone(&self.plan),
            parent,
            self.enclosing_names.clone(),
        )
    }
}

pub(super) struct LocalPlan {
    fields: Vec<LocalField>,
    constructors: BTreeMap<String, Vec<LocalArgument>>,
}

struct LocalField {
    name: String,
    descriptor: String,
}

pub(super) struct LocalArgument {
    pub(super) field: usize,
    pub(super) ordinal: usize,
    pub(super) slot: u16,
    pub(super) store: Option<u32>,
}

impl LocalPlan {
    pub(super) fn constructor(&self, descriptor: &str) -> Option<&[LocalArgument]> {
        Some(self.constructors.get(descriptor)?.as_slice())
    }

    fn read(
        group: &ClassGroup<'_>,
        class: &ClassFile<'_>,
        owner: &str,
    ) -> Result<Option<Self>, LiftError> {
        let pool = &class.pool;
        let mut fields = Vec::new();
        for field in &class.fields {
            let name = pool.utf8(field.name_index)?;
            let descriptor = pool.utf8(field.descriptor_index)?;
            if local_capture_field(group, class, owner, field, name, descriptor)? {
                fields.push(LocalField {
                    name: name.into(),
                    descriptor: descriptor.into(),
                });
            }
        }
        if fields.is_empty() {
            return Ok(None);
        }
        let superclass = (class.super_class != 0)
            .then(|| pool.class_name(class.super_class))
            .transpose()?;
        let mut layouts = BTreeMap::new();
        for method in &class.methods {
            if pool.utf8(method.name_index)? != "<init>" {
                continue;
            }
            let descriptor = pool.utf8(method.descriptor_index)?;
            let signature = MethodDescriptor::parse(descriptor)?;
            let code = method.code(pool)?.ok_or_else(layout)?;
            let instructions = bytecode::decode(code.bytes).map_err(|_| layout())?;
            let mut stores = Vec::new();
            let prefix = scan_stores(
                group,
                class,
                owner,
                &fields,
                &signature.parameters,
                &instructions,
                &mut stores,
            )?;
            if instructions.get(prefix).is_none_or(|op| op.opcode != 0x2a) {
                return Err(layout());
            }
            // A local allocation before the chaining call would make a plain
            // member-reference scan ambiguous; the receiver proof applies only
            // to this linear constructor prefix.
            let mut chain = None;
            for (index, op) in instructions.iter().enumerate().skip(prefix + 1) {
                if matches!(op.operand, Operand::Branch(_) | Operand::Switch { .. })
                    || matches!(op.opcode, 0xbb | 0xac..=0xb1 | 0xbf)
                {
                    return Err(layout());
                }
                if op.opcode == 0xb7
                    && let Operand::Constant(cp) = op.operand
                {
                    let (target, name, descriptor) = pool.member_ref(cp)?;
                    if name == "<init>" && (target == owner || Some(target) == superclass) {
                        chain = Some((index, target, descriptor));
                        break;
                    }
                }
            }
            let (chain_at, target, target_descriptor) = chain.ok_or_else(layout)?;
            let delegate = if target == owner {
                if !stores.is_empty() {
                    return Err(layout());
                }
                Some((target_descriptor, prefix + 1..chain_at))
            } else {
                scan_stores(
                    group,
                    class,
                    owner,
                    &fields,
                    &signature.parameters,
                    &instructions[chain_at + 1..],
                    &mut stores,
                )?;
                if stores.len() != fields.len() {
                    return Err(layout());
                }
                None
            };
            if stores
                .iter()
                .any(|capture| instructions.iter().any(|op| writes_local(op, capture.slot)))
                || (!code.exceptions.is_empty()
                    && code
                        .exceptions
                        .iter()
                        .any(|handler| u32::from(handler.start_pc) < instructions[chain_at].offset))
            {
                return Err(layout());
            }
            // Check the direct constructor's suffix now; delegation is resolved
            // below after the target shape is known, independently of file order.
            if delegate.is_none() && !is_capture_suffix(&stores, signature.parameters.len()) {
                return Err(layout());
            }
            layouts.insert(
                descriptor.to_owned(),
                Pending {
                    signature,
                    stores,
                    delegate,
                    instructions,
                },
            );
        }
        if layouts.is_empty() {
            return Err(layout());
        }
        let mut constructors = BTreeMap::new();
        while !layouts.is_empty() {
            let Some(next) = layouts
                .iter()
                .find_map(|(desc, pending)| {
                    pending
                        .delegate
                        .as_ref()
                        .is_none_or(|(desc, _)| constructors.contains_key(*desc))
                        .then_some(desc)
                })
                .cloned()
            else {
                return Err(layout());
            };
            let mut pending = layouts.remove(&next).expect("known pending constructor");
            if let Some((target, range)) = pending.delegate {
                let forwarded: &Vec<LocalArgument> = &constructors[target];
                let loads = &pending.instructions[range];
                let tail = loads
                    .get(
                        loads
                            .len()
                            .checked_sub(forwarded.len())
                            .ok_or_else(layout)?..,
                    )
                    .ok_or_else(layout)?;
                // Capture ordinals may be reordered, while ordinary source
                // arguments (including any observable expressions) are untouched.
                let mut target_order: Vec<_> = forwarded.iter().collect();
                target_order.sort_by_key(|argument| argument.ordinal);
                for (argument, load) in target_order.into_iter().zip(tail) {
                    let (ordinal, slot) =
                        loaded_parameter(load, &pending.signature.parameters).ok_or_else(layout)?;
                    if pending.signature.parameters[ordinal]
                        != Type::parse(&fields[argument.field].descriptor)?
                        || pending.instructions.iter().any(|op| writes_local(op, slot))
                    {
                        return Err(layout());
                    }
                    pending.stores.push(LocalArgument {
                        field: argument.field,
                        ordinal,
                        slot,
                        store: None,
                    });
                }
                if !is_capture_suffix(&pending.stores, pending.signature.parameters.len()) {
                    return Err(layout());
                }
            }
            pending.stores.sort_by_key(|argument| argument.field);
            constructors.insert(next, pending.stores);
        }
        Ok(Some(Self {
            fields,
            constructors,
        }))
    }
}

struct Pending<'a> {
    signature: MethodDescriptor,
    stores: Vec<LocalArgument>,
    delegate: Option<(&'a str, Range<usize>)>,
    instructions: Vec<Instruction>,
}

fn layout() -> LiftError {
    LiftError::Unsupported {
        offset: 0,
        opcode: 0xb7,
        reason: "unrecognized captured local-class constructor layout",
    }
}

fn is_capture_suffix(captures: &[LocalArgument], parameters: usize) -> bool {
    let Some(start) = parameters.checked_sub(captures.len()) else {
        return false;
    };
    (start..parameters).all(|index| captures.iter().any(|capture| capture.ordinal == index))
}

fn scan_stores(
    group: &ClassGroup<'_>,
    class: &ClassFile<'_>,
    owner: &str,
    fields: &[LocalField],
    parameters: &[Type],
    instructions: &[Instruction],
    found: &mut Vec<LocalArgument>,
) -> Result<usize, LiftError> {
    let mut offset = 0;
    while let Some(CaptureStore {
        field,
        descriptor,
        ordinal,
        slot,
        offset: store,
    }) = capture_store(class, owner, parameters, &instructions[offset..])?
    {
        if group.outer_field(owner, field, descriptor).is_some() {
            if ordinal != 0 {
                return Err(layout());
            }
        } else {
            let field = fields
                .iter()
                .position(|candidate| candidate.name == field && candidate.descriptor == descriptor)
                .ok_or_else(layout)?;
            if found
                .iter()
                .any(|prior| prior.field == field || prior.ordinal == ordinal)
            {
                return Err(layout());
            }
            found.push(LocalArgument {
                field,
                ordinal,
                slot,
                store: Some(store),
            });
        }
        offset += 3;
    }
    Ok(offset)
}

pub(crate) fn local_capture_field(
    group: &ClassGroup<'_>,
    class: &ClassFile<'_>,
    owner: &str,
    field: &crate::classfile::Member<'_>,
    name: &str,
    descriptor: &str,
) -> Result<bool, ClassError> {
    Ok(field.access_flags & (0x0008 | 0x0010) == 0x0010
        && (field.access_flags & 0x1000 != 0
            || find_attribute(&field.attributes, &class.pool, "Synthetic")?.is_some())
        && group.outer_field(owner, name, descriptor).is_none())
}

impl Machine<'_, '_> {
    pub(in crate::lift) fn local_constructor_arguments<'args>(
        &self,
        owner: &str,
        descriptor: &str,
        args: &'args [Expr],
    ) -> Result<&'args [Expr], LiftError> {
        let Some(group) = self.group else {
            return Ok(args);
        };
        let Some(node) = group
            .nested_class(owner)
            .filter(|node| matches!(node.kind, NestedKind::Local(_)))
        else {
            return Ok(args);
        };
        if !group.is_attached(owner) {
            return Ok(args);
        }
        let class = group
            .get(owner)
            .expect("attached local class is registered");
        let known = self
            .anonymous_bindings
            .as_deref()
            .and_then(|bindings| bindings.named_frame(owner));
        let prior = self.anonymous_sites.as_ref().and_then(|registry| {
            registry
                .borrow()
                .local_sites(owner)
                .next()
                .map(|site| Rc::clone(&site.plan))
        });
        let plan = if let Some((plan, _)) = known {
            Rc::clone(plan)
        } else if let Some(plan) = prior {
            plan
        } else {
            let Some(plan) = LocalPlan::read(group, class, owner)? else {
                return Ok(args);
            };
            Rc::new(plan)
        };
        let constructor = plan.constructor(descriptor).ok_or_else(layout)?;
        if let Some((_, bindings)) = known {
            for (argument, capture) in constructor.iter().zip(bindings.iter()) {
                let arg = args.get(argument.ordinal).ok_or_else(layout)?;
                if !capture.matches_capture_argument(arg) {
                    return Err(self.unsupported("local constructor changes its captured variable"));
                }
            }
        } else {
            let method_descriptor = self.class.pool.utf8(self.method.descriptor_index)?;
            if node.outer != self.owner
                || !node.method.as_ref().is_some_and(|(name, desc)| {
                    name == self.method_name && desc == method_descriptor
                })
            {
                return Err(
                    self.unsupported("captured local class constructed outside declaration scope")
                );
            }
            let registry = self.anonymous_sites.as_ref().ok_or_else(layout)?;
            let mut bindings = Vec::with_capacity(constructor.len());
            for argument in constructor {
                let arg = args.get(argument.ordinal).ok_or_else(layout)?;
                let owner_field = &plan.fields[argument.field];
                let origin = self.capture_argument(arg).ok_or_else(|| {
                    self.unsupported(
                        "local-class capture is not an effectively final lexical variable",
                    )
                })?;
                if matches!(
                    origin,
                    CaptureOrigin::Local {
                        declaration: None,
                        parameter: false,
                        ..
                    }
                ) {
                    return Err(
                        self.unsupported("cannot locate declaration of local-class capture")
                    );
                }
                bindings.push(Capture::new(
                    argument.ordinal,
                    argument.slot,
                    &owner_field.name,
                    &owner_field.descriptor,
                    &arg.text,
                    Type::parse(&owner_field.descriptor)?,
                    origin,
                ));
            }
            registry.borrow_mut().push_local(LocalSite {
                class: owner.into(),
                offset: self.debug_offset(self.offset),
                plan: Rc::clone(&plan),
                bindings: bindings.into(),
                enclosing_names: self.locals.lexical_names(),
            });
        }
        Ok(&args[..args
            .len()
            .checked_sub(constructor.len())
            .ok_or_else(layout)?])
    }
}

#[cfg(test)]
#[path = "local_class_tests.rs"]
mod tests;
