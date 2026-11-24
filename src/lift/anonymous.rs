// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{cell::RefCell, fmt::Write, rc::Rc};

use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::ClassFile,
    context::NestedKind,
    descriptor::{ClassSignature, GenericType, MethodDescriptor, Type, TypeArgument},
    source_text::Document,
};

use super::{
    LiftError, Machine,
    expr::{AnonymousOrigin, Expr, Source},
    nested::parameter_load_slot,
};

#[path = "anonymous_capture.rs"]
mod capture;
pub(crate) use capture::AnonymousBindings;
use capture::{Capture, CaptureFrame, loaded_parameter, writes_local};
use super::locals::LexicalNames;

#[path = "local_classes.rs"]
mod local;
use local::LocalSite;

pub(crate) type AnonymousSites = Rc<RefCell<NestedSites>>;

#[derive(Default)]
pub(crate) struct NestedSites {
    entries: Vec<NestedSite>,
    enclosing_names: Option<LexicalNames>,
}

enum NestedSite {
    Anonymous(AnonymousSite),
    Local(LocalSite),
}

impl NestedSites {
    pub(crate) fn uncaptured_local_bindings(
        &self,
        owner: &str,
        parent: Option<AnonymousBindings>,
    ) -> Option<AnonymousBindings> {
        Some(CaptureFrame::bind(
            owner.into(),
            Rc::default(),
            parent,
            Some(self.enclosing_names.clone()?),
        ))
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn truncate(&mut self, len: usize) {
        self.entries.truncate(len);
    }

    pub(crate) fn push(&mut self, site: AnonymousSite) {
        self.entries.push(NestedSite::Anonymous(site));
    }

    pub(crate) fn get(&self, index: usize) -> Option<&AnonymousSite> {
        match self.entries.get(index)? {
            NestedSite::Anonymous(site) => Some(site),
            NestedSite::Local(_) => None,
        }
    }

    pub(crate) fn local_sites<'s>(&'s self, class: &'s str) -> impl Iterator<Item = &'s LocalSite> {
        self.entries.iter().filter_map(move |entry| match entry {
            NestedSite::Local(site) if site.class() == class => Some(site),
            _ => None,
        })
    }

    fn push_local(&mut self, site: LocalSite) {
        self.entries.push(NestedSite::Local(site));
    }
}

pub(crate) struct AnonymousSite {
    pub class: Rc<str>,
    pub descriptor: String,
    pub instructions: Vec<Instruction>,
    pub initializer_start: usize,
    captures: Option<Rc<[Capture]>>,
    enclosing_names: Option<LexicalNames>,
}

impl AnonymousSite {
    pub(crate) fn uncaptured(
        class: &str,
        descriptor: &str,
        instructions: Vec<Instruction>,
        initializer_start: usize,
    ) -> Self {
        Self {
            class: class.into(),
            descriptor: descriptor.into(),
            instructions,
            initializer_start,
            captures: None,
            enclosing_names: None,
        }
    }

    pub(crate) fn capture_bindings(
        &self,
        parent: Option<AnonymousBindings>,
    ) -> Option<AnonymousBindings> {
        if self.captures.is_none() && self.enclosing_names.is_none() {
            return parent;
        }
        Some(CaptureFrame::bind(
            Rc::clone(&self.class),
            self.captures.clone().unwrap_or_default(),
            parent,
            self.enclosing_names.clone(),
        ))
    }

    pub(crate) fn captures_field(&self, name: &str, descriptor: &str) -> bool {
        self.captures.as_ref().is_some_and(|captures| {
            captures
                .iter()
                .any(|capture| capture.is_field(name, descriptor))
        })
    }
}

impl Machine<'_, '_> {
    pub(crate) fn set_anonymous_sites(&mut self, sites: AnonymousSites) {
        sites.borrow_mut().enclosing_names = Some(self.locals.lexical_names());
        self.anonymous_sites = Some(sites);
    }

    pub(crate) fn mark_initialized_this(&mut self) {
        self.initialized_this = true;
    }

    /// Decode the synthetic constructor before rendering an anonymous class.
    /// Its enclosing instance is implicit, and its explicit arguments are
    /// forwarded exactly once and in order to the selected super constructor.
    pub(super) fn anonymous_construction(
        &self,
        owner: &str,
        descriptor: &str,
        args: &[Expr],
    ) -> Result<Option<(Document, AnonymousOrigin)>, LiftError> {
        let Some(group) = self.group.filter(|_| self.options.decompile_inner) else {
            return Ok(None);
        };
        let Some(node) = group
            .nested_class(owner)
            .filter(|node| matches!(node.kind, NestedKind::Anonymous))
        else {
            return Ok(None);
        };
        if !group.is_attached(owner) {
            return Ok(None);
        }
        if node.outer != self.owner {
            return Err(self.unsupported("anonymous construction outside its lexical class"));
        }
        let class = group.get(owner).expect("attached class is registered");
        let pool = &class.pool;
        let fail = || self.unsupported("unrecognized anonymous constructor forwarding layout");
        let sites = self.anonymous_sites.as_ref().ok_or_else(fail)?;
        let mut constructor = None;
        for method in &class.methods {
            if pool.utf8(method.name_index)? == "<init>"
                && pool.utf8(method.descriptor_index)? == descriptor
            {
                constructor = method.code(pool)?;
                break;
            }
        }
        let code = constructor.ok_or_else(fail)?;
        let constructor_type = MethodDescriptor::parse(descriptor)?;
        let instructions = bytecode::decode(code.bytes).map_err(|_| fail())?;
        let enclosing = group.constructor_outer(owner, descriptor);
        let implicit = usize::from(enclosing.is_some());
        if let Some(enclosing) = enclosing && !args.first().is_some_and(|argument| {
            matches!(argument.source, Source::This | Source::OuterThis)
                && matches!(&argument.ty, Type::Object(ty) if group.is_assignable(ty, enclosing))
        }) {
            return Err(fail());
        }
        let mut captures = ConstructorCaptures {
            owner,
            class,
            parameters: &constructor_type.parameters,
            args,
            enclosing,
            fields: Vec::new(),
            enclosing_assigned: false,
        };
        let prefix = captures.skip_stores(self, &instructions)?;
        let remaining = instructions.get(prefix..).ok_or_else(fail)?;
        let Some((receiver, remaining)) = remaining.split_first() else {
            return Err(fail());
        };
        if receiver.opcode != 0x2a {
            return Err(fail());
        }
        let super_call = remaining
            .iter()
            .position(|op| op.opcode == 0xb7)
            .ok_or_else(fail)?;
        let super_op = &remaining[super_call];
        let Operand::Constant(super_index) = super_op.operand else {
            return Err(fail());
        };
        let (super_owner, super_name, super_descriptor) = pool.member_ref(super_index)?;
        if super_name != "<init>"
            || class.super_class == 0
            || pool.class_name(class.super_class)? != super_owner
        {
            return Err(fail());
        }
        let mut loads = &remaining[..super_call];
        let super_descriptor = if let Some((last, prefix)) = loads.split_last()
            && last.opcode == 0x01
            && let Some(target) =
                self.legacy_constructor_descriptor(super_owner, super_descriptor)?
        {
            loads = prefix;
            target
        } else {
            super_descriptor
        };
        let super_type = MethodDescriptor::parse(super_descriptor)?;
        let first = match loads.first() {
            Some(load) => {
                loaded_parameter(load, captures.parameters)
                    .ok_or_else(fail)?
                    .0
            }
            None => 0,
        };
        let last = first + loads.len();
        let prepared = captures.parameters.get(first..last).ok_or_else(fail)?;
        if prepared != super_type.parameters.as_slice()
            || loads.iter().enumerate().any(|(index, load)| {
                loaded_parameter(load, captures.parameters)
                    .is_none_or(|(ordinal, _)| ordinal != first + index)
            })
        {
            return Err(fail());
        }
        let super_end = prefix + super_call + 2;
        let initializer_start =
            super_end + captures.skip_stores(self, &instructions[super_end..])?;
        if (0..captures.parameters.len()).any(|index| {
            index >= implicit
                && !(first..last).contains(&index)
                && !captures
                    .fields
                    .iter()
                    .any(|capture| capture.parameter == index)
        }) {
            return Err(fail());
        }
        let tail = &instructions[initializer_start..];
        let first_offset = tail.first().ok_or_else(fail)?.offset;
        if code
            .exceptions
            .iter()
            .any(|handler| u32::from(handler.start_pc) < first_offset)
            || constructor_parameters_are_used(
                tail,
                captures.parameters,
                implicit,
                &captures.fields,
            )
        {
            return Err(fail());
        }
        let signature = if self.options.decompile_generics {
            class.signature()?.map(ClassSignature::parse).transpose()?
        } else {
            None
        };
        let (mut head, visible_args) = match &class.interfaces[..] {
            [] => {
                let (mut head, visible_args) = self.constructor_target(
                    super_owner,
                    super_descriptor,
                    &args[first..last],
                    None,
                )?;
                if let Some(signature) = &signature
                    && head.starts_with("new ")
                    && !head.contains(".new ")
                {
                    head = Document::from("new ");
                    self.append_generic_reference(&mut head, &signature.superclass);
                }
                (head, visible_args)
            }
            [interface] if super_owner == "java/lang/Object" && loads.is_empty() => {
                let mut head = Document::from("new ");
                if let Some(interface) = signature
                    .as_ref()
                    .and_then(|signature| signature.interfaces.first())
                {
                    self.append_generic_reference(&mut head, interface);
                } else {
                    head.append(self.class_reference(pool.class_name(*interface)?));
                }
                (head, &args[first..last])
            }
            _ => return Err(fail()),
        };
        let mut sites = sites.borrow_mut();
        let id = sites.len();
        sites.push(AnonymousSite {
            class: owner.into(),
            descriptor: descriptor.into(),
            instructions,
            initializer_start,
            captures: (!captures.fields.is_empty()).then(|| captures.fields.into()),
            enclosing_names: Some(self.locals.lexical_names()),
        });
        head.append_relative_arguments(visible_args.iter().map(|arg| &arg.text));
        let _ = write!(head, "\0{id}\0");
        Ok(Some((head, AnonymousOrigin::new(id + 1).expect("one-based site index"))))
    }

    fn append_generic_reference(&self, head: &mut Document, ty: &GenericType) {
        match ty {
            GenericType::Class(class) => {
                head.append(self.class_reference(&class.internal_name));
                self.append_generic_arguments(head, &class.arguments);
                let mut owner = class.internal_name.clone();
                for part in &class.nested {
                    owner.push('$');
                    owner.push_str(&part.name);
                    head.push('.');
                    self.append_class_reference(head, &part.name, &owner);
                    self.append_generic_arguments(head, &part.arguments);
                }
            }
            GenericType::Array {
                element,
                dimensions,
            } => {
                self.append_generic_reference(head, element);
                for _ in 0..*dimensions {
                    head.push_str("[]");
                }
            }
            _ => head.push_str(&ty.render(self.class_name)),
        }
    }

    fn append_generic_arguments(&self, head: &mut Document, arguments: &[TypeArgument]) {
        if arguments.is_empty() {
            return;
        }
        head.push('<');
        for (index, argument) in arguments.iter().enumerate() {
            if index != 0 {
                head.push_str(", ");
            }
            match argument {
                TypeArgument::Any => head.push('?'),
                TypeArgument::Exact(ty) => self.append_generic_reference(head, ty),
                TypeArgument::Extends(ty) => {
                    head.push_str("? extends ");
                    self.append_generic_reference(head, ty);
                }
                TypeArgument::Super(ty) => {
                    head.push_str("? super ");
                    self.append_generic_reference(head, ty);
                }
            }
        }
        head.push('>');
    }
}

struct ConstructorCaptures<'a, 'c> {
    owner: &'c str,
    class: &'c ClassFile<'a>,
    parameters: &'c [Type],
    args: &'c [Expr],
    enclosing: Option<&'c str>,
    fields: Vec<Capture>,
    enclosing_assigned: bool,
}

impl ConstructorCaptures<'_, '_> {
    fn skip_stores(
        &mut self,
        machine: &Machine<'_, '_>,
        instructions: &[Instruction],
    ) -> Result<usize, LiftError> {
        let mut offset = 0;
        while let Some(capture) = machine.anonymous_capture_store(
            self.owner,
            self.class,
            self.parameters,
            self.args,
            &instructions[offset..],
            self.enclosing,
        )? {
            if let Some(capture) = capture {
                if self.fields.iter().any(|field| field.same_field(&capture)) {
                    return Err(machine.unsupported("duplicate anonymous capture store"));
                }
                self.fields.push(capture);
            } else if std::mem::replace(&mut self.enclosing_assigned, true) {
                return Err(machine.unsupported("duplicate anonymous enclosing-instance store"));
            }
            offset += 3;
        }
        Ok(offset)
    }
}

fn constructor_parameters_are_used(
    instructions: &[Instruction],
    parameters: &[Type],
    implicit: usize,
    captures: &[Capture],
) -> bool {
    let mut slot = 1u16;
    for (index, ty) in parameters.iter().enumerate() {
        let recoverable =
            index < implicit || captures.iter().any(|capture| capture.parameter == index);
        if instructions.iter().any(|op| {
            writes_local(op, slot) || (!recoverable && parameter_load_slot(op, ty) == Some(slot))
        }) {
            return true;
        }
        let Some(next) = slot.checked_add(ty.slots()) else {
            return true;
        };
        slot = next;
    }
    false
}
