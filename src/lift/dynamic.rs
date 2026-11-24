// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{
    borrow::Cow,
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use crate::{
    bytecode::{Instruction, Operand, decode},
    cfg::ControlFlowGraph,
    classfile::{BootstrapMethod, ClassFile, Constant, ConstantPool, Member, find_attribute},
    classpath::ClassMetadata,
    descriptor::{
        ClassSignature, GenericType, MethodDescriptor, MethodSignature, Primitive, Type,
        TypeArgument,
    },
    emit::synthetic_marks::append_lambda_mark,
    source_text::Document,
    structure::structure_with_handlers,
};

use super::{
    Effect, LiftError, Machine,
    boxing::{unboxed, wrapper},
    expr::{Expr, PRIMARY, Source, UNARY},
};

const METAFACTORY: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
const ALT_METAFACTORY: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";
const CONSTANT_BOOTSTRAP_PREFIX: &str =
    "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/Class;";
const FLAG_SERIALIZABLE: i32 = 1;
const FLAG_MARKERS: i32 = 2;
const FLAG_BRIDGES: i32 = 4;
const STATIC: u16 = 0x0008;
const FINAL: u16 = 0x0010;
const BRIDGE: u16 = 0x0040;
const INTERFACE: u16 = 0x0200;
const ABSTRACT: u16 = 0x0400;
const SYNTHETIC: u16 = 0x1000;
const ENUM: u16 = 0x4000;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dispatch {
    Static,
    Virtual,
    Special,
    Constructor,
    Interface,
}

impl Dispatch {
    fn has_receiver(self) -> bool {
        matches!(self, Self::Virtual | Self::Special | Self::Interface)
    }
}

pub(super) struct LambdaSite<'a> {
    sam_name: &'a str,
    sam_descriptor: &'a str,
    sam: MethodDescriptor,
    instantiated: MethodDescriptor,
    dispatch: Dispatch,
    owner: &'a str,
    name: &'a str,
    implementation_descriptor: &'a str,
    implementation: MethodDescriptor,
    markers: Vec<&'a str>,
    bridges: Vec<&'a str>,
}

impl<'c> LambdaSite<'c> {
    pub(super) fn read(
        machine: &Machine<'_, 'c>,
        bootstrap_name: &str,
        bootstrap_descriptor: &str,
        sam_name: &'c str,
        method: &BootstrapMethod,
    ) -> Result<Self, LiftError> {
        let alternate = match (bootstrap_name, bootstrap_descriptor) {
            ("metafactory", METAFACTORY) => false,
            ("altMetafactory", ALT_METAFACTORY) => true,
            _ => {
                return Err(
                    machine.invalid_operand("invalid LambdaMetafactory bootstrap signature")
                );
            }
        };
        let &[sam_type, target, instantiated_type, ref arguments @ ..] =
            method.arguments.as_slice()
        else {
            return Err(machine.invalid_operand("missing LambdaMetafactory bootstrap arguments"));
        };
        let pool = &machine.class.pool;
        let sam_descriptor = method_type(machine, sam_type)?;
        let sam = MethodDescriptor::parse(sam_descriptor)?;
        let instantiated = MethodDescriptor::parse(method_type(machine, instantiated_type)?)?;
        if sam.parameters.len() != instantiated.parameters.len()
            || !sam
                .parameters
                .iter()
                .zip(&instantiated.parameters)
                .all(|(a, b)| same_sam_category(a, b))
            || !same_sam_category(&sam.return_type, &instantiated.return_type)
        {
            return Err(
                machine.invalid_operand("instantiated lambda type does not adapt the erased SAM")
            );
        }
        let Constant::MethodHandle {
            reference_kind,
            reference_index,
        } = *pool.get(target)?
        else {
            return Err(machine.invalid_operand("lambda implementation is not a method handle"));
        };
        let dispatch = match (reference_kind, pool.get(reference_index)?) {
            (5, Constant::Methodref { .. }) => Dispatch::Virtual,
            (6, Constant::Methodref { .. } | Constant::InterfaceMethodref { .. }) => {
                Dispatch::Static
            }
            (7, Constant::Methodref { .. } | Constant::InterfaceMethodref { .. }) => {
                Dispatch::Special
            }
            (8, Constant::Methodref { .. }) => Dispatch::Constructor,
            (9, Constant::InterfaceMethodref { .. }) => Dispatch::Interface,
            _ => {
                return Err(
                    machine.invalid_operand("lambda implementation is not an invocation handle")
                );
            }
        };
        let (owner, name, implementation_descriptor) = pool.member_ref(reference_index)?;
        let implementation = MethodDescriptor::parse(implementation_descriptor)?;
        if dispatch == Dispatch::Constructor {
            if name != "<init>"
                || implementation.return_type != Type::Void
                || owner.starts_with('[')
            {
                return Err(machine.invalid_operand("invalid lambda constructor handle"));
            }
        } else if !java_identifier(machine, name) {
            return Err(machine.unsupported("lambda implementation name is not a Java identifier"));
        }

        let mut arguments = arguments.iter().copied();
        let mut markers = Vec::new();
        let mut bridges = Vec::new();
        if alternate {
            let flags = bootstrap_integer(machine, arguments.next())?;
            if flags & !(FLAG_SERIALIZABLE | FLAG_MARKERS | FLAG_BRIDGES) != 0 {
                return Err(machine.unsupported("unknown altMetafactory bootstrap flags"));
            }
            if flags & FLAG_MARKERS != 0 {
                let count = bootstrap_count(machine, &mut arguments)?;
                for index in arguments.by_ref().take(count) {
                    let marker = pool.class_name(index)?;
                    if marker.starts_with('[') {
                        return Err(machine
                            .invalid_operand("altMetafactory marker is not an interface type"));
                    }
                    if !markers.contains(&marker) {
                        markers.push(marker);
                    }
                }
            }
            if flags & FLAG_SERIALIZABLE != 0 && !markers.contains(&"java/io/Serializable") {
                markers.push("java/io/Serializable");
            }
            if flags & FLAG_BRIDGES != 0 {
                let count = bootstrap_count(machine, &mut arguments)?;
                for index in arguments.by_ref().take(count) {
                    let descriptor = method_type(machine, index)?;
                    let bridge = MethodDescriptor::parse(descriptor)?;
                    if bridge.parameters.len() != sam.parameters.len() {
                        return Err(
                            machine.invalid_operand("altMetafactory bridge has the wrong arity")
                        );
                    }
                    bridges.push(descriptor);
                }
            }
        }
        if arguments.next().is_some() {
            return Err(machine.invalid_operand("extra LambdaMetafactory bootstrap arguments"));
        }
        Ok(Self {
            sam_name,
            sam_descriptor,
            sam,
            instantiated,
            dispatch,
            owner,
            name,
            implementation_descriptor,
            implementation,
            markers,
            bridges,
        })
    }
}

fn same_sam_category(erased: &Type, instantiated: &Type) -> bool {
    erased == instantiated || is_reference(erased) && is_reference(instantiated)
}

fn method_type<'c>(machine: &Machine<'_, 'c>, index: u16) -> Result<&'c str, LiftError> {
    let pool = &machine.class.pool;
    let Constant::MethodType(descriptor) = *pool.get(index)? else {
        return Err(machine.invalid_operand("lambda bootstrap argument is not a method type"));
    };
    Ok(pool.utf8(descriptor)?)
}

fn bootstrap_integer(machine: &Machine<'_, '_>, index: Option<u16>) -> Result<i32, LiftError> {
    let index =
        index.ok_or_else(|| machine.invalid_operand("missing altMetafactory integer argument"))?;
    let Constant::Integer(value) = *machine.class.pool.get(index)? else {
        return Err(machine.invalid_operand("altMetafactory argument is not an integer"));
    };
    Ok(value)
}

fn bootstrap_count(
    machine: &Machine<'_, '_>,
    arguments: &mut impl ExactSizeIterator<Item = u16>,
) -> Result<usize, LiftError> {
    usize::try_from(bootstrap_integer(machine, arguments.next())?)
        .ok()
        .filter(|&count| count <= arguments.len())
        .ok_or_else(|| machine.invalid_operand("altMetafactory argument count is out of range"))
}

impl<'a, 'c> Machine<'a, 'c> {
    pub(super) fn lower_lambda(
        &mut self,
        site: LambdaSite<'c>,
        factory: MethodDescriptor,
    ) -> Result<Effect, LiftError> {
        let Type::Object(interface) = &factory.return_type else {
            return Err(self.invalid_operand("lambda factory must return an interface"));
        };
        let instance = site.dispatch.has_receiver();
        let capture_count = factory.parameters.len();
        let sam_count = site.instantiated.parameters.len();
        if capture_count + sam_count != site.implementation.parameters.len() + usize::from(instance)
        {
            return Err(
                self.invalid_operand("lambda implementation arity does not match its arguments")
            );
        }
        if instance
            && !is_reference(if capture_count == 0 {
                &site.instantiated.parameters[0]
            } else {
                &factory.parameters[0]
            })
        {
            return Err(self.invalid_operand("lambda receiver is not a reference"));
        }
        let bound = instance && capture_count != 0;
        let captured_parameters = capture_count - usize::from(bound);
        if factory.parameters[usize::from(bound)..]
            != site.implementation.parameters[..captured_parameters]
        {
            return Err(
                self.invalid_operand("lambda capture types do not match implementation parameters")
            );
        }
        let instantiated = &site.instantiated.parameters[usize::from(instance && !bound)..];
        let implementation = &site.implementation.parameters[captured_parameters..];
        let instantiated_return = &site.instantiated.return_type;
        let implementation_return = if site.dispatch == Dispatch::Constructor {
            Type::Object(site.owner.into())
        } else {
            site.implementation.return_type.clone()
        };
        if *instantiated_return != Type::Void && implementation_return == Type::Void {
            return Err(
                self.invalid_operand("void lambda implementation has a value-returning SAM")
            );
        }
        let target = self.lambda_target(interface, &site)?;
        let helper = (site.owner == self.owner)
            .then(|| self.synthetic_method(site.name, site.implementation_descriptor))
            .flatten();
        let mut captures = self.arguments(&factory, None)?;
        let super_qualifier = if site.dispatch == Dispatch::Special {
            self.lambda_special_qualifier(&site, captures.first())?
        } else {
            None
        };

        // A capture-free static/constructor reference or a bound reference is
        // representable directly only if javac will select the linked overload.
        // When the adaptation changes a parameter type, name the exact overload
        // in an adapter with ordinary calls and explicit conversions instead.
        let direct = helper.is_none()
            && capture_count == usize::from(bound)
            && instantiated == implementation
            && self.direct_lambda_return(&implementation_return, instantiated_return)
            && !self.competing_reference_overload(&site, bound)
            && !(site.dispatch == Dispatch::Constructor
                && self.group.is_some_and(|group| {
                    group
                        .constructor_outer(site.owner, site.implementation_descriptor)
                        .is_some()
                }));
        let expression = if direct {
            let qualifier = if let Some(qualifier) = super_qualifier {
                qualifier
            } else if bound {
                self.member_receiver(captures[0].clone(), site.owner, false)?
                    .into_at(PRIMARY)
            } else {
                self.type_reference(&reference_type(site.owner)?)
            };
            let name = if site.dispatch == Dispatch::Constructor {
                Cow::Borrowed("new")
            } else {
                self.source_invocation_name(site.owner, site.name, site.implementation_descriptor)
            };
            let mut text = lambda_cast(&target);
            text.append(qualifier);
            text.push_str("::");
            self.append_method_reference(
                &mut text,
                &name,
                site.owner,
                site.name,
                site.implementation_descriptor,
            );
            self.expression(factory.return_type, text, UNARY, &captures, true)?
        } else {
            // The factory captures values, not expressions. Freeze in the JVM
            // order before the adapter can defer their use to SAM invocation.
            self.keep_final_captures(&mut captures);
            self.freeze_values(&mut captures)?;
            if let Some(helper) = helper
                && instantiated == implementation
                && instantiated_return == &implementation_return
                && let Some(text) = self.inline_lambda(helper, &site, &captures, &target)?
            {
                let expression =
                    self.expression(factory.return_type, text, UNARY, &captures, true)?;
                self.push(expression)?;
                return Ok(Effect::None);
            }
            if bound && !matches!(captures[0].source, Source::This) {
                self.before_statement(None)?;
                let owner = "java/util/Objects";
                let mut statement = self.class_reference(owner);
                statement.push('.');
                self.append_method_reference(
                    &mut statement,
                    "requireNonNull",
                    owner,
                    "requireNonNull",
                    "(Ljava/lang/Object;)Ljava/lang/Object;",
                );
                statement.append_relative_arguments([&captures[0].text]);
                statement.push(';');
                self.prelude.push(statement);
            }
            let parameters: Vec<_> = (0..sam_count)
                .map(|index| self.locals.lambda_parameter(index))
                .collect();
            let receiver = if instance && super_qualifier.is_none() {
                let value = if bound {
                    captures[0].clone()
                } else {
                    Expr::atom(
                        site.instantiated.parameters[0].clone(),
                        parameters[0].clone().into(),
                    )
                };
                Some(
                    self.member_receiver(value, site.owner, false)?
                        .into_at(PRIMARY),
                )
            } else {
                None
            };
            let mut arguments = Vec::with_capacity(site.implementation.parameters.len());
            for capture in &captures[usize::from(bound)..] {
                arguments.push(capture.clone());
            }
            for ((parameter, from), to) in parameters[usize::from(instance && !bound)..]
                .iter()
                .zip(instantiated)
                .zip(implementation)
            {
                arguments.push(Expr::atom(
                    to.clone(),
                    self.lambda_conversion(Document::from(parameter.as_str()), from, to)?,
                ));
            }
            let source_name =
                self.source_invocation_name(site.owner, site.name, site.implementation_descriptor);
            let call = match site.dispatch {
                Dispatch::Constructor => {
                    let (mut target, visible_arguments) = self.constructor_target(
                        site.owner,
                        site.implementation_descriptor,
                        &arguments,
                        None,
                    )?;
                    target.append_relative_arguments(visible_arguments.iter().map(|arg| &arg.text));
                    target
                }
                Dispatch::Static => {
                    let mut call = self.class_reference(site.owner);
                    call.push('.');
                    self.append_method_reference(
                        &mut call,
                        &source_name,
                        site.owner,
                        site.name,
                        site.implementation_descriptor,
                    );
                    call.append_relative_arguments(arguments.iter().map(|arg| &arg.text));
                    call
                }
                _ => {
                    let mut call = super_qualifier.or(receiver).expect("instance receiver");
                    call.push('.');
                    self.append_method_reference(
                        &mut call,
                        &source_name,
                        site.owner,
                        site.name,
                        site.implementation_descriptor,
                    );
                    call.append_relative_arguments(arguments.iter().map(|arg| &arg.text));
                    call
                }
            };
            let body = if *instantiated_return == Type::Void {
                call
            } else {
                self.lambda_conversion(call, &implementation_return, instantiated_return)?
            };
            let expression = self.expression(
                factory.return_type,
                render_lambda(
                    lambda_cast(&target),
                    parameters.into_iter().map(Document::from).collect(),
                    body,
                ),
                UNARY,
                &captures,
                true,
            )?;
            if let Some(helper) = helper {
                self.note_synthetic_method(helper);
            }
            expression
        };
        self.push(expression)?;
        Ok(Effect::None)
    }

    fn keep_final_captures(&self, captures: &mut [Expr]) {
        if !captures
            .iter()
            .any(|capture| self.locals.capture_slot(capture).is_some())
        {
            return;
        }
        let Ok(instructions) = decode(self.code.bytes) else {
            return;
        };
        for capture in captures {
            let Some((slot, parameter)) = self.locals.capture_slot(capture) else {
                continue;
            };
            let writes = instructions
                .iter()
                .filter(|op| stored_slot(op) == Some(slot));
            if writes.take(2).count() <= usize::from(!parameter) {
                // An effectively final local already denotes the exact value
                // captured at this site and needs no additional temporary.
                capture.order = None;
            }
        }
    }

    pub(super) fn record_synthetic_invocation(&self, owner: &str, name: &str, descriptor: &str) {
        if self.dynamic_helpers.is_some()
            && owner == self.owner
            && let Some(helper) = self.synthetic_method(name, descriptor)
        {
            self.note_synthetic_method(helper);
        }
    }

    pub(super) fn source_invocation_name<'n>(
        &'n self,
        owner: &str,
        name: &'n str,
        descriptor: &str,
    ) -> Cow<'n, str> {
        if let Some(renames) = self.renames {
            let effective = renames.method_name(owner, name, descriptor);
            if effective != name {
                return Cow::Borrowed(effective);
            }
        }
        if name.starts_with("lambda$")
            && let Some(class) = self.dynamic_class(owner)
        {
            source_method_name(class, name, descriptor)
        } else {
            Cow::Borrowed(name)
        }
    }

    fn synthetic_method(&self, name: &str, descriptor: &str) -> Option<&'c Member<'a>> {
        synthetic_method(self.class, name, descriptor)
    }

    fn note_synthetic_method(&self, helper: &Member<'_>) {
        if let Some(helpers) = &self.dynamic_helpers {
            helpers
                .borrow_mut()
                .insert((helper.name_index, helper.descriptor_index));
        }
    }

    fn inline_lambda(
        &self,
        helper: &'c Member<'a>,
        site: &LambdaSite<'_>,
        captures: &[Expr],
        target: &Document,
    ) -> Result<Option<Document>, LiftError> {
        // Multiple indy instructions can reference the same helper, including
        // recursively in hand-written bytecode; bound source expansion.
        if self.lambda_depth >= 8 || site.name == self.method_name {
            return Ok(None);
        }
        let is_static = site.dispatch == Dispatch::Static;
        if (helper.access_flags & STATIC != 0) != is_static
            || (!is_static
                && !captures
                    .first()
                    .is_some_and(|value| matches!(value.source, Source::This)))
        {
            return Ok(None);
        }
        let captured = &captures[usize::from(!is_static)..];
        let captured_slots = site.implementation.parameters[..captured.len()]
            .iter()
            .map(Type::slots)
            .sum::<u16>()
            + u16::from(!is_static);
        if captured
            .iter()
            .any(|capture| capture.text != "this" && !java_identifier(self, &capture.text))
        {
            return Ok(None);
        }
        let Some(code) = helper.code(&self.class.pool)? else {
            return Ok(None);
        };
        let Ok(instructions) = decode(code.bytes) else {
            return Ok(None);
        };
        if instructions
            .iter()
            .any(|instruction| stored_slot(instruction).is_some_and(|slot| slot < captured_slots))
        {
            return Ok(None);
        }
        let Ok(graph) = ControlFlowGraph::build(&instructions, &code.exceptions) else {
            return Ok(None);
        };
        let mut machine = Machine::new(
            self.class,
            helper,
            &code,
            &site.implementation,
            self.options,
            self.class_name,
        )?;
        machine.renames = self.renames;
        machine.group = self.group;
        machine
            .anonymous_bindings
            .clone_from(&self.anonymous_bindings);
        machine.bootstrap.clone_from(&self.bootstrap);
        // Bound the amount of source copied by each helper tree, not only
        // its call depth (a helper can contain many nested factories).
        let nested_sites = instructions.iter().filter(|op| op.opcode == 0xba).count();
        let nesting_cost = (usize::BITS - nested_sites.leading_zeros()).max(1) as u8;
        machine.lambda_depth = self.lambda_depth + nesting_cost;
        let local_helpers = self
            .dynamic_helpers
            .as_ref()
            .map(|_| super::DynamicHelpers::default());
        machine.dynamic_helpers.clone_from(&local_helpers);
        let captures = captured
            .iter()
            .map(|capture| capture.text.as_str())
            .collect::<Vec<_>>();
        machine
            .locals
            .bind_lambda_scope(&self.locals, &captures, &site.implementation, is_static);
        let mut parameters =
            Vec::with_capacity(site.implementation.parameters.len() - captured.len());
        let mut slot = u16::from(!is_static);
        for (index, ty) in site.implementation.parameters.iter().enumerate() {
            if let Some(capture) = captured.get(index) {
                if self.options.dump_text_tokens {
                    if let Source::Local(outer_slot) = capture.source
                        && self
                            .local_capture_binding(outer_slot, &capture.text)
                            .is_some()
                    {
                        machine.inherit_lambda_capture_token(slot, self, outer_slot);
                    } else {
                        machine.omit_lambda_capture_token(slot);
                    }
                }
            } else {
                let parameter = machine
                    .local_document(slot, true)
                    .unwrap_or_else(|| Document::from(machine.parameter_names()[index].as_str()));
                parameters.push(parameter);
            }
            slot += ty.slots();
        }
        let Ok(mut lines) =
            structure_with_handlers(&instructions, &graph, machine, &code.exceptions)
        else {
            return Ok(None);
        };
        if let (Some(outer), Some(retained)) = (&self.dynamic_helpers, local_helpers) {
            outer.borrow_mut().append(&mut retained.borrow_mut());
        }
        if site.implementation.return_type == Type::Void
            && lines
                .last()
                .is_some_and(|line| line.depth == 0 && line.text == "return;")
        {
            lines.pop();
        }
        let mut prefix = lambda_cast(target);
        append_lambda_mark(
            &mut prefix,
            self.options,
            site.owner,
            site.name,
            site.implementation_descriptor,
        );
        if let [line] = lines.as_slice()
            && line.depth == 0
            && line.text.ends_with(';')
        {
            let mut statement = line.text.clone();
            statement.pop();
            if statement.starts_with("return ") {
                statement.replace_literal_prefix("return ".len(), "");
                // javac lowers an array constructor reference to a synthetic
                // method whose only action is to create an array of the passed
                // length. Matching this behavior also permits the equivalent
                // source lambda `length -> new T[length]`.
                if captures.is_empty()
                    && is_static
                    && let [parameter] = parameters.as_slice()
                    && site.implementation.parameters.as_slice() == [super::expr::INT]
                    && matches!(site.implementation.return_type, Type::Array(_))
                {
                    let array = self.render_type(&site.implementation.return_type);
                    let creation = array.replacen("[]", &format!("[{parameter}]"), 1);
                    if statement.strip_prefix("new ") == Some(creation.as_str()) {
                        prefix.append(self.type_reference(&site.implementation.return_type));
                        prefix.push_str("::new");
                        return Ok(Some(prefix));
                    }
                }
                return Ok(Some(render_lambda(prefix, parameters, statement)));
            }
            if site.implementation.return_type == Type::Void
                && instructions
                    .iter()
                    .rev()
                    .find(|code| !matches!(code.opcode, 0x00 | 0xb1))
                    .is_some_and(
                        |code| matches!(code.opcode, 0xb3 | 0xb5..=0xb9 | 0x4f..=0x56 | 0x84),
                    )
            {
                return Ok(Some(render_lambda(prefix, parameters, statement)));
            }
        }
        let mut body = Document::from("{");
        for mut line in lines {
            let depth = line.depth + 1;
            body.hard_line(depth);
            line.text.offset_relative_depth(depth);
            body.append(line.text);
        }
        body.hard_line(0);
        body.push('}');
        Ok(Some(render_lambda(prefix, parameters, body)))
    }

    fn lambda_special_qualifier(
        &self,
        site: &LambdaSite<'_>,
        receiver: Option<&Expr>,
    ) -> Result<Option<Document>, LiftError> {
        if site.owner == self.owner
            && self.own_method_is_private(site.name, site.implementation_descriptor)?
        {
            return Ok(None);
        }
        if !receiver.is_some_and(|receiver| matches!(receiver.source, Source::This)) {
            return Err(
                self.unsupported("nonvirtual lambda invocation without a lexical super receiver")
            );
        }
        if self.super_class == Some(site.owner) {
            return Ok(Some("super".into()));
        }
        if self.class.interfaces.iter().any(|&index| {
            self.class
                .pool
                .class_name(index)
                .is_ok_and(|name| name == site.owner)
        }) {
            let mut qualifier = self.class_reference(site.owner);
            qualifier.push_str(".super");
            return Ok(Some(qualifier));
        }
        Err(self.unsupported("lambda invokespecial target is not a direct supertype"))
    }

    fn direct_lambda_return(&self, from: &Type, to: &Type) -> bool {
        if from == to || *to == Type::Void {
            return true;
        }
        match (from, to) {
            (Type::Primitive(from), Type::Primitive(to)) => primitive_widens(*from, *to),
            (Type::Primitive(from), Type::Object(to)) => to == wrapper(*from).0,
            (Type::Object(from), Type::Primitive(to)) => {
                unboxed(from).is_some_and(|p| primitive_widens(p, *to))
            }
            _ => self.known_assignable(from, to),
        }
    }

    fn lambda_conversion(
        &self,
        mut expression: Document,
        from: &Type,
        to: &Type,
    ) -> Result<Document, LiftError> {
        if from == to {
            return Ok(expression);
        }
        let target = self.render_type(to);
        match (from, to) {
            (Type::Primitive(from), Type::Primitive(to)) if primitive_widens(*from, *to) => {
                expression.surround(&format!("({target})("), ")");
                Ok(expression)
            }
            (Type::Primitive(from), to) if is_reference(to) => {
                if let Type::Object(name) = to
                    && let Some(primitive) = unboxed(name)
                {
                    if !primitive_widens(*from, primitive) {
                        return Err(self.invalid_operand("invalid lambda box conversion"));
                    }
                    if *from != primitive {
                        expression.surround(&format!("({})(", primitive.java_name()), ")");
                    }
                    let mut call = Document::from(format!("{target}.valueOf"));
                    call.append(Document::relative_delimited([expression]));
                    return Ok(call);
                }
                let boxed = (self.class_name)(wrapper(*from).0);
                let mut call = Document::from(format!("({target}){boxed}.valueOf"));
                call.append(Document::relative_delimited([expression]));
                Ok(call)
            }
            (Type::Object(from), Type::Primitive(to)) => {
                let Some(primitive) = unboxed(from) else {
                    let (boxed, accessor) = wrapper(*to);
                    let owner = if matches!(to, Primitive::Boolean | Primitive::Char) {
                        boxed
                    } else {
                        "java/lang/Number"
                    };
                    expression.surround("(", ")");
                    let converted = self.reference_cast(
                        Expr::atom(Type::Object(from.clone()), expression),
                        Type::Object(owner.into()),
                        true,
                    )?;
                    let mut value = converted.into_at(PRIMARY);
                    value.push_str(&format!(".{accessor}()"));
                    return Ok(value);
                };
                if !primitive_widens(primitive, *to) {
                    return Err(self.invalid_operand("invalid lambda unboxing conversion"));
                }
                let (_, accessor) = wrapper(primitive);
                expression.surround("(", &format!(").{accessor}()"));
                if primitive != *to {
                    expression.prepend_str(&format!("({target})"));
                }
                Ok(expression)
            }
            (from, to) if is_reference(from) && is_reference(to) => {
                expression.surround("(", ")");
                let result =
                    self.reference_cast(Expr::atom(from.clone(), expression), to.clone(), true)?;
                Ok(result.text)
            }
            _ => Err(self.invalid_operand("invalid lambda implementation conversion")),
        }
    }
}

enum SiteClass<'a, 'c> {
    Input(&'c ClassFile<'a>),
    Library(Arc<ClassMetadata>),
}

impl SiteClass<'_, '_> {
    fn flags(&self) -> u16 {
        match self {
            Self::Input(class) => class.access_flags,
            Self::Library(class) => class.access_flags,
        }
    }

    fn signature(&self) -> Result<Option<&str>, LiftError> {
        match self {
            Self::Input(class) => Ok(class.signature()?),
            Self::Library(class) => Ok(class.signature.as_deref()),
        }
    }

    fn interfaces(&self) -> impl Iterator<Item = &str> {
        let (input, library) = match self {
            Self::Input(class) => (Some(*class), None),
            Self::Library(class) => (None, Some(class.as_ref())),
        };
        input
            .into_iter()
            .flat_map(|class| {
                class
                    .interfaces
                    .iter()
                    .filter_map(move |&index| class.pool.class_name(index).ok())
            })
            .chain(
                library
                    .into_iter()
                    .flat_map(|class| class.interfaces.iter().map(String::as_str)),
            )
    }

    fn superclass(&self) -> Option<&str> {
        match self {
            Self::Input(class) => class.pool.class_name(class.super_class).ok(),
            Self::Library(class) => class.super_name.as_deref(),
        }
    }

    fn any_method(&self, mut predicate: impl FnMut(&str, &str, u16) -> bool) -> bool {
        match self {
            Self::Input(class) => {
                let pool = &class.pool;
                class.methods.iter().any(|method| {
                    matches!((pool.utf8(method.name_index), pool.utf8(method.descriptor_index)),
                        (Ok(name), Ok(descriptor)) if predicate(name, descriptor, method.access_flags))
                })
            }
            Self::Library(class) => class
                .methods
                .iter()
                .any(|method| predicate(&method.name, &method.descriptor, method.access_flags)),
        }
    }

    fn sam_signature(&self, site: &LambdaSite<'_>) -> Result<Option<Option<&str>>, LiftError> {
        match self {
            Self::Input(class) => {
                let pool = &class.pool;
                for method in &class.methods {
                    if method.access_flags & (ABSTRACT | STATIC) == ABSTRACT
                        && pool.utf8(method.name_index)? == site.sam_name
                        && pool.utf8(method.descriptor_index)? == site.sam_descriptor
                    {
                        return Ok(Some(method.signature(pool)?));
                    }
                }
                Ok(None)
            }
            Self::Library(class) => Ok(class
                .methods
                .iter()
                .find(|method| {
                    method.access_flags & (ABSTRACT | STATIC) == ABSTRACT
                        && method.name == site.sam_name
                        && method.descriptor == site.sam_descriptor
                })
                .map(|method| method.signature.as_deref())),
        }
    }
}

impl<'a, 'c> Machine<'a, 'c> {
    fn dynamic_class(&self, name: &str) -> Option<&'c ClassFile<'a>> {
        if name == self.owner {
            Some(self.class)
        } else {
            self.group.and_then(|group| group.get(name))
        }
    }

    fn lookup_site_class(&self, name: &str) -> Option<SiteClass<'a, 'c>> {
        self.dynamic_class(name).map(SiteClass::Input).or_else(|| {
            [
                self.options.library_classpath.as_deref(),
                self.options.runtime_classpath.as_deref(),
            ]
            .into_iter()
            .flatten()
            .find_map(|path| path.metadata(name).ok().flatten().map(SiteClass::Library))
        })
    }

    fn lambda_target(&self, interface: &str, site: &LambdaSite<'_>) -> Result<Document, LiftError> {
        let mut target = self.class_reference(interface);
        let types = if let Some(class) = self.lookup_site_class(interface) {
            if class.flags() & INTERFACE == 0 {
                return Err(self.invalid_operand("lambda factory does not return an interface"));
            }
            self.interface_type_arguments(&class, site)?
        } else {
            jdk_type_arguments(interface, site)
        };
        if let Some(types) = types {
            if !types.is_empty() {
                target.push('<');
                let mut separator = "";
                for ty in types {
                    target.push_str(separator);
                    target.append(self.type_reference(&ty));
                    separator = ", ";
                }
                target.push('>');
            }
        } else if site.sam != site.instantiated {
            return Err(
                self.unsupported("missing generic signature for the specialized lambda SAM")
            );
        }
        for &marker in &site.markers {
            if marker == interface {
                continue;
            }
            if self
                .lookup_site_class(marker)
                .is_some_and(|class| class.flags() & INTERFACE == 0)
            {
                return Err(self.invalid_operand("altMetafactory marker is not an interface"));
            }
            if self.any_member(marker, |class_flags, name, descriptor, flags| {
                class_flags & INTERFACE != 0
                    && flags & (STATIC | ABSTRACT) == ABSTRACT
                    && name != site.sam_name
                    && !matches!(
                        (name, descriptor),
                        ("equals", "(Ljava/lang/Object;)Z")
                            | ("hashCode", "()I")
                            | ("toString", "()Ljava/lang/String;")
                    )
            }) {
                return Err(self
                    .unsupported("altMetafactory intersection does not have a single source SAM"));
            }
            target.push_str(" & ");
            target.append(self.class_reference(marker));
        }
        for &bridge in &site.bridges {
            if bridge != site.sam_descriptor
                && !self.has_interface_method(interface, site.sam_name, bridge)
                && !site
                    .markers
                    .iter()
                    .any(|marker| self.has_interface_method(marker, site.sam_name, bridge))
            {
                return Err(self.unsupported(
                    "altMetafactory bridge is not declared by its source interfaces",
                ));
            }
        }
        Ok(target)
    }

    fn has_interface_method(&self, start: &str, name: &str, descriptor: &str) -> bool {
        self.any_member(
            start,
            |class_flags, method_name, method_descriptor, flags| {
                class_flags & INTERFACE != 0
                    && flags & STATIC == 0
                    && method_name == name
                    && method_descriptor == descriptor
            },
        )
    }

    fn competing_reference_overload(&self, site: &LambdaSite<'_>, bound: bool) -> bool {
        // A reference of the form Type::method searches both static and
        // receiver-first overloads. Do not let Java choose between the two
        // searches when a class hierarchy is available to inspect.
        if bound || site.dispatch == Dispatch::Constructor {
            return false;
        }
        let static_handle = site.dispatch == Dispatch::Static;
        let arity = site.instantiated.parameters.len();
        self.any_member(site.owner, |_, name, descriptor, flags| {
            name == site.name
                && flags & BRIDGE == 0
                && (flags & STATIC != 0) != static_handle
                && MethodDescriptor::parse(descriptor).is_ok_and(|descriptor| {
                    descriptor.parameters.len() + usize::from(static_handle) == arity
                })
        })
    }

    fn any_member(
        &self,
        start: &str,
        mut predicate: impl FnMut(u16, &str, &str, u16) -> bool,
    ) -> bool {
        fn visit(
            machine: &Machine<'_, '_>,
            owner: &str,
            predicate: &mut impl FnMut(u16, &str, &str, u16) -> bool,
            visited: &mut HashSet<String>,
            depth: u8,
        ) -> bool {
            if depth == 32 || !visited.insert(owner.into()) {
                return false;
            }
            let Some(class) = machine.lookup_site_class(owner) else {
                return false;
            };
            let found = class.any_method(|name, descriptor, flags| {
                predicate(class.flags(), name, descriptor, flags)
            }) || class
                .interfaces()
                .chain(class.superclass())
                .any(|parent| visit(machine, parent, predicate, visited, depth + 1));
            found
        }
        visit(self, start, &mut predicate, &mut HashSet::new(), 0)
    }

    fn interface_type_arguments(
        &self,
        class: &SiteClass<'_, '_>,
        site: &LambdaSite<'_>,
    ) -> Result<Option<Vec<Type>>, LiftError> {
        let Some(signature) = class.signature()?.map(ClassSignature::parse).transpose()? else {
            if site.sam == site.instantiated {
                return Ok(Some(Vec::new()));
            }
            // A non-generic interface can specialize an inherited method.
            let mut inferred = BTreeMap::new();
            return Ok(self
                .infer_interface_sam(
                    class,
                    None,
                    &BTreeMap::new(),
                    site,
                    &mut inferred,
                    &mut HashSet::new(),
                    0,
                )?
                .then(Vec::new));
        };
        let mut inferred = BTreeMap::new();
        if !self.infer_interface_sam(
            class,
            Some(&signature),
            &BTreeMap::new(),
            site,
            &mut inferred,
            &mut HashSet::new(),
            0,
        )? {
            return Ok(None);
        }
        Ok(signature
            .type_parameters
            .iter()
            .map(|formal| {
                if let Some(ty) = inferred.remove(formal.name.as_str()) {
                    Some(ty)
                } else if formal.interface_bounds.is_empty()
                    && formal
                        .class_bound
                        .as_ref()
                        .is_none_or(GenericType::is_java_lang_object)
                {
                    Some(super::object_type())
                } else {
                    None
                }
            })
            .collect())
    }

    fn infer_interface_sam(
        &self,
        class: &SiteClass<'_, '_>,
        signature: Option<&ClassSignature>,
        assignments: &BTreeMap<String, GenericType>,
        site: &LambdaSite<'_>,
        inferred: &mut BTreeMap<String, Type>,
        visited: &mut HashSet<String>,
        depth: u8,
    ) -> Result<bool, LiftError> {
        if depth == 32 {
            return Ok(false);
        }
        if let Some(signature) = class.sam_signature(site)? {
            let Some(method) = signature.map(MethodSignature::parse).transpose()? else {
                return Ok(site.sam == site.instantiated);
            };
            if !method.type_parameters.is_empty()
                || method.parameters.len() != site.instantiated.parameters.len()
            {
                return Ok(false);
            }
            return Ok(method
                .parameters
                .iter()
                .chain([&method.return_type])
                .zip(
                    site.instantiated
                        .parameters
                        .iter()
                        .chain([&site.instantiated.return_type]),
                )
                .all(|(generic, instantiated)| {
                    bind_sam_type(
                        &substitute_sam_type(generic, assignments),
                        instantiated,
                        inferred,
                    )
                }));
        }
        for parent_name in class.interfaces() {
            if !visited.insert(parent_name.into()) {
                continue;
            }
            let parent_arguments = signature.and_then(|signature| {
                signature.interfaces.iter().find_map(|ty| match ty {
                    GenericType::Class(class) if class.binary_name() == parent_name => {
                        Some(&class.arguments)
                    }
                    _ => None,
                })
            });
            let Some(parent) = self.lookup_site_class(parent_name) else {
                if let (Some(formals), Some(types)) =
                    (parent_arguments, jdk_type_arguments(parent_name, site))
                    && formals.len() == types.len()
                {
                    let mut possible = inferred.clone();
                    if formals.iter().zip(&types).all(|(formal, concrete)| {
                        matches!(formal, TypeArgument::Exact(formal) if bind_sam_type(&substitute_sam_type(formal, assignments), concrete, &mut possible))
                    }) {
                        *inferred = possible;
                        return Ok(true);
                    }
                }
                continue;
            };
            let parent_signature = parent.signature()?.map(ClassSignature::parse).transpose()?;
            let mut parent_assignments = BTreeMap::new();
            if let (Some(parent_signature), Some(parent_arguments)) =
                (&parent_signature, parent_arguments)
            {
                for (formal, actual) in parent_signature
                    .type_parameters
                    .iter()
                    .zip(parent_arguments)
                {
                    let TypeArgument::Exact(actual) = actual else {
                        return Ok(false);
                    };
                    parent_assignments.insert(
                        formal.name.clone(),
                        substitute_sam_type(actual, assignments),
                    );
                }
            }
            let mut possible = inferred.clone();
            if self.infer_interface_sam(
                &parent,
                parent_signature.as_ref(),
                &parent_assignments,
                site,
                &mut possible,
                visited,
                depth + 1,
            )? {
                *inferred = possible;
                return Ok(true);
            }
        }
        Ok(false)
    }
}

fn reference_type(name: &str) -> Result<Type, LiftError> {
    Ok(if name.starts_with('[') {
        Type::parse(name)?
    } else {
        Type::Object(name.into())
    })
}

fn substitute_sam_type(
    ty: &GenericType,
    assignments: &BTreeMap<String, GenericType>,
) -> GenericType {
    match ty {
        GenericType::Variable(name) => assignments.get(name).unwrap_or(ty).clone(),
        GenericType::Array {
            element,
            dimensions,
        } => GenericType::Array {
            element: Box::new(substitute_sam_type(element, assignments)),
            dimensions: *dimensions,
        },
        _ => ty.clone(),
    }
}

fn bind_sam_type(
    generic: &GenericType,
    instantiated: &Type,
    inferred: &mut BTreeMap<String, Type>,
) -> bool {
    match generic {
        GenericType::Variable(name) if is_reference(instantiated) => {
            if let Some(existing) = inferred.get(name) {
                existing == instantiated
            } else {
                inferred.insert(name.clone(), instantiated.clone());
                true
            }
        }
        GenericType::Class(class) => {
            matches!(instantiated, Type::Object(name) if class.binary_name() == name.as_str())
        }
        GenericType::Primitive(primitive) => *instantiated == Type::Primitive(*primitive),
        GenericType::Void => *instantiated == Type::Void,
        GenericType::Array {
            element,
            dimensions,
        } => {
            let mut component = instantiated;
            for _ in 0..*dimensions {
                let Type::Array(next) = component else {
                    return false;
                };
                component = next;
            }
            bind_sam_type(element, component, inferred)
        }
        GenericType::Variable(_) => false,
    }
}

// Standard SAMs when a JDK is not on the input classpath. The bootstrap
// supplies reified parameter/return erasures, but not formal parameter names
// or their order in the functional interface's declaration.
fn jdk_type_arguments(interface: &str, site: &LambdaSite<'_>) -> Option<Vec<Type>> {
    let args = &site.instantiated.parameters;
    let result = &site.instantiated.return_type;
    let same = |indices: &[Type]| indices.windows(2).all(|pair| pair[0] == pair[1]);
    let types = match interface {
        "java/util/concurrent/Callable"
        | "java/security/PrivilegedAction"
        | "java/security/PrivilegedExceptionAction" => vec![result],
        "java/util/Comparator" if args.len() == 2 && same(args) => vec![&args[0]],
        _ => match (
            interface.strip_prefix("java/util/function/")?,
            args.as_slice(),
        ) {
            ("Supplier" | "IntFunction" | "LongFunction" | "DoubleFunction", _) => vec![result],
            (
                "Consumer" | "Predicate" | "ToIntFunction" | "ToLongFunction" | "ToDoubleFunction"
                | "ObjIntConsumer" | "ObjLongConsumer" | "ObjDoubleConsumer",
                [first, ..],
            ) => vec![first],
            ("Function", [first]) => vec![first, result],
            ("UnaryOperator", [first]) if first == result => vec![first],
            ("BiFunction", [first, second]) => vec![first, second, result],
            (
                "BiConsumer" | "BiPredicate" | "ToIntBiFunction" | "ToLongBiFunction"
                | "ToDoubleBiFunction",
                [first, second],
            ) => vec![first, second],
            ("BinaryOperator", [first, second]) if first == second && first == result => {
                vec![first]
            }
            _ => return None,
        },
    };
    types
        .into_iter()
        .map(|ty| is_reference(ty).then(|| ty.clone()))
        .collect()
}

fn lambda_cast(target: &Document) -> Document {
    let mut cast = target.clone();
    cast.surround("(", ")");
    cast
}

fn render_lambda(mut declaration: Document, parameters: Vec<Document>, body: Document) -> Document {
    let parenthesized = parameters.len() != 1;
    if parenthesized {
        declaration.push('(');
    }
    for (index, parameter) in parameters.into_iter().enumerate() {
        if index != 0 {
            declaration.push_str(", ");
        }
        declaration.append(parameter);
    }
    if parenthesized {
        declaration.push(')');
    }
    declaration.push_str(" -> ");
    declaration.append(body);
    declaration
}

fn is_reference(ty: &Type) -> bool {
    matches!(ty, Type::Object(_) | Type::Array(_))
}

fn primitive_widens(from: Primitive, to: Primitive) -> bool {
    use Primitive::*;
    from == to
        || match from {
            Byte => matches!(to, Short | Int | Long | Float | Double),
            Short | Char => matches!(to, Int | Long | Float | Double),
            Int => matches!(to, Long | Float | Double),
            Long => matches!(to, Float | Double),
            Float => to == Double,
            Boolean | Double => false,
        }
}

fn is_synthetic(pool: &ConstantPool<'_>, member: &Member<'_>) -> bool {
    member.access_flags & SYNTHETIC != 0
        || find_attribute(&member.attributes, pool, "Synthetic")
            .is_ok_and(|attribute| attribute.is_some())
}

fn synthetic_method<'c, 'a>(
    class: &'c ClassFile<'a>,
    name: &str,
    descriptor: &str,
) -> Option<&'c Member<'a>> {
    let pool = &class.pool;
    class
        .methods
        .iter()
        .find(|method| {
            pool.utf8(method.name_index)
                .is_ok_and(|candidate| candidate == name)
                && pool
                    .utf8(method.descriptor_index)
                    .is_ok_and(|candidate| candidate == descriptor)
        })
        .filter(|member| is_synthetic(pool, member))
}

/// Do not let retained implementation methods collide with a fresh javac
/// helper generated to implement the decompiled source lambda.
pub(crate) fn source_method_name<'n>(
    class: &ClassFile<'_>,
    name: &'n str,
    descriptor: &str,
) -> Cow<'n, str> {
    if !name.starts_with("lambda$") || synthetic_method(class, name, descriptor).is_none() {
        return Cow::Borrowed(name);
    }
    let mut source = format!("_{name}");
    let pool = &class.pool;
    while class.methods.iter().any(|method| {
        pool.utf8(method.name_index)
            .is_ok_and(|name| name == source)
    }) {
        source.insert(0, '_');
    }
    Cow::Owned(source)
}

fn java_identifier(machine: &Machine<'_, '_>, name: &str) -> bool {
    crate::naming::is_valid_local_identifier(name, machine.class.major_version)
}

fn stored_slot(op: &Instruction) -> Option<u16> {
    match (op.opcode, &op.operand) {
        (0x36..=0x3a, Operand::Local(slot)) | (0x84, Operand::Increment { index: slot, .. }) => {
            Some(*slot)
        }
        (0x3b..=0x4e, _) => Some(u16::from((op.opcode - 0x3b) % 4)),
        _ => None,
    }
}

impl<'a, 'c> Machine<'a, 'c> {
    pub(super) fn dynamic_constant(&mut self, index: u16) -> Result<Expr, LiftError> {
        if self.bootstrap.is_none() {
            self.bootstrap = Some(self.class.bootstrap_methods()?.into());
        }
        let pool = &self.class.pool;
        let Constant::Dynamic {
            bootstrap_index,
            name_and_type_index,
        } = *pool.get(index)?
        else {
            return Err(self.invalid_operand("expected a dynamic constant"));
        };
        let methods = self.bootstrap.as_ref().expect("loaded bootstrap methods");
        let method = methods
            .get(usize::from(bootstrap_index))
            .ok_or_else(|| self.invalid_operand("bootstrap index is out of range"))?;
        let Constant::MethodHandle {
            reference_kind: 6,
            reference_index,
        } = *pool.get(method.method_ref)?
        else {
            return Err(self.unsupported("non-static dynamic constant bootstrap"));
        };
        if !matches!(pool.get(reference_index)?, Constant::Methodref { .. }) {
            return Err(self.unsupported("dynamic constant bootstrap is not a static class method"));
        }
        let (owner, bootstrap, signature) = pool.member_ref(reference_index)?;
        if owner != "java/lang/invoke/ConstantBootstraps" {
            return Err(self.unsupported("custom dynamic constant bootstrap requires JVM linkage"));
        }
        let (name, descriptor) = pool.name_and_type(name_and_type_index)?;
        let ty = Type::parse(descriptor)?;
        let suffix = signature.strip_prefix(CONSTANT_BOOTSTRAP_PREFIX);
        let args = method.arguments.as_slice();
        match (bootstrap, suffix, args) {
            ("nullConstant", Some(")Ljava/lang/Object;"), []) if is_reference(&ty) => Ok(Expr {
                source: Source::Null,
                ..Expr::atom(ty, "null".into())
            }),
            ("primitiveClass", Some(")Ljava/lang/Class;"), [])
                if descriptor == "Ljava/lang/Class;" =>
            {
                if !matches!(name, "Z" | "B" | "C" | "S" | "I" | "J" | "F" | "D" | "V") {
                    return Err(self.invalid_operand("invalid primitiveClass constant name"));
                }
                let primitive = if name == "V" {
                    Type::Void
                } else {
                    Type::parse(name)?
                };
                Ok(Expr::atom(
                    ty,
                    format!("{}.class", self.render_type(&primitive)).into(),
                ))
            }
            ("enumConstant", Some(")Ljava/lang/Enum;"), []) => {
                let Type::Object(owner) = &ty else {
                    return Err(self.invalid_operand("enumConstant needs an enum type"));
                };
                if !java_identifier(self, name) {
                    return Err(self.unsupported("enum constant name is not a Java identifier"));
                }
                if let Some(class) = self.dynamic_class(owner)
                    && (class.access_flags & ENUM == 0
                        || !class.fields.iter().any(|field| {
                            field.access_flags & (ENUM | STATIC | FINAL) == (ENUM | STATIC | FINAL)
                                && class.pool.utf8(field.name_index).is_ok_and(|n| n == name)
                                && class
                                    .pool
                                    .utf8(field.descriptor_index)
                                    .is_ok_and(|d| d == descriptor)
                        }))
                {
                    return Err(self.invalid_operand("enumConstant does not name an enum member"));
                }
                let mut text = self.class_reference(owner);
                text.push('.');
                self.append_field_reference(&mut text, name, owner, name, descriptor);
                self.expression(ty, text, PRIMARY, [], true)
            }
            ("getStaticFinal", Some(")Ljava/lang/Object;"), [])
            | ("getStaticFinal", Some("Ljava/lang/Class;)Ljava/lang/Object;"), [_]) => {
                let owner = match args {
                    [index] => pool.class_name(*index)?,
                    [] => match &ty {
                        Type::Object(owner) => owner,
                        Type::Primitive(primitive) => wrapper(*primitive).0,
                        Type::Array(_) | Type::Void => {
                            return Err(
                                self.unsupported("getStaticFinal has no source declaring class")
                            );
                        }
                    },
                    _ => unreachable!(),
                };
                self.static_final_dynamic(&ty, owner, name, descriptor)
            }
            ("explicitCast", Some("Ljava/lang/Object;)Ljava/lang/Object;"), [argument]) => {
                self.explicit_cast_dynamic(ty, *argument)
            }
            ("fieldVarHandle" | "staticFieldVarHandle" | "arrayVarHandle", _, _) => {
                self.var_handle_constant(bootstrap, signature, name, ty, args)
            }
            ("invoke", _, _) => {
                Err(self
                    .unsupported("dynamic constant bootstrap requires lazy, cached JVM linkage"))
            }
            _ => Err(self.unsupported("unrepresentable ConstantBootstraps invocation")),
        }
    }

    fn static_final_dynamic(
        &self,
        ty: &Type,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> Result<Expr, LiftError> {
        // Inlining a ConstantValue from another class could suppress that
        // class's initialization. A non-constant final can also be sampled and
        // cached before its initializer runs (e.g. during reentrant <clinit>).
        if owner != self.owner || !java_identifier(self, name) {
            return Err(self.unsupported("getStaticFinal needs verified initialization semantics"));
        }
        let pool = &self.class.pool;
        for field in &self.class.fields {
            if field.access_flags & (STATIC | FINAL) == (STATIC | FINAL)
                && pool.utf8(field.name_index)? == name
                && pool.utf8(field.descriptor_index)? == descriptor
                && find_attribute(&field.attributes, pool, "ConstantValue")?.is_some()
            {
                let mut text = self.class_reference(owner);
                text.push('.');
                self.append_field_reference(&mut text, name, owner, name, descriptor);
                return Ok(Expr::literal(ty.clone(), text));
            }
        }
        Err(self.unsupported("getStaticFinal can cache a value read during class initialization"))
    }

    fn explicit_cast_dynamic(&self, ty: Type, index: u16) -> Result<Expr, LiftError> {
        let pool = &self.class.pool;
        let constant = pool.get(index)?;
        // Primitive results cannot expose a changed wrapper identity. Numeric
        // casts here are ordinary Java casts (never reflective bootstrap calls).
        let Type::Primitive(target) = ty else {
            if matches!(constant, Constant::String(_))
                && matches!(&ty, Type::Object(name) if name == "java/lang/String" || name == "java/lang/Object")
            {
                let literal =
                    super::constant_literal(pool, index, None, self.options.ascii_strings)?;
                let string = Type::Object("java/lang/String".into());
                let value = Expr::literal(string.clone(), literal.into());
                return if ty == string {
                    Ok(value)
                } else {
                    self.cast(value, ty, false)
                };
            }
            if matches!(constant, Constant::Class(_))
                && matches!(&ty, Type::Object(name) if matches!(name.as_str(), "java/lang/Class" | "java/lang/Object"))
            {
                let class = self.class_type(index)?;
                let class_type = Type::Object("java/lang/Class".into());
                let mut text = self.type_reference(&class);
                text.push_str(".class");
                let value = self.expression(class_type.clone(), text, PRIMARY, [], true)?;
                return if ty == class_type {
                    Ok(value)
                } else {
                    self.cast(value, ty, false)
                };
            }
            return Err(self
                .unsupported("explicitCast reference result may require a cached runtime value"));
        };
        if !matches!(
            constant,
            Constant::Integer(_) | Constant::Long(_) | Constant::Float(_) | Constant::Double(_)
        ) {
            return Err(self.unsupported("explicitCast has a non-numeric bootstrap argument"));
        }
        if matches!(constant, Constant::Float(value) if value.is_nan() && value.to_bits() != f32::NAN.to_bits())
            || matches!(constant, Constant::Double(value) if value.is_nan() && value.to_bits() != f64::NAN.to_bits())
        {
            return Err(self.unsupported("explicitCast of a noncanonical NaN"));
        }
        let literal = super::constant_literal(pool, index, None, self.options.ascii_strings)?;
        let text = if target == Primitive::Boolean {
            format!("((int)({literal}) & 1) != 0")
        } else {
            format!("({})({literal})", target.java_name())
        };
        let precedence = if target == Primitive::Boolean {
            super::expr::EQUALITY
        } else {
            UNARY
        };
        Ok(Expr {
            precedence,
            ..Expr::literal(Type::Primitive(target), text.into())
        })
    }
}
