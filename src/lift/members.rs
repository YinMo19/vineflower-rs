// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::{
    bytecode::{Instruction, Operand},
    classfile::Constant,
    descriptor::{MethodDescriptor, Type},
    source_text::Document,
};

use super::{
    Effect, LiftError, Machine,
    concat::{builder_constructor, call_source, inline_value_of, is_string, push_joined},
    dynamic::LambdaSite,
    expr::{ADDITIVE, Category, Expr, Order, PRIMARY, Source},
    string_literal,
};

impl Machine<'_, '_> {
    pub(super) fn field(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        let index = self.constant_index(op)?;
        let pool = &self.class.pool;
        if !matches!(pool.get(index)?, Constant::Fieldref { .. }) {
            return Err(self.invalid_operand("field opcode requires a Fieldref"));
        }
        let (owner, name, descriptor) = pool.member_ref(index)?;
        let source_name = self
            .renames
            .map_or(name, |renames| renames.field_name(owner, name, descriptor));
        let ty = Type::parse(descriptor)?;
        let write = matches!(op.opcode, 0xb3 | 0xb5);
        let value = if write {
            let value = self.pop_category(Category::of(&ty).expect("field type is not void"))?;
            Some(self.coerce(value, &ty, false)?)
        } else {
            None
        };
        let mut receiver = None;
        let mut access = if matches!(op.opcode, 0xb4 | 0xb5) {
            let expr = if write {
                let expr = self.pop_raw()?;
                if Category::of(&expr.ty) != Some(Category::Ref) {
                    return Err(self.invalid_stack("field receiver needs a reference"));
                }
                expr
            } else {
                self.pop_category(Category::Ref)?
            };
            if let Some(effect) =
                self.synthetic_outer_access(owner, name, descriptor, &expr, value.as_ref())?
            {
                return Ok(effect);
            }
            if let Some(effect) =
                self.synthetic_anonymous_capture(owner, name, descriptor, &expr, value.as_ref())?
            {
                return Ok(effect);
            }
            if expr.is_uninitialized(self.initialized_this) {
                return Err(self.invalid_stack("uninitialized receiver used before invokespecial"));
            }
            if matches!(expr.source, Source::This) && self.super_class == Some(owner) {
                Document::from("super.")
            } else {
                let expr = self.member_receiver(expr, owner, false)?;
                let access = if self.unnamed_enclosing_receiver(&expr) {
                    if self.current_member_named(source_name, false)? {
                        return Err(self.unsupported("an unnameable enclosing field is shadowed"));
                    }
                    Document::new()
                } else {
                    let mut head = expr.at(PRIMARY).into_owned();
                    if head.begin_qualifier(breakable_qualifier(&expr), expr.precedence == PRIMARY)
                    {
                        head.end_group();
                    }
                    head.push('.');
                    head
                };
                receiver = Some(expr);
                access
            }
        } else if write
            && self.method_name == "<clinit>"
            && owner == self.owner
            && self.own_field_is_static_final(name, descriptor)?
        {
            // A blank static final must be assigned by simple name in its
            // declaring class, even though ordinary static writes can qualify.
            Document::new()
        } else {
            let mut head = Document::from((self.class_name)(owner));
            head.push('.');
            head
        };
        self.anchor_member(&mut access, op);
        access.push_str(source_name);
        if let Some(value) = value {
            let order = self.order_of(receiver.iter().chain([&value]), true)?;
            self.before_statement(order)?;
            Ok(Effect::FieldAssignment {
                target: access,
                value: value.text,
            })
        } else {
            self.push(self.expression(ty, access, PRIMARY, receiver.iter(), true)?)?;
            Ok(Effect::None)
        }
    }

    fn own_field_is_static_final(&self, name: &str, descriptor: &str) -> Result<bool, LiftError> {
        let pool = &self.class.pool;
        for field in &self.class.fields {
            if field.access_flags & 0x0018 == 0x0018
                && pool.utf8(field.name_index)? == name
                && pool.utf8(field.descriptor_index)? == descriptor
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn invoke(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        let (index, count) = if op.opcode == 0xb9 {
            let Operand::InvokeInterface { index, count } = op.operand else {
                return Err(self.invalid_operand("expected invokeinterface member and slot count"));
            };
            (index, Some(count))
        } else {
            (self.constant_index(op)?, None)
        };
        let pool = &self.class.pool;
        let tag = pool.get(index)?;
        if !matches!(
            (op.opcode, tag),
            (0xb6..=0xb8, Constant::Methodref { .. })
                | (0xb7..=0xb9, Constant::InterfaceMethodref { .. })
        ) {
            return Err(
                self.invalid_operand("expected a method reference matching the invocation opcode")
            );
        }
        let (owner, name, method_type) = pool.member_ref(index)?;
        let descriptor = MethodDescriptor::parse(method_type)?;
        if count.is_some_and(|count| {
            u16::from(count) != 1 + descriptor.parameters.iter().map(Type::slots).sum::<u16>()
        }) {
            return Err(
                self.invalid_operand("invokeinterface slot count does not match descriptor")
            );
        }
        let member = (owner, name, method_type);
        let mut args = self.raw_arguments(&descriptor)?;
        if name == "<init>" {
            if op.opcode != 0xb7 || descriptor.return_type != Type::Void {
                return Err(
                    self.invalid_operand("constructor needs a void invokespecial descriptor")
                );
            }
            let omit = self.omit_invocation_casts(owner, member, &descriptor, &args, op.opcode);
            self.coerce_arguments(&mut args, &descriptor, Some(member), None, omit)?;
            return self.construct(owner, method_type, args);
        }
        if name.starts_with('<') {
            return Err(self.invalid_operand("invalid method invocation name"));
        }
        let mut receiver = None;
        let mut super_call = false;
        if op.opcode != 0xb8 {
            let expr = self.pop_category(Category::Ref)?;
            if op.opcode == 0xb7 && owner != self.owner {
                if !matches!(expr.source, Source::This) {
                    return Err(
                        self.unsupported("non-this invokespecial needs a nonvirtual Java dispatch")
                    );
                }
                super_call = true;
                if matches!(tag, Constant::InterfaceMethodref { .. }) {
                    if !self.class.interfaces.iter().any(|index| {
                        pool.class_name(*index)
                            .is_ok_and(|interface| interface == owner)
                    }) {
                        return Err(self.unsupported("indirect interface super invocation"));
                    }
                } else if self.super_class.is_none() {
                    return Err(
                        self.invalid_operand("special super invocation without a superclass")
                    );
                }
            } else {
                if op.opcode == 0xb7 && !self.own_method_is_private(name, method_type)? {
                    return Err(self.unsupported(
                        "nonvirtual invokespecial of a nonprivate current-class method",
                    ));
                }
                let expr = self.member_receiver(expr, owner, true)?;
                receiver = Some(expr);
            }
        }
        let lookup_owner = match receiver.as_ref().map(|expr| &expr.ty) {
            Some(Type::Object(owner)) => owner.as_str(),
            _ => owner,
        };
        let generic = self.generic_call(owner, name, method_type, op.opcode == 0xb8);
        let omit = self.omit_invocation_casts(lookup_owner, member, &descriptor, &args, op.opcode);
        self.coerce_arguments(&mut args, &descriptor, Some(member), generic.as_ref(), omit)?;
        if op.opcode == 0xb8
            && let Some(effect) =
                self.synthetic_nest_accessor(owner, name, method_type, &descriptor, &args)?
        {
            return Ok(effect);
        }
        if let Some(effect) =
            self.emit_builder_concat(owner, name, method_type, receiver.as_ref())?
        {
            return Ok(effect);
        }
        let unqualified = receiver
            .as_ref()
            .is_some_and(|receiver| self.unnamed_enclosing_receiver(receiver));
        let (mut text, chain) = if unqualified {
            (Document::new(), false)
        } else if let Some(receiver) = &receiver {
            let mut text = receiver.at(PRIMARY).into_owned();
            let chain = text.begin_qualifier(
                breakable_qualifier(receiver),
                receiver.precedence == PRIMARY,
            );
            (text, chain)
        } else if !super_call {
            ((self.class_name)(owner).into(), false)
        } else if matches!(tag, Constant::InterfaceMethodref { .. }) {
            (format!("{}.super", (self.class_name)(owner)).into(), false)
        } else {
            ("super".into(), false)
        };
        self.record_synthetic_invocation(owner, name, method_type);
        let source_name = self.source_invocation_name(owner, name, method_type);
        if unqualified {
            if self.current_member_named(&source_name, true)? {
                return Err(self.unsupported("an unnameable enclosing method is shadowed"));
            }
        } else {
            text.push('.');
        }
        self.anchor_member(&mut text, op);
        text.push_str(&source_name);
        text.append_relative_arguments(args.iter().map(|argument| &argument.text));
        if chain {
            text.end_group();
        }
        let operands = receiver.iter().chain(&args);
        if descriptor.return_type == Type::Void {
            let order = self.order_of(operands, true)?;
            self.before_statement(order)?;
            text.push(';');
            Ok(Effect::Statement(text))
        } else {
            let result = generic
                .and_then(|call| call.return_type(&args))
                .filter(|result| self.known_assignable(result, &descriptor.return_type))
                .unwrap_or_else(|| descriptor.return_type.clone());
            let mut expression = self.expression(result, text, PRIMARY, operands, true)?;
            expression.source = call_source(owner, name, &descriptor, receiver, args);
            if owner == "java/lang/invoke/MethodHandle" && matches!(name, "invoke" | "invokeExact")
                || owner == "java/lang/invoke/VarHandle"
                    && matches!(
                        name,
                        "get"
                            | "getVolatile"
                            | "getOpaque"
                            | "getAcquire"
                            | "compareAndSet"
                            | "compareAndExchange"
                            | "compareAndExchangeAcquire"
                            | "compareAndExchangeRelease"
                            | "weakCompareAndSetPlain"
                            | "weakCompareAndSet"
                            | "weakCompareAndSetAcquire"
                            | "weakCompareAndSetRelease"
                            | "getAndSet"
                            | "getAndSetAcquire"
                            | "getAndSetRelease"
                            | "getAndAdd"
                            | "getAndAddAcquire"
                            | "getAndAddRelease"
                            | "getAndBitwiseOr"
                            | "getAndBitwiseOrAcquire"
                            | "getAndBitwiseOrRelease"
                            | "getAndBitwiseAnd"
                            | "getAndBitwiseAndAcquire"
                            | "getAndBitwiseAndRelease"
                            | "getAndBitwiseXor"
                            | "getAndBitwiseXorAcquire"
                            | "getAndBitwiseXorRelease"
                    )
            {
                // The cast is part of the signature-polymorphic invocation
                // descriptor, not a runtime conversion of an Object result.
                let ty = expression.ty.clone();
                let expression = self.cast(expression, ty, false)?;
                self.push(expression)?;
            } else {
                self.push(Expr {
                    statement: true,
                    ..expression
                })?;
            }
            Ok(Effect::None)
        }
    }

    pub(super) fn member_receiver(
        &self,
        receiver: Expr,
        owner: &str,
        virtual_call: bool,
    ) -> Result<Expr, LiftError> {
        let ty = if owner.starts_with('[') {
            Type::parse(owner)?
        } else {
            Type::Object(owner.into())
        };
        if !matches!(receiver.source, Source::Null)
            && (receiver.ty == ty
                || (virtual_call
                    && matches!(receiver.source, Source::This | Source::OuterThis)
                    && self.known_assignable(&receiver.ty, &ty)))
        {
            Ok(receiver)
        } else {
            self.reference_cast(receiver, ty, false)
        }
    }

    fn current_member_named(&self, source_name: &str, method: bool) -> Result<bool, LiftError> {
        let pool = &self.class.pool;
        let members = if method {
            &self.class.methods
        } else {
            &self.class.fields
        };
        for member in members {
            let name = pool.utf8(member.name_index)?;
            let descriptor = pool.utf8(member.descriptor_index)?;
            let same_name = if method {
                self.source_invocation_name(self.owner, name, descriptor) == source_name
            } else {
                self.source_field_name(self.owner, name, descriptor) == source_name
            };
            if same_name {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn own_method_is_private(
        &self,
        name: &str,
        descriptor: &str,
    ) -> Result<bool, LiftError> {
        let pool = &self.class.pool;
        for method in &self.class.methods {
            if method.access_flags & 0x0002 != 0
                && pool.utf8(method.name_index)? == name
                && pool.utf8(method.descriptor_index)? == descriptor
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn arguments(
        &mut self,
        descriptor: &MethodDescriptor,
        member: Option<(&str, &str, &str)>,
    ) -> Result<Vec<Expr>, LiftError> {
        let mut args = self.raw_arguments(descriptor)?;
        self.coerce_arguments(&mut args, descriptor, member, None, false)?;
        Ok(args)
    }

    fn raw_arguments(&mut self, descriptor: &MethodDescriptor) -> Result<Vec<Expr>, LiftError> {
        let mut args = Vec::with_capacity(descriptor.parameters.len());
        for ty in descriptor.parameters.iter().rev() {
            args.push(self.pop_category(Category::of(ty).expect("parameter type is not void"))?);
        }
        args.reverse();
        Ok(args)
    }

    fn coerce_arguments(
        &self,
        args: &mut [Expr],
        descriptor: &MethodDescriptor,
        member: Option<(&str, &str, &str)>,
        generic: Option<&super::generics::GenericCall>,
        omit_widening: bool,
    ) -> Result<(), LiftError> {
        for (index, (value, ty)) in args.iter_mut().zip(&descriptor.parameters).enumerate() {
            if value.ty == *ty && !matches!(value.source, Source::Null) {
                continue;
            }
            // The core Throwable family exposes one cause-taking overload of
            // each arity. A statically known exception can widen implicitly
            // without risking selection of a different overload.
            let throwable_constructor =
                member.is_some_and(|(owner, name, _)| name == "<init>" && core_throwable(owner));
            let throwable_parameter =
                matches!(ty, Type::Object(name) if name == "java/lang/Throwable");
            let known_throwable = matches!(&value.ty, Type::Object(name) if core_throwable(name)
                || name == self.owner && self.super_class.is_some_and(core_throwable));
            let enclosing_constructor = index == 0
                && member.is_some_and(|(owner, name, desc)| {
                    name == "<init>"
                        && self.group.is_some_and(|group| {
                            group.constructor_outer(owner, desc).is_some()
                                && self.known_assignable(&value.ty, ty)
                        })
                });
            if enclosing_constructor
                || throwable_constructor && throwable_parameter && known_throwable
                || generic.is_some_and(|call| call.argument_fits(index, value, ty, self))
                || omit_widening && self.invocation_argument_widens(value, ty)
            {
                continue;
            }
            let operand = std::mem::replace(value, Expr::atom(Type::Void, Document::new()));
            *value = self.coerce(operand, ty, true)?;
        }
        Ok(())
    }

    fn construct(
        &mut self,
        owner: &str,
        method_type: &str,
        args: Vec<Expr>,
    ) -> Result<Effect, LiftError> {
        let receiver = self.pop_raw()?;
        match receiver.source {
            Source::This if !self.initialized_this => {
                if !self.stack_is_empty() || !self.prelude.is_empty() {
                    return Err(self.unsupported("constructor chaining with pending stack values"));
                }
                self.order_of(&args, true)?;
                let target = if owner == self.owner {
                    "this"
                } else if self.super_class == Some(owner) {
                    "super"
                } else {
                    return Err(self.invalid_operand(
                        "constructor must target this class or its direct superclass",
                    ));
                };
                let (target, visible_args) =
                    self.constructor_target(owner, method_type, &args, Some(target))?;
                let visible_args = if self.class.access_flags & 0x4000 != 0 && owner == self.owner {
                    let [label, ordinal, visible @ ..] = visible_args else {
                        return Err(
                            self.invalid_operand("missing implicit enum constructor arguments")
                        );
                    };
                    if !matches!(label.source, Source::Local(1))
                        || !matches!(ordinal.source, Source::Local(2))
                        || !method_type.starts_with("(Ljava/lang/String;I")
                    {
                        return Err(self.unsupported("noncanonical enum constructor delegation"));
                    }
                    visible
                } else {
                    visible_args
                };
                self.initialized_this = true;
                let mut text = target;
                text.append_relative_arguments(visible_args.iter().map(|argument| &argument.text));
                text.push(';');
                Ok(Effect::Statement(text))
            }
            Source::New(allocation) => {
                if !matches!(&receiver.ty, Type::Object(name) if name == owner) {
                    return Err(self.invalid_operand("constructor owner does not match new"));
                }
                // Unlike explicit this()/super() delegation, this call is
                // part of a new expression. Its arguments own the mappings.
                self.instruction_has_source = false;
                let order = self
                    .order_of(&args, true)?
                    .expect("constructor has effects");
                let order = Some(self.join_order(Some(Order::at(allocation)), order)?);
                let text =
                    if let Some(text) = self.anonymous_construction(owner, method_type, &args)? {
                        text
                    } else {
                        let (target, visible_args) =
                            self.constructor_target(owner, method_type, &args, None)?;
                        let mut text = target;
                        text.append_relative_arguments(
                            visible_args.iter().map(|argument| &argument.text),
                        );
                        text
                    };
                let mut value = Expr {
                    order,
                    observable: true,
                    statement: true,
                    source: builder_constructor(owner, method_type, args),
                    ..Expr::atom(receiver.ty, text)
                };
                let is_alias = |value: &Expr| matches!(value.source, Source::New(offset) if offset == allocation);
                let aliases = self.stack.iter().filter(|value| is_alias(value)).count();
                if aliases == 0 {
                    self.before_statement(order)?;
                    value.text.push(';');
                    return Ok(Effect::Statement(value.text));
                }
                if aliases > 1 {
                    let pending =
                        self.order_of(self.stack.iter().filter(|value| !is_alias(value)), false)?;
                    self.join_order(pending, order.expect("constructor has effects"))?;
                    if !self.initialized_this
                        || self.stack.iter().any(|value| {
                            !is_alias(value) && value.is_uninitialized(self.initialized_this)
                        })
                    {
                        return Err(self.unsupported(
                            "multiple surviving allocation aliases in an unfinished constructor",
                        ));
                    }
                    let mut stack = std::mem::take(&mut self.stack);
                    for item in stack.iter_mut().filter(|value| value.order.is_some()) {
                        self.spill(item);
                    }
                    self.spill(&mut value);
                    self.stack = stack;
                }
                let mut value = Some(value);
                let mut remaining = aliases;
                for item in self.stack.iter_mut().filter(|value| is_alias(value)) {
                    remaining -= 1;
                    *item = if remaining == 0 {
                        value.take().expect("last alias")
                    } else {
                        value.as_ref().expect("remaining aliases").clone()
                    };
                }
                Ok(Effect::None)
            }
            _ => Err(self.invalid_stack("invokespecial <init> requires an uninitialized receiver")),
        }
    }

    pub(super) fn invoke_dynamic(&mut self, op: &Instruction) -> Result<Effect, LiftError> {
        let index = self.constant_index(op)?;
        let pool = &self.class.pool;
        let Constant::InvokeDynamic {
            bootstrap_index,
            name_and_type_index,
        } = *pool.get(index)?
        else {
            return Err(self.invalid_operand("invokedynamic requires an InvokeDynamic entry"));
        };
        if self.bootstrap.is_none() {
            self.bootstrap = Some(self.class.bootstrap_methods()?.into());
        }
        let methods = self.bootstrap.as_ref().expect("loaded bootstrap methods");
        let method = methods
            .get(usize::from(bootstrap_index))
            .ok_or_else(|| self.invalid_operand("bootstrap index is out of range"))?;
        let Constant::MethodHandle {
            reference_kind: 6,
            reference_index,
        } = *pool.get(method.method_ref)?
        else {
            return Err(self.unsupported("non-static invokedynamic bootstrap"));
        };
        let (owner, name, bootstrap_descriptor) = pool.member_ref(reference_index)?;
        let (sam_name, method_descriptor) = pool.name_and_type(name_and_type_index)?;
        if owner == "java/lang/invoke/LambdaMetafactory" {
            let site = LambdaSite::read(self, name, bootstrap_descriptor, sam_name, method)?;
            return self.lower_lambda(site, MethodDescriptor::parse(method_descriptor)?);
        }
        if owner != "java/lang/invoke/StringConcatFactory"
            || !matches!(name, "makeConcat" | "makeConcatWithConstants")
        {
            return Err(self.unsupported("unrecognized invokedynamic bootstrap"));
        }
        let descriptor = MethodDescriptor::parse(method_descriptor)?;
        if !is_string(&descriptor.return_type) {
            return Err(self.invalid_operand("string concatenation must return String"));
        }
        let mut parts = Vec::new();
        if name == "makeConcat" {
            if !method.arguments.is_empty() {
                return Err(self.invalid_operand("makeConcat does not take bootstrap arguments"));
            }
            parts.extend((0..descriptor.parameters.len()).map(Part::Arg));
        } else {
            let (&recipe_index, constants) = method
                .arguments
                .split_first()
                .ok_or_else(|| self.invalid_operand("missing string concatenation recipe"))?;
            let Constant::String(text_index) = *pool.get(recipe_index)? else {
                return Err(self.invalid_operand("concat recipe is not a String"));
            };
            let recipe = pool.utf16(text_index)?;
            let mut literal_start = 0;
            let mut arg_index = 0;
            let mut constant_index = 0;
            for (position, &unit) in recipe.iter().enumerate() {
                if !matches!(unit, 1 | 2) {
                    continue;
                }
                if literal_start < position {
                    parts.push(Part::Text(string_literal(
                        &recipe[literal_start..position],
                        self.options.ascii_strings,
                    )));
                }
                literal_start = position + 1;
                if unit == 1 {
                    parts.push(Part::Arg(arg_index));
                    arg_index += 1;
                } else {
                    let index = *constants.get(constant_index).ok_or_else(|| {
                        self.invalid_operand("concat recipe references a missing constant")
                    })?;
                    let literal = match pool.get(index)? {
                        Constant::String(index) => {
                            string_literal(&pool.utf16(*index)?, self.options.ascii_strings)
                        }
                        Constant::Integer(_)
                        | Constant::Long(_)
                        | Constant::Float(_)
                        | Constant::Double(_) => {
                            let number = super::constant_literal(
                                pool,
                                index,
                                None,
                                self.options.ascii_strings,
                            )?;
                            format!("(\"\" + {number})")
                        }
                        _ => {
                            return Err(self
                                .unsupported("non-literal string concatenation recipe constant"));
                        }
                    };
                    parts.push(Part::Text(literal));
                    constant_index += 1;
                }
            }
            if literal_start < recipe.len() {
                parts.push(Part::Text(string_literal(
                    &recipe[literal_start..],
                    self.options.ascii_strings,
                )));
            }
            if arg_index != descriptor.parameters.len() || constant_index != constants.len() {
                return Err(self.invalid_operand("concat recipe does not match its arguments"));
            }
        }
        let mut args = self.arguments(&descriptor, None)?;
        // A reference's toString can run arbitrary code. invokedynamic
        // evaluates all its arguments before it converts any of them.
        let conversion = args
            .iter()
            .position(|arg| Category::of(&arg.ty) == Some(Category::Ref) && !is_string(&arg.ty));
        if conversion.is_some_and(|index| args[index + 1..].iter().any(|arg| arg.order.is_some())) {
            self.freeze_values(&mut args)?;
        }
        inline_value_of(&mut args);
        let is_text = |part: &Part| match part {
            Part::Text(_) => true,
            Part::Arg(index) => is_string(&args[*index].ty),
        };
        let mut text = Document::new();
        if parts.len() != 1 && !parts.iter().take(2).any(is_text) {
            text.push_str("\"\"");
        }
        let single = parts.len() == 1;
        for part in parts {
            match part {
                Part::Text(literal) => {
                    if !text.is_empty() {
                        text.push_str(" + ");
                    }
                    text.push_str(&literal);
                }
                Part::Arg(index) => push_joined(&mut text, &args[index]),
            }
        }
        if single {
            text.push_str(" + \"\"");
        }
        // An invokedynamic concat is not a Java constant expression. Preserve
        // the distinction when every operand can be folded into a literal.
        let precedence = if args.iter().all(|arg| arg.constant) {
            let string = self.render_type(&descriptor.return_type);
            text.surround(&format!("new {string}("), ")");
            PRIMARY
        } else {
            ADDITIVE
        };
        self.push(self.expression(descriptor.return_type, text, precedence, &args, true)?)?;
        Ok(Effect::None)
    }

    fn anchor_member(&self, text: &mut Document, op: &Instruction) {
        if self.options.include_line_mappings && self.normalized.is_none() {
            text.anchor(op.offset..op.offset + op.len);
        }
    }
}

enum Part {
    Text(String),
    Arg(usize),
}

fn core_throwable(name: &str) -> bool {
    matches!(
        name,
        "java/lang/Throwable"
            | "java/lang/Exception"
            | "java/lang/RuntimeException"
            | "java/lang/Error"
    )
}

fn breakable_qualifier(receiver: &Expr) -> bool {
    receiver.observable
        || receiver.text.has_layout()
        || !matches!(
            receiver.source,
            Source::Local(_)
                | Source::CapturedLocal
                | Source::Plain
                | Source::This
                | Source::OuterThis
        )
}
