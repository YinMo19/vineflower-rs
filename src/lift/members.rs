// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::fmt::Write;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::Constant,
    descriptor::{MethodDescriptor, Type},
};

use super::{
    Effect, LiftError, Machine,
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
        let ty = Type::parse(descriptor)?;
        let write = matches!(op.opcode, 0xb3 | 0xb5);
        let value = if write {
            let value = self.pop_category(Category::of(&ty).expect("field type is not void"))?;
            Some(self.coerce(value, &ty, false)?)
        } else {
            None
        };
        let mut receiver = None;
        let access = if matches!(op.opcode, 0xb4 | 0xb5) {
            let expr = self.pop_category(Category::Ref)?;
            if matches!(expr.source, Source::This) && self.super_class == Some(owner) {
                format!("super.{name}")
            } else {
                let expr = self.member_receiver(expr, owner, false)?;
                let access = format!("{}.{name}", expr.at(PRIMARY));
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
            name.to_owned()
        } else {
            format!("{}.{name}", (self.class_name)(owner))
        };
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
        let args = self.arguments(&descriptor, Some((owner, name)))?;
        if name == "<init>" {
            if op.opcode != 0xb7 || descriptor.return_type != Type::Void {
                return Err(
                    self.invalid_operand("constructor needs a void invokespecial descriptor")
                );
            }
            return self.construct(owner, args);
        }
        if name.starts_with('<') {
            return Err(self.invalid_operand("invalid method invocation name"));
        }
        let mut receiver = None;
        let qualifier = if op.opcode == 0xb8 {
            (self.class_name)(owner)
        } else {
            let expr = self.pop_category(Category::Ref)?;
            if op.opcode == 0xb7 && owner != self.owner {
                if !matches!(expr.source, Source::This) {
                    return Err(
                        self.unsupported("non-this invokespecial needs a nonvirtual Java dispatch")
                    );
                }
                if matches!(tag, Constant::InterfaceMethodref { .. }) {
                    if !self.class.interfaces.iter().any(|index| {
                        pool.class_name(*index)
                            .is_ok_and(|interface| interface == owner)
                    }) {
                        return Err(self.unsupported("indirect interface super invocation"));
                    }
                    format!("{}.super", (self.class_name)(owner))
                } else if self.super_class.is_some() {
                    "super".into()
                } else {
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
                let qualifier = expr.at(PRIMARY).into_owned();
                receiver = Some(expr);
                qualifier
            }
        };
        let text = format!("{qualifier}.{name}({})", render_arguments(&args));
        let operands = receiver.iter().chain(&args);
        if descriptor.return_type == Type::Void {
            let order = self.order_of(operands, true)?;
            self.before_statement(order)?;
            Ok(Effect::Statement(format!("{text};")))
        } else {
            let expression =
                self.expression(descriptor.return_type, text, PRIMARY, operands, true)?;
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

    fn member_receiver(
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
                    && matches!(receiver.source, Source::This)
                    && self.known_assignable(&receiver.ty, &ty)))
        {
            Ok(receiver)
        } else {
            self.reference_cast(receiver, ty, false)
        }
    }

    fn own_method_is_private(&self, name: &str, descriptor: &str) -> Result<bool, LiftError> {
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

    fn arguments(
        &mut self,
        descriptor: &MethodDescriptor,
        member: Option<(&str, &str)>,
    ) -> Result<Vec<Expr>, LiftError> {
        let mut args = Vec::with_capacity(descriptor.parameters.len());
        for ty in descriptor.parameters.iter().rev() {
            let value = self.pop_category(Category::of(ty).expect("parameter type is not void"))?;
            // The core Throwable family exposes one cause-taking overload of
            // each arity. A statically known exception can widen implicitly
            // without risking selection of a different overload.
            let throwable_constructor =
                member.is_some_and(|(owner, name)| name == "<init>" && core_throwable(owner));
            let throwable_parameter =
                matches!(ty, Type::Object(name) if name == "java/lang/Throwable");
            let known_throwable = matches!(&value.ty, Type::Object(name) if core_throwable(name)
                || name == self.owner && self.super_class.is_some_and(core_throwable));
            let value = if throwable_constructor && throwable_parameter && known_throwable {
                value
            } else {
                self.coerce(value, ty, true)?
            };
            args.push(value);
        }
        args.reverse();
        Ok(args)
    }

    fn construct(&mut self, owner: &str, args: Vec<Expr>) -> Result<Effect, LiftError> {
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
                self.initialized_this = true;
                Ok(Effect::Statement(format!(
                    "{target}({});",
                    render_arguments(&args)
                )))
            }
            Source::New(allocation) => {
                if !matches!(&receiver.ty, Type::Object(name) if name == owner) {
                    return Err(self.invalid_operand("constructor owner does not match new"));
                }
                let order = self
                    .order_of(&args, true)?
                    .expect("constructor has effects");
                let order = Some(self.join_order(Some(Order::at(allocation)), order)?);
                let text = format!(
                    "new {}({})",
                    (self.class_name)(owner),
                    render_arguments(&args)
                );
                let mut value = Expr {
                    order,
                    observable: true,
                    statement: true,
                    ..Expr::atom(receiver.ty, text)
                };
                let is_alias = |value: &Expr| matches!(value.source, Source::New(offset) if offset == allocation);
                let aliases = self.stack.iter().filter(|value| is_alias(value)).count();
                if aliases == 0 {
                    self.before_statement(order)?;
                    return Ok(Effect::Statement(format!("{};", value.text)));
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
        let (owner, name, _) = pool.member_ref(reference_index)?;
        if owner != "java/lang/invoke/StringConcatFactory"
            || !matches!(name, "makeConcat" | "makeConcatWithConstants")
        {
            return Err(self.unsupported("invokedynamic bootstrap other than StringConcatFactory"));
        }
        let (_, method_descriptor) = pool.name_and_type(name_and_type_index)?;
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
        let is_text = |part: &Part| match part {
            Part::Text(_) => true,
            Part::Arg(index) => is_string(&args[*index].ty),
        };
        let mut text = String::new();
        if parts.len() < 2 || !parts.iter().take(2).any(is_text) {
            text.push_str("\"\"");
        }
        for part in parts {
            if !text.is_empty() {
                text.push_str(" + ");
            }
            match part {
                Part::Text(literal) => text.push_str(&literal),
                Part::Arg(index) => text.push_str(&args[index].at(ADDITIVE + 1)),
            }
        }
        // An invokedynamic concat is not a Java constant expression. Preserve
        // the distinction when every operand can be folded into a literal.
        let precedence = if args.iter().all(|arg| arg.constant) {
            let string = self.render_type(&descriptor.return_type);
            text = format!("new {string}({text})");
            PRIMARY
        } else {
            ADDITIVE
        };
        self.push(self.expression(descriptor.return_type, text, precedence, &args, true)?)?;
        Ok(Effect::None)
    }
}

enum Part {
    Text(String),
    Arg(usize),
}

fn is_string(ty: &Type) -> bool {
    matches!(ty, Type::Object(name) if name == "java/lang/String")
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

fn render_arguments(args: &[Expr]) -> String {
    let mut text = String::new();
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            text.push_str(", ");
        }
        let _ = write!(text, "{}", arg.text);
    }
    text
}
