// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::HashSet;

use crate::{
    classfile::ClassFile,
    descriptor::{MethodSignature, Type},
    source_text::Document,
    structure::Line,
};

use super::{
    ABSTRACT, INTERFACE, LambdaSite, LiftError, Machine, STATIC, SiteClass,
    java_identifier,
};
impl Machine<'_, '_> {
    pub(super) fn lambda_expression(
        &self,
        ty: Type,
        text: Document,
        captures: &[super::Expr],
        anonymous: bool,
    ) -> Result<super::Expr, LiftError> {
        let precedence = if anonymous { super::PRIMARY } else { super::UNARY };
        Ok(super::Expr {
            statement: anonymous,
            ..self.expression(ty, text, precedence, captures, true)?
        })
    }

    pub(super) fn qualify_anonymous_lambda_super(&self, qualifier: &mut Document) -> Result<(), LiftError> {
        if *qualifier != "super" || !self.has_named_lambda_enclosure() {
            return Err(self.unsupported("cannot express the lambda's lexical super call inside an anonymous class"));
        }
        let mut outer = self.class_reference(self.owner);
        outer.push_str(".super");
        *qualifier = outer;
        Ok(())
    }

    pub(super) fn prepare_anonymous_lambda_captures(&mut self, captures: &mut [super::Expr]) -> Result<(), LiftError> {
        for capture in captures {
            if self.unnamed_enclosing_receiver(capture) {
                return Err(self.unsupported("anonymous lambda would capture an unnameable enclosing instance"));
            }
            if matches!(capture.source, super::Source::This) {
                if !self.has_named_lambda_enclosure() {
                    return Err(self.unsupported("anonymous lambda would capture an unnameable this"));
                }
                capture.text = self.class_reference(self.owner);
                capture.text.push_str(".this");
            } else if !matches!(capture.source, super::Source::OuterThis)
                && !capture.constant
                && !java_identifier(self, &capture.text)
            {
                // A source cast around `this`, for example, can have no JVM
                // ordering dependency but still needs the lexical receiver.
                self.before_statement(None)?;
                self.spill(capture)?;
            }
        }
        Ok(())
    }

    fn has_named_lambda_enclosure(&self) -> bool {
        !(self.options.decompile_inner && self.group.is_some_and(|group| {
            group.is_attached(self.owner) && group.nested_class(self.owner)
                .is_some_and(|class| matches!(class.kind, crate::context::NestedKind::Anonymous))
        }))
    }
}

pub(super) struct AnonymousSam<'site, 'pool> {
    site: &'site LambdaSite<'pool>,
    throws: Vec<Type>,
}

impl<'site, 'pool> AnonymousSam<'site, 'pool> {
    pub(super) fn read(
        machine: &Machine<'_, '_>,
        interface: &str,
        site: &'site LambdaSite<'pool>,
    ) -> Result<Self, LiftError> {
        if !java_identifier(machine, site.sam_name) {
            return Err(machine.unsupported("anonymous SAM method is not a Java identifier"));
        }
        let interface_type = Type::Object(interface.to_owned());
        if site.markers.iter().any(|marker| {
            *marker != interface && !machine.known_assignable(&interface_type, &Type::Object((*marker).into()))
        }) {
            return Err(machine.unsupported("an anonymous class cannot implement the lambda's additional interfaces"));
        }
        let mut throws = Vec::new();
        let mut visited = HashSet::new();
        let mut pending = vec![interface.to_owned()];
        let mut primary = false;
        while let Some(owner) = pending.pop() {
            if !visited.insert(owner.clone()) {
                continue;
            }
            if matches!(owner.as_str(), "java/io/Serializable" | "java/lang/Cloneable") {
                continue;
            }
            if let Some((name, descriptor, exception)) = standard_sam(&owner) {
                let matches = sam_member(machine, site, name, descriptor)?;
                primary |= matches;
                throws.push(exception.into_iter().map(|name| Type::Object(name.into())).collect());
                continue;
            }
            let Some(class) = machine.lookup_site_class(&owner) else {
                return Err(machine.unsupported("anonymous SAM interface declaration is unavailable"));
            };
            if class.flags() & INTERFACE == 0 {
                return Err(machine.invalid_operand("anonymous SAM target is not an interface"));
            }
            pending.extend(class.interfaces().map(str::to_owned));
            match class {
                SiteClass::Input(class) => {
                    primary |= input_declarations(machine, site, class, &mut throws)?;
                }
                SiteClass::Library(class) => {
                    // The metadata cache omits the Exceptions attribute.
                    // Load the class declaration (not its code) only for a
                    // library interface selected for anonymous rendering.
                    let bytes = [machine.options.library_classpath.as_deref(), machine.options.runtime_classpath.as_deref()]
                        .into_iter().flatten().find_map(|path| path.load(&class.name).ok().flatten());
                    let Some(bytes) = bytes else {
                        return Err(machine.unsupported("anonymous SAM exception metadata is unavailable"));
                    };
                    let declaration = ClassFile::parse(&bytes)?;
                    primary |= input_declarations(machine, site, &declaration, &mut throws)?;
                }
            }
        }
        if !primary {
            return Err(machine.unsupported("anonymous SAM method does not match the interface declaration"));
        }
        // A source override may only throw what every inherited declaration
        // allows. A narrower exception from any declaration is sufficient.
        let mut common = Vec::new();
        for candidate in throws.iter().flatten() {
            if !common.contains(candidate)
                && throws.iter().all(|declared| declared.iter().any(|exception| machine.known_assignable(candidate, exception)))
            {
                common.push(candidate.clone());
            }
        }
        Ok(Self { site, throws: common })
    }

    pub(super) fn call_body(
        &self,
        machine: &Machine<'_, '_>,
        target: &Document,
        parameters: Vec<Document>,
        mut call: Document,
    ) -> Document {
        if self.site.instantiated.return_type != Type::Void {
            call.prepend_str("return ");
        }
        call.push(';');
        self.render(machine, target, parameters, [(0, call)])
    }

    pub(super) fn inline_body(
        &self,
        machine: &Machine<'_, '_>,
        target: &Document,
        parameters: Vec<Document>,
        lines: Vec<Line>,
    ) -> Document {
        self.render(machine, target, parameters, lines.into_iter().map(|line| (line.depth, line.text)))
    }

    fn render(
        &self,
        machine: &Machine<'_, '_>,
        target: &Document,
        parameters: Vec<Document>,
        body: impl IntoIterator<Item = (usize, Document)>,
    ) -> Document {
        let mut source = Document::from("new ");
        source.append_ref(target);
        source.push_str("() {");
        source.hard_line(1);
        if machine.options.override_annotation {
            source.push_str("@Override");
            source.hard_line(1);
        }
        source.push_str("public ");
        source.append(machine.type_document(&self.site.instantiated.return_type));
        source.push(' ');
        source.push_str(self.site.sam_name);
        let mut arguments = Document::relative_delimited(parameters.into_iter().zip(&self.site.instantiated.parameters).map(|(name, ty)| {
            let mut parameter = machine.type_document(ty);
            parameter.push(' ');
            parameter.append(name);
            parameter
        }));
        arguments.offset_relative_depth(1);
        source.append(arguments);
        if !self.throws.is_empty() {
            let mut separator = " throws ";
            for exception in &self.throws {
                source.push_str(separator);
                source.append(machine.type_document(exception));
                separator = ", ";
            }
        }
        source.push_str(" {");
        for (depth, mut line) in body {
            let depth = depth + 2;
            source.hard_line(depth);
            line.offset_relative_depth(depth);
            source.append(line);
        }
        source.hard_line(1);
        source.push('}');
        source.hard_line(0);
        source.push('}');
        source
    }
}

fn input_declarations(
    machine: &Machine<'_, '_>,
    site: &LambdaSite<'_>,
    class: &ClassFile<'_>,
    throws: &mut Vec<Vec<Type>>,
) -> Result<bool, LiftError> {
    let pool = &class.pool;
    let mut primary = false;
    for method in &class.methods {
        if method.access_flags & (ABSTRACT | STATIC) != ABSTRACT {
            continue;
        }
        let name = pool.utf8(method.name_index)?;
        let descriptor = pool.utf8(method.descriptor_index)?;
        if matches!((name, descriptor), ("equals", "(Ljava/lang/Object;)Z") | ("hashCode", "()I") | ("toString", "()Ljava/lang/String;")) {
            continue;
        }
        primary |= sam_member(machine, site, name, descriptor)?;
        if let Some(signature) = method.signature(pool)? {
            let signature = MethodSignature::parse(signature)?;
            if !signature.type_parameters.is_empty() || signature.throws.iter().any(|exception| !matches!(exception, crate::descriptor::GenericType::Class(_))) {
                return Err(machine.unsupported("anonymous SAM needs a generic method or throws declaration"));
            }
        }
        throws.push(method.exceptions(pool)?.into_iter().map(|index| {
            pool.class_name(index).map(|name| Type::Object(name.into()))
        }).collect::<Result<_, _>>()?);
    }
    Ok(primary)
}

fn sam_member(machine: &Machine<'_, '_>, site: &LambdaSite<'_>, name: &str, descriptor: &str) -> Result<bool, LiftError> {
    if name != site.sam_name || (descriptor != site.sam_descriptor && !site.bridges.contains(&descriptor)) {
        return Err(machine.unsupported("anonymous class cannot implement a separate abstract method at this lambda site"));
    }
    Ok(descriptor == site.sam_descriptor)
}

/// Validate standard bootstrap SAM descriptors without forcing runtime class
/// loading when the decompiler has no JDK image configured.
fn standard_sam(owner: &str) -> Option<(&'static str, &'static str, Option<&'static str>)> {
    let (name, desc, exception) = match owner {
        "java/lang/Runnable" => ("run", "()V", None),
        "java/util/Comparator" => ("compare", "(Ljava/lang/Object;Ljava/lang/Object;)I", None),
        "java/util/concurrent/Callable" => ("call", "()Ljava/lang/Object;", Some("java/lang/Exception")),
        "java/security/PrivilegedAction" => ("run", "()Ljava/lang/Object;", None),
        "java/security/PrivilegedExceptionAction" => ("run", "()Ljava/lang/Object;", Some("java/lang/Exception")),
        _ => {
            let (name, desc) = match owner.strip_prefix("java/util/function/")? {
                "Function" | "UnaryOperator" => ("apply", "(Ljava/lang/Object;)Ljava/lang/Object;"),
                "BiFunction" | "BinaryOperator" => ("apply", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
                "Consumer" => ("accept", "(Ljava/lang/Object;)V"),
                "BiConsumer" => ("accept", "(Ljava/lang/Object;Ljava/lang/Object;)V"),
                "Predicate" => ("test", "(Ljava/lang/Object;)Z"),
                "BiPredicate" => ("test", "(Ljava/lang/Object;Ljava/lang/Object;)Z"),
                "Supplier" => ("get", "()Ljava/lang/Object;"),
                "BooleanSupplier" => ("getAsBoolean", "()Z"),
                "IntSupplier" => ("getAsInt", "()I"),
                "LongSupplier" => ("getAsLong", "()J"),
                "DoubleSupplier" => ("getAsDouble", "()D"),
                "IntConsumer" => ("accept", "(I)V"),
                "LongConsumer" => ("accept", "(J)V"),
                "DoubleConsumer" => ("accept", "(D)V"),
                "ObjIntConsumer" => ("accept", "(Ljava/lang/Object;I)V"),
                "ObjLongConsumer" => ("accept", "(Ljava/lang/Object;J)V"),
                "ObjDoubleConsumer" => ("accept", "(Ljava/lang/Object;D)V"),
                "IntPredicate" => ("test", "(I)Z"),
                "LongPredicate" => ("test", "(J)Z"),
                "DoublePredicate" => ("test", "(D)Z"),
                "IntFunction" => ("apply", "(I)Ljava/lang/Object;"),
                "LongFunction" => ("apply", "(J)Ljava/lang/Object;"),
                "DoubleFunction" => ("apply", "(D)Ljava/lang/Object;"),
                "ToIntFunction" => ("applyAsInt", "(Ljava/lang/Object;)I"),
                "ToLongFunction" => ("applyAsLong", "(Ljava/lang/Object;)J"),
                "ToDoubleFunction" => ("applyAsDouble", "(Ljava/lang/Object;)D"),
                "ToIntBiFunction" => ("applyAsInt", "(Ljava/lang/Object;Ljava/lang/Object;)I"),
                "ToLongBiFunction" => ("applyAsLong", "(Ljava/lang/Object;Ljava/lang/Object;)J"),
                "ToDoubleBiFunction" => ("applyAsDouble", "(Ljava/lang/Object;Ljava/lang/Object;)D"),
                "IntUnaryOperator" => ("applyAsInt", "(I)I"),
                "LongUnaryOperator" => ("applyAsLong", "(J)J"),
                "DoubleUnaryOperator" => ("applyAsDouble", "(D)D"),
                "IntBinaryOperator" => ("applyAsInt", "(II)I"),
                "LongBinaryOperator" => ("applyAsLong", "(JJ)J"),
                "DoubleBinaryOperator" => ("applyAsDouble", "(DD)D"),
                "IntToLongFunction" => ("applyAsLong", "(I)J"),
                "IntToDoubleFunction" => ("applyAsDouble", "(I)D"),
                "LongToIntFunction" => ("applyAsInt", "(J)I"),
                "LongToDoubleFunction" => ("applyAsDouble", "(J)D"),
                "DoubleToIntFunction" => ("applyAsInt", "(D)I"),
                "DoubleToLongFunction" => ("applyAsLong", "(D)J"),
                _ => return None,
            };
            (name, desc, None)
        }
    };
    Some((name, desc, exception))
}
