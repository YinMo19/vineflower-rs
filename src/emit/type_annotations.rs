// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::HashMap;

use super::{DecompileError, Document, Writer, symbols};
use crate::{
    classfile::{Annotation, ClassError, ClassFile, TypeAnnotation, TypePathStep, TypeTarget},
    descriptor::{
        ClassSignature, ClassType, GenericType, NestedType, Type, TypeArgument, TypeParameter,
    },
};

/// An explicit, non-static membership edge adds one INNER_TYPE step. A `$` in
/// the binary name alone does not establish such an edge (e.g. Map.Entry).
#[derive(Default)]
pub(super) struct TypeNesting<'a> {
    members: HashMap<&'a str, (&'a str, &'a str)>,
}

impl<'a> TypeNesting<'a> {
    pub(super) fn new(class: &'a ClassFile<'_>) -> Result<Self, ClassError> {
        let pool = &class.pool;
        let mut members = HashMap::new();
        for inner in class.inner_classes()? {
            if inner.access_flags & 0x0008 == 0
                && inner.inner_class != 0
                && inner.outer_class != 0
                && inner.inner_name != 0
            {
                members.insert(
                    pool.class_name(inner.inner_class)?,
                    (
                        pool.class_name(inner.outer_class)?,
                        pool.utf8(inner.inner_name)?,
                    ),
                );
            }
        }
        Ok(Self { members })
    }
}

#[derive(Clone, Copy)]
pub(crate) enum RenderType<'a> {
    Erased(&'a Type),
    Generic(&'a GenericType),
}

impl<'a> From<&'a Type> for RenderType<'a> {
    fn from(ty: &'a Type) -> Self {
        Self::Erased(ty)
    }
}

impl<'a> From<&'a GenericType> for RenderType<'a> {
    fn from(ty: &'a GenericType) -> Self {
        Self::Generic(ty)
    }
}

impl RenderType<'_> {
    fn array_parts(mut self) -> (Self, usize) {
        let mut dimensions = 0;
        loop {
            match self {
                Self::Erased(Type::Array(element)) => {
                    self = Self::Erased(element);
                    dimensions += 1;
                }
                Self::Generic(GenericType::Array {
                    element,
                    dimensions: rank,
                }) => {
                    self = Self::Generic(element);
                    dimensions += usize::from(*rank);
                }
                _ => return (self, dimensions),
            }
        }
    }
}

/// Renders only the annotations selected by the caller's exact target match.
/// A path that does not exist on the supplied source type is not relocated to
/// another node (e.g. when only an erased descriptor can be recovered).
pub(super) fn render<'a, 'b, E>(
    nesting: &TypeNesting<'_>,
    ty: impl Into<RenderType<'a>>,
    annotations: impl IntoIterator<Item = &'b TypeAnnotation>,
    mut map_class: impl FnMut(&str) -> String,
    mut map_annotation: impl FnMut(&Annotation) -> Result<Document, E>,
    varargs: bool,
    marked: bool,
) -> Result<Document, E> {
    let ty = ty.into();
    let mut by_path = HashMap::<_, Vec<_>>::new();
    for annotation in annotations {
        by_path
            .entry(annotation.path.as_slice())
            .or_default()
            .push(&annotation.annotation);
    }
    if by_path.is_empty() && !varargs && !marked {
        return Ok(match ty {
            RenderType::Erased(ty) => ty.render(map_class),
            RenderType::Generic(ty) => ty.render(map_class),
        }
        .into());
    }
    let mut renderer = Renderer {
        nesting,
        by_path,
        map_class: &mut map_class,
        map_annotation: &mut map_annotation,
        path: Vec::new(),
        out: Document::new(),
        marked,
    };
    renderer.write_type(ty, varargs)?;
    Ok(renderer.out)
}

pub(crate) fn render_generic_type(
    ty: &GenericType,
    map_class: impl FnMut(&str) -> String,
    marked: bool,
) -> Document {
    if !marked {
        return ty.render(map_class).into();
    }
    render(&TypeNesting::default(), ty, [], map_class, |_| {
        Ok::<_, std::convert::Infallible>(Document::new())
    }, false, true).unwrap()
}

struct Renderer<'f, 'b, 'n, E> {
    nesting: &'f TypeNesting<'n>,
    by_path: HashMap<&'b [TypePathStep], Vec<&'b Annotation>>,
    map_class: &'f mut dyn FnMut(&str) -> String,
    map_annotation: &'f mut dyn FnMut(&Annotation) -> Result<Document, E>,
    path: Vec<TypePathStep>,
    out: Document,
    marked: bool,
}

impl<E> Renderer<'_, '_, '_, E> {
    fn write_annotations(&mut self, before_suffix: bool) -> Result<(), E> {
        if let Some(annotations) = self.by_path.get(self.path.as_slice()) {
            let mut needs_space = before_suffix;
            for annotation in annotations {
                let java = (self.map_annotation)(annotation)?;
                if java.is_empty() {
                    continue;
                }
                if needs_space {
                    self.out.push(' ');
                    needs_space = false;
                }
                self.out.append(java);
                self.out.push(' ');
            }
        }
        Ok(())
    }

    fn write_type(&mut self, ty: RenderType<'_>, varargs: bool) -> Result<(), E> {
        let (element, dimensions) = ty.array_parts();
        let root = self.path.len();
        self.path
            .resize(root + dimensions, TypePathStep::ArrayElement);
        match element {
            RenderType::Erased(Type::Object(name)) => self.write_class(name, &[], &[])?,
            RenderType::Generic(GenericType::Class(class)) => {
                self.write_class(&class.internal_name, &class.arguments, &class.nested)?;
            }
            _ => {
                self.write_annotations(false)?;
                self.out.push_str(match element {
                    RenderType::Erased(Type::Primitive(primitive))
                    | RenderType::Generic(GenericType::Primitive(primitive)) => {
                        primitive.java_name()
                    }
                    RenderType::Erased(Type::Void) | RenderType::Generic(GenericType::Void) => {
                        "void"
                    }
                    RenderType::Generic(GenericType::Variable(name)) => name,
                    _ => unreachable!("array_parts returns the non-array element"),
                });
            }
        }
        self.path.truncate(root);
        for i in 0..dimensions {
            self.write_annotations(true)?;
            self.out.push_str(if varargs && i + 1 == dimensions {
                "..."
            } else {
                "[]"
            });
            self.path.push(TypePathStep::ArrayElement);
        }
        self.path.truncate(root);
        Ok(())
    }

    fn write_class(
        &mut self,
        name: &str,
        arguments: &[TypeArgument],
        nested: &[NestedType],
    ) -> Result<(), E> {
        let root = self.path.len();
        let mut base = name;
        let mut implicit = Vec::new();
        if !self.by_path.is_empty() {
            while let Some(&(outer, simple)) = self.nesting.members.get(base) {
                if implicit.len() == self.nesting.members.len() {
                    // A malformed cyclic InnerClasses graph is not a usable path.
                    implicit.clear();
                    base = name;
                    break;
                }
                implicit.push((base, simple));
                base = outer;
            }
        }
        let mapped = (self.map_class)(base);
        // A package or static qualifier comes before the actual type-use node:
        // pkg.Outer.@A Static is legal Java; @A pkg.Outer.Static is not.
        let leaf_start = mapped.rfind('.').map_or(0, |dot| dot + 1);
        if self.by_path.contains_key(self.path.as_slice()) {
            self.out.push_str(&mapped[..leaf_start]);
            if self.marked
                && leaf_start != 0
                && let Some((parent, _)) = base.rsplit_once('$')
            {
                let qualifier = &mapped[..leaf_start - 1];
                let package = base.rsplit_once('/').map_or("", |(package, _)| package);
                if qualifier.bytes().ne(package
                    .bytes()
                    .map(|byte| if byte == b'/' { b'.' } else { byte }))
                {
                    let start = self.out.len() - leaf_start;
                    symbols::class_ranges(&mut self.out, start, qualifier, parent);
                }
            }
            self.write_annotations(false)?;
            symbols::append_class(&mut self.out, &mapped[leaf_start..], base, self.marked);
        } else {
            symbols::append_class(&mut self.out, &mapped, base, self.marked);
        }
        for (owner, simple) in implicit.into_iter().rev() {
            self.write_nested(simple, owner)?;
        }
        self.write_arguments(arguments)?;
        let mut owner = self.marked.then(|| name.to_owned());
        for part in nested {
            if let Some(owner) = &mut owner {
                owner.push('$');
                owner.push_str(&part.name);
            }
            self.write_nested(&part.name, owner.as_deref().unwrap_or(""))?;
            self.write_arguments(&part.arguments)?;
        }
        self.path.truncate(root);
        Ok(())
    }

    fn write_nested(&mut self, name: &str, owner: &str) -> Result<(), E> {
        self.out.push('.');
        self.path.push(TypePathStep::NestedType);
        self.write_annotations(false)?;
        symbols::append_class(&mut self.out, name, owner, self.marked);
        Ok(())
    }

    fn write_arguments(&mut self, arguments: &[TypeArgument]) -> Result<(), E> {
        if arguments.is_empty() {
            return Ok(());
        }
        self.out.push('<');
        for (index, argument) in arguments.iter().enumerate() {
            if index != 0 {
                self.out.push_str(", ");
            }
            let root = self.path.len();
            // Arguments after 255 cannot be identified by type_path. Suppress
            // lookup at their nodes instead of aliasing an earlier argument.
            if let Ok(index) = u8::try_from(index) {
                self.path.push(TypePathStep::TypeArgument(index));
            } else {
                self.path
                    .resize((root + 1).max(256), TypePathStep::ArrayElement);
            }
            match argument {
                TypeArgument::Exact(ty) => self.write_type(ty.into(), false)?,
                TypeArgument::Any => {
                    self.write_annotations(false)?;
                    self.out.push('?');
                }
                TypeArgument::Extends(ty) | TypeArgument::Super(ty) => {
                    self.write_annotations(false)?;
                    self.out
                        .push_str(if matches!(argument, TypeArgument::Extends(_)) {
                            "? extends "
                        } else {
                            "? super "
                        });
                    self.path.push(TypePathStep::WildcardBound);
                    self.write_type(ty.into(), false)?;
                }
            }
            self.path.truncate(root);
        }
        self.out.push('>');
        Ok(())
    }
}

impl Writer<'_, '_> {
    pub(super) fn render_type_target<'a>(
        &self,
        ty: impl Into<RenderType<'a>>,
        annotations: &[TypeAnnotation],
        target: TypeTarget,
        declarations: &[Annotation],
        varargs: bool,
    ) -> Result<Document, DecompileError> {
        render(
            &self.type_nesting,
            ty,
            annotations.iter().filter(|annotation| {
                annotation.target == target
                    && (!annotation.path.is_empty()
                        || !declarations.contains(&annotation.annotation))
            }),
            |name| self.names.render(name),
            |annotation| self.annotation_document(annotation, None),
            varargs,
            self.options.dump_text_tokens,
        )
    }

    pub(super) fn type_parameters(
        &self,
        output: &mut Document,
        parameters: &[TypeParameter],
        annotations: &[TypeAnnotation],
        target: impl Fn(u8) -> TypeTarget,
    ) -> Result<(), DecompileError> {
        if parameters.is_empty() {
            return Ok(());
        }
        output.push('<');
        for (index, parameter) in parameters.iter().enumerate() {
            if index != 0 {
                output.push_str(", ");
            }
            let index = u8::try_from(index)
                .map_err(|_| DecompileError::InvalidAttribute("annotated type parameter count"))?;
            output.append(self.render_annotated_type_parameter(
                &self.type_nesting,
                parameter,
                target(index),
                annotations,
            )?);
        }
        output.push('>');
        Ok(())
    }

    pub(super) fn annotated_receiver(
        &self,
        annotations: &[TypeAnnotation],
        constructor: bool,
    ) -> Result<Option<Document>, DecompileError> {
        let target = TypeTarget::MethodReceiver;
        if !annotations
            .iter()
            .any(|annotation| annotation.target == target)
        {
            return Ok(None);
        }
        let unsupported = || DecompileError::Unsupported {
            feature: "annotated constructor receiver without enclosing member class",
        };
        let qualified = if constructor {
            let member = self
                .group
                .member_class(self.owner)
                .ok_or_else(unsupported)?;
            if member.access_flags & super::STATIC != 0 {
                return Err(unsupported());
            }
            Some(member.outer)
        } else {
            None
        };
        let receiver = qualified.unwrap_or(self.owner);
        let mut owner = receiver;
        let mut nested = Vec::new();
        let arguments = |owner| -> Result<Vec<TypeArgument>, DecompileError> {
            if !self.options.decompile_generics {
                return Ok(Vec::new());
            }
            let Some(class) = self.group.get(owner) else {
                return Ok(Vec::new());
            };
            let Some(signature) = class.signature()? else {
                return Ok(Vec::new());
            };
            let signature = super::parse(signature, ClassSignature::parse)?;
            Ok(signature
                .type_parameters
                .into_iter()
                .map(|parameter| TypeArgument::Exact(GenericType::Variable(parameter.name)))
                .collect())
        };
        while let Some(member) = self.group.member_class(owner) {
            if member.access_flags & super::STATIC != 0 {
                break;
            }
            nested.push(NestedType {
                name: member.simple_name.into(),
                arguments: arguments(owner)?,
            });
            owner = member.outer;
        }
        nested.reverse();
        let ty = GenericType::Class(ClassType {
            internal_name: owner.into(),
            arguments: arguments(owner)?,
            nested,
        });
        let mut value = self.render_type_target(&ty, annotations, target, &[], false)?;
        if let Some(outer) = qualified {
            let name = self
                .group
                .member_class(outer)
                .map_or(super::simple(outer), |outer| outer.simple_name);
            value.push(' ');
            value.push_str(name);
            value.push_str(".this");
        } else {
            value.push_str(" this");
        }
        Ok(Some(value))
    }

    pub(super) fn render_annotated_type_parameter(
        &self,
        nesting: &TypeNesting<'_>,
        parameter: &TypeParameter,
        target: TypeTarget,
        annotations: &[TypeAnnotation],
    ) -> Result<Document, DecompileError> {
        render_parameter(
            nesting,
            parameter,
            target,
            annotations,
            |name| self.names.render(name),
            |annotation| self.annotation_document(annotation, None),
            self.options.dump_text_tokens,
        )
    }
}

/// Renders one class/method type parameter, including annotations on the
/// declaration and bounds. JVMS bound 0 is reserved for the class bound, even
/// when the signature starts with an interface bound and omits that class bound.
pub(super) fn render_parameter<E>(
    nesting: &TypeNesting<'_>,
    parameter: &TypeParameter,
    target: TypeTarget,
    annotations: &[TypeAnnotation],
    mut map_class: impl FnMut(&str) -> String,
    mut map_annotation: impl FnMut(&Annotation) -> Result<Document, E>,
    marked: bool,
) -> Result<Document, E> {
    let bound_target = |bound| match target {
        TypeTarget::ClassTypeParameter(parameter) => {
            Some(TypeTarget::ClassTypeParameterBound { parameter, bound })
        }
        TypeTarget::MethodTypeParameter(parameter) => {
            Some(TypeTarget::MethodTypeParameterBound { parameter, bound })
        }
        _ => None,
    };
    let mut out = Document::new();
    for annotation in annotations
        .iter()
        .filter(|a| a.target == target && a.path.is_empty())
    {
        let java = map_annotation(&annotation.annotation)?;
        if !java.is_empty() {
            out.append(java);
            out.push(' ');
        }
    }
    out.push_str(&parameter.name);
    let mut separator = " extends ";
    for (index, bound) in std::iter::once(parameter.class_bound.as_ref())
        .chain(parameter.interface_bounds.iter().map(Some))
        .enumerate()
    {
        let Some(bound) = bound else { continue };
        let target = u8::try_from(index).ok().and_then(bound_target);
        let mut selected = annotations
            .iter()
            .filter(|a| target.as_ref() == Some(&a.target))
            .peekable();
        if index == 0
            && bound.is_java_lang_object()
            && parameter.interface_bounds.is_empty()
            && selected.peek().is_none()
        {
            continue;
        }
        out.push_str(separator);
        out.append(render(
            nesting,
            bound,
            selected,
            &mut map_class,
            &mut map_annotation,
            false,
            marked,
        )?);
        separator = " & ";
    }
    Ok(out)
}
