// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Native Kotlin language selection and declaration recovery for JVM class files.
//! Metadata supplies source declarations and JVM member identities; bytecode,
//! not Java source rendering, supplies the implementations.

mod body;
mod emit;
mod metadata;
mod model;
mod names;
mod proto;
mod syntax;
#[cfg(test)]
mod tests;
pub use metadata::{Metadata, MetadataHeader, has_metadata, read_metadata};
pub use model::{
    ClassDeclaration, ClassKind, ClassName, Classifier, Constructor, Declaration, Flags, Function,
    JvmFieldSignature, JvmMethodSignature, JvmPropertySignature, MemberKind, Modality,
    PackageDeclaration, Property, Type, TypeAlias, TypeArgument, TypeParameter, ValueParameter,
    Variance, Visibility,
};

use crate::{
    Options,
    bytecode::BytecodeError,
    classfile::{ClassError, ClassFile},
    context::ClassGroup,
    descriptor::DescriptorError,
    emit::SourceMap,
};

#[derive(Debug, thiserror::Error)]
pub enum KotlinError {
    #[error(transparent)]
    Class(#[from] ClassError),
    #[error("invalid Kotlin metadata protobuf: {0}")]
    Protobuf(#[from] prost::DecodeError),
    #[error("invalid JVM descriptor in Kotlin declaration: {0}")]
    Descriptor(#[from] DescriptorError),
    #[error("invalid Kotlin bytecode: {0}")]
    Bytecode(#[from] BytecodeError),
    #[error("invalid Kotlin metadata: {0}")]
    Metadata(&'static str),
    #[error("unsupported Kotlin metadata version {0:?}")]
    Version(Vec<i32>),
    #[error("unsupported Kotlin declaration {declaration}: {feature}")]
    Unsupported {
        declaration: String,
        feature: &'static str,
    },
}

impl KotlinError {
    fn unsupported(declaration: &str, feature: &'static str) -> Self {
        Self::Unsupported {
            declaration: declaration.to_owned(),
            feature,
        }
    }
}

/// Decompile a class selected by its `kotlin.Metadata` annotation. `None`
/// means the class is not Kotlin, never that Kotlin parsing or rendering failed.
pub fn decompile_class(class: &ClassFile<'_>) -> Result<Option<String>, KotlinError> {
    read_metadata(class)?
        .map(|metadata| emit::render(class, &metadata, None, None).map(|(text, _)| text))
        .transpose()
}

pub(crate) fn decompile_with_options(
    class: &ClassFile<'_>,
    group: &ClassGroup<'_>,
    options: &Options,
) -> Result<Option<(String, Option<SourceMap>)>, KotlinError> {
    read_metadata(class)?
        .map(|metadata| emit::render(class, &metadata, Some(group), Some(options)))
        .transpose()
}
