// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::descriptor::{MethodDescriptor, Type as JvmType};

use super::KotlinError;

/// A Kotlin metadata class ID: package components use `/` and nested classes use `.`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassName {
    pub id: String,
    pub local: bool,
}

impl ClassName {
    pub fn package(&self) -> &str {
        self.id.rsplit_once('/').map_or("", |(package, _)| package)
    }

    pub fn relative_name(&self) -> &str {
        self.id.rsplit('/').next().unwrap_or_default()
    }

    pub fn jvm_internal_name(&self) -> String {
        self.id.replace('.', "$")
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassKind {
    Class,
    Interface,
    EnumClass,
    EnumEntry,
    Annotation,
    Object,
    CompanionObject,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Visibility {
    Internal,
    Private,
    Protected,
    Public,
    PrivateToThis,
    Local,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Modality {
    Final,
    Open,
    Abstract,
    Sealed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemberKind {
    Declaration,
    FakeOverride,
    Delegation,
    Synthesized,
}

/// The flag word as defined by the Kotlin metadata schema. Kind-specific flags
/// share bit positions and must be interpreted in the owning declaration kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Flags(pub u32);

impl Flags {
    pub fn has(self, bit: u32) -> bool {
        self.0 & (1 << bit) != 0
    }

    pub fn has_annotations(self) -> bool {
        self.has(0)
    }

    pub fn visibility(self) -> Result<Visibility, KotlinError> {
        Ok(match (self.0 >> 1) & 7 {
            0 => Visibility::Internal,
            1 => Visibility::Private,
            2 => Visibility::Protected,
            3 => Visibility::Public,
            4 => Visibility::PrivateToThis,
            5 => Visibility::Local,
            _ => return Err(KotlinError::Metadata("invalid declaration visibility")),
        })
    }

    pub fn modality(self) -> Modality {
        match (self.0 >> 4) & 3 {
            0 => Modality::Final,
            1 => Modality::Open,
            2 => Modality::Abstract,
            _ => Modality::Sealed,
        }
    }

    pub fn member_kind(self) -> MemberKind {
        match (self.0 >> 6) & 3 {
            0 => MemberKind::Declaration,
            1 => MemberKind::FakeOverride,
            2 => MemberKind::Delegation,
            _ => MemberKind::Synthesized,
        }
    }

    pub(super) fn class_kind(self) -> Result<ClassKind, KotlinError> {
        Ok(match (self.0 >> 6) & 7 {
            0 => ClassKind::Class,
            1 => ClassKind::Interface,
            2 => ClassKind::EnumClass,
            3 => ClassKind::EnumEntry,
            4 => ClassKind::Annotation,
            5 => ClassKind::Object,
            6 => ClassKind::CompanionObject,
            _ => return Err(KotlinError::Metadata("invalid class kind")),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Classifier {
    Class(ClassName),
    TypeParameter(i32),
    TypeParameterName(String),
    TypeAlias(ClassName),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Variance {
    In,
    Out,
    Invariant,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeArgument {
    Star,
    Type(Variance, Type),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Type {
    pub classifier: Classifier,
    pub arguments: Vec<TypeArgument>,
    pub nullable: bool,
    pub suspend: bool,
    pub definitely_not_null: bool,
    pub outer: Option<Box<Type>>,
    pub abbreviated: Option<Box<Type>>,
    pub flexible: Option<(String, Box<Type>)>,
    pub raw: bool,
    pub annotations: Vec<ClassName>,
}

impl Type {
    pub(super) fn class_id(&self) -> Option<&str> {
        match &self.classifier {
            Classifier::Class(name) => Some(&name.id),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeParameter {
    pub id: i32,
    pub name: String,
    pub variance: Variance,
    pub reified: bool,
    pub upper_bounds: Vec<Type>,
    pub annotations: Vec<ClassName>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueParameter {
    pub name: String,
    pub ty: Type,
    pub vararg_element: Option<Type>,
    pub flags: Flags,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JvmMethodSignature {
    pub name: String,
    pub descriptor: MethodDescriptor,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JvmFieldSignature {
    pub name: String,
    pub descriptor: JvmType,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct JvmPropertySignature {
    pub field: Option<JvmFieldSignature>,
    pub getter: Option<JvmMethodSignature>,
    pub setter: Option<JvmMethodSignature>,
    pub annotations_method: Option<JvmMethodSignature>,
    pub delegate_method: Option<JvmMethodSignature>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Property {
    pub name: String,
    pub ty: Type,
    pub type_parameters: Vec<TypeParameter>,
    pub receiver: Option<Type>,
    pub context_receivers: Vec<Type>,
    pub context_parameters: Vec<ValueParameter>,
    pub setter_parameter: Option<ValueParameter>,
    pub flags: Flags,
    pub getter_flags: Option<Flags>,
    pub setter_flags: Option<Flags>,
    pub signature: JvmPropertySignature,
    pub jvm_flags: u32,
}

impl Property {
    pub fn mutable(&self) -> bool {
        self.flags.has(8)
    }
    pub fn constant(&self) -> bool {
        self.flags.has(11)
    }
    pub fn late_init(&self) -> bool {
        self.flags.has(12)
    }
    pub fn delegated(&self) -> bool {
        self.flags.has(15)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub name: String,
    pub returns: Type,
    pub type_parameters: Vec<TypeParameter>,
    pub parameters: Vec<ValueParameter>,
    pub receiver: Option<Type>,
    pub context_receivers: Vec<Type>,
    pub context_parameters: Vec<ValueParameter>,
    pub flags: Flags,
    pub signature: Option<JvmMethodSignature>,
    pub has_contract: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constructor {
    pub parameters: Vec<ValueParameter>,
    pub flags: Flags,
    pub signature: Option<JvmMethodSignature>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAlias {
    pub name: String,
    pub flags: Flags,
    pub type_parameters: Vec<TypeParameter>,
    pub underlying: Type,
    pub expanded: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassDeclaration {
    pub name: ClassName,
    pub kind: ClassKind,
    pub flags: Flags,
    pub companion_name: Option<String>,
    pub nested_names: Vec<String>,
    pub enum_entries: Vec<String>,
    pub supertypes: Vec<Type>,
    pub context_receivers: Vec<Type>,
    pub type_parameters: Vec<TypeParameter>,
    pub constructors: Vec<Constructor>,
    pub members: PackageDeclaration,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageDeclaration {
    pub properties: Vec<Property>,
    pub functions: Vec<Function>,
    pub type_aliases: Vec<TypeAlias>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Declaration {
    Class(ClassDeclaration),
    FileFacade(PackageDeclaration),
    Synthetic(Option<Box<Function>>),
    MultifileFacade(Vec<String>),
    MultifilePart(PackageDeclaration),
}
