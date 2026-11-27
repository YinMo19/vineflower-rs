//! Upstream's `struct.gen` packages: JVM types, descriptors and generic
//! signatures.

pub mod data_point;
pub mod descriptors;
pub mod generic_main;
pub mod generic_type;
pub mod var_type;

pub use descriptors::{FieldDescriptor, MethodDescriptor, NewClassNameBuilder};
pub use generic_main::{
    GenericClassDescriptor, GenericFieldDescriptor, GenericMethodDescriptor, GenericsChecker,
    SharedSignature,
};
pub use generic_type::{GenericType, GenericsMap, NamedGenerics};
pub use var_type::{CodeType, TypeFamily, VarType};
