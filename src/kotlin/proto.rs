// Copyright 2010-2025 JetBrains s.r.o. and Kotlin Programming Language contributors.
// Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! JVM projection of Kotlin 2.2's `metadata.proto` and `jvm_metadata.proto`.
//! JVM extensions have ordinary wire tags; prost skips fields not used by the
//! declaration reader. Required name indices are optional here so absence can
//! be distinguished from the valid string-table index zero.

use prost::Message;

#[derive(Message)]
pub(super) struct StringTableTypes {
    #[prost(message, repeated, tag = "1")]
    pub records: Vec<StringRecord>,
    #[prost(int32, repeated, packed = "true", tag = "5")]
    pub local_names: Vec<i32>,
}

#[derive(Message)]
pub(super) struct StringRecord {
    #[prost(int32, optional, tag = "1")]
    pub range: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub predefined_index: Option<i32>,
    #[prost(int32, optional, tag = "3")]
    pub operation: Option<i32>,
    #[prost(int32, repeated, packed = "true", tag = "4")]
    pub substring: Vec<i32>,
    #[prost(int32, repeated, packed = "true", tag = "5")]
    pub replace: Vec<i32>,
    #[prost(string, optional, tag = "6")]
    pub string: Option<String>,
}

#[derive(Message)]
pub(super) struct JvmSignature {
    #[prost(int32, optional, tag = "1")]
    pub name: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub descriptor: Option<i32>,
}

#[derive(Message)]
pub(super) struct JvmPropertySignature {
    #[prost(message, optional, tag = "1")]
    pub field: Option<JvmSignature>,
    #[prost(message, optional, tag = "2")]
    pub annotations_method: Option<JvmSignature>,
    #[prost(message, optional, tag = "3")]
    pub getter: Option<JvmSignature>,
    #[prost(message, optional, tag = "4")]
    pub setter: Option<JvmSignature>,
    #[prost(message, optional, tag = "5")]
    pub delegate_method: Option<JvmSignature>,
}

#[derive(Message)]
pub(super) struct Type {
    #[prost(int32, optional, tag = "1")]
    pub flags: Option<i32>,
    #[prost(message, repeated, tag = "2")]
    pub arguments: Vec<TypeArgument>,
    #[prost(bool, optional, tag = "3")]
    pub nullable: Option<bool>,
    #[prost(int32, optional, tag = "4")]
    pub flexible_capabilities: Option<i32>,
    #[prost(message, optional, boxed, tag = "5")]
    pub flexible_upper: Option<Box<Type>>,
    #[prost(int32, optional, tag = "6")]
    pub class_name: Option<i32>,
    #[prost(int32, optional, tag = "7")]
    pub type_parameter: Option<i32>,
    #[prost(int32, optional, tag = "8")]
    pub flexible_upper_id: Option<i32>,
    #[prost(int32, optional, tag = "9")]
    pub type_parameter_name: Option<i32>,
    #[prost(message, optional, boxed, tag = "10")]
    pub outer: Option<Box<Type>>,
    #[prost(int32, optional, tag = "11")]
    pub outer_id: Option<i32>,
    #[prost(int32, optional, tag = "12")]
    pub type_alias_name: Option<i32>,
    #[prost(message, optional, boxed, tag = "13")]
    pub abbreviated: Option<Box<Type>>,
    #[prost(int32, optional, tag = "14")]
    pub abbreviated_id: Option<i32>,
    #[prost(message, repeated, tag = "100")]
    pub annotations: Vec<Annotation>,
    #[prost(bool, optional, tag = "101")]
    pub raw: Option<bool>,
}

#[derive(Message)]
pub(super) struct Annotation {
    #[prost(int32, optional, tag = "1")]
    pub id: Option<i32>,
    #[prost(bytes = "vec", repeated, tag = "2")]
    pub arguments: Vec<Vec<u8>>,
}

#[derive(Message)]
pub(super) struct TypeArgument {
    #[prost(int32, optional, tag = "1")]
    pub projection: Option<i32>,
    #[prost(message, optional, tag = "2")]
    pub ty: Option<Type>,
    #[prost(int32, optional, tag = "3")]
    pub type_id: Option<i32>,
}

#[derive(Message)]
pub(super) struct TypeParameter {
    #[prost(int32, optional, tag = "1")]
    pub id: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub name: Option<i32>,
    #[prost(bool, optional, tag = "3")]
    pub reified: Option<bool>,
    #[prost(int32, optional, tag = "4")]
    pub variance: Option<i32>,
    #[prost(message, repeated, tag = "5")]
    pub upper_bounds: Vec<Type>,
    #[prost(int32, repeated, packed = "true", tag = "6")]
    pub upper_bound_ids: Vec<i32>,
    #[prost(message, repeated, tag = "100")]
    pub annotations: Vec<Annotation>,
}

#[derive(Message)]
pub(super) struct TypeTable {
    #[prost(message, repeated, tag = "1")]
    pub types: Vec<Type>,
    #[prost(int32, optional, tag = "2")]
    pub first_nullable: Option<i32>,
}

#[derive(Message)]
pub(super) struct ValueParameter {
    #[prost(int32, optional, tag = "1")]
    pub flags: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub name: Option<i32>,
    #[prost(message, optional, tag = "3")]
    pub ty: Option<Type>,
    #[prost(message, optional, tag = "4")]
    pub vararg_element: Option<Type>,
    #[prost(int32, optional, tag = "5")]
    pub type_id: Option<i32>,
    #[prost(int32, optional, tag = "6")]
    pub vararg_element_id: Option<i32>,
}

#[derive(Message)]
pub(super) struct Constructor {
    #[prost(int32, optional, tag = "1")]
    pub flags: Option<i32>,
    #[prost(message, repeated, tag = "2")]
    pub parameters: Vec<ValueParameter>,
    #[prost(message, optional, tag = "100")]
    pub signature: Option<JvmSignature>,
}

#[derive(Message)]
pub(super) struct Function {
    #[prost(int32, optional, tag = "1")]
    pub old_flags: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub name: Option<i32>,
    #[prost(message, optional, tag = "3")]
    pub returns: Option<Type>,
    #[prost(message, repeated, tag = "4")]
    pub type_parameters: Vec<TypeParameter>,
    #[prost(message, optional, tag = "5")]
    pub receiver: Option<Type>,
    #[prost(message, repeated, tag = "6")]
    pub parameters: Vec<ValueParameter>,
    #[prost(int32, optional, tag = "7")]
    pub returns_id: Option<i32>,
    #[prost(int32, optional, tag = "8")]
    pub receiver_id: Option<i32>,
    #[prost(int32, optional, tag = "9")]
    pub flags: Option<i32>,
    #[prost(message, repeated, tag = "10")]
    pub context_receivers: Vec<Type>,
    #[prost(int32, repeated, packed = "true", tag = "11")]
    pub context_receiver_ids: Vec<i32>,
    #[prost(message, repeated, tag = "13")]
    pub context_parameters: Vec<ValueParameter>,
    #[prost(message, optional, tag = "30")]
    pub type_table: Option<TypeTable>,
    #[prost(bytes = "vec", optional, tag = "32")]
    pub contract: Option<Vec<u8>>,
    #[prost(message, optional, tag = "100")]
    pub signature: Option<JvmSignature>,
}

#[derive(Message)]
pub(super) struct Property {
    #[prost(int32, optional, tag = "1")]
    pub old_flags: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub name: Option<i32>,
    #[prost(message, optional, tag = "3")]
    pub ty: Option<Type>,
    #[prost(message, repeated, tag = "4")]
    pub type_parameters: Vec<TypeParameter>,
    #[prost(message, optional, tag = "5")]
    pub receiver: Option<Type>,
    #[prost(message, optional, tag = "6")]
    pub setter_parameter: Option<ValueParameter>,
    #[prost(int32, optional, tag = "7")]
    pub getter_flags: Option<i32>,
    #[prost(int32, optional, tag = "8")]
    pub setter_flags: Option<i32>,
    #[prost(int32, optional, tag = "9")]
    pub type_id: Option<i32>,
    #[prost(int32, optional, tag = "10")]
    pub receiver_id: Option<i32>,
    #[prost(int32, optional, tag = "11")]
    pub flags: Option<i32>,
    #[prost(message, repeated, tag = "12")]
    pub context_receivers: Vec<Type>,
    #[prost(int32, repeated, packed = "true", tag = "13")]
    pub context_receiver_ids: Vec<i32>,
    #[prost(message, repeated, tag = "17")]
    pub context_parameters: Vec<ValueParameter>,
    #[prost(message, optional, tag = "100")]
    pub signature: Option<JvmPropertySignature>,
    #[prost(int32, optional, tag = "101")]
    pub jvm_flags: Option<i32>,
}

#[derive(Message)]
pub(super) struct TypeAlias {
    #[prost(int32, optional, tag = "1")]
    pub flags: Option<i32>,
    #[prost(int32, optional, tag = "2")]
    pub name: Option<i32>,
    #[prost(message, repeated, tag = "3")]
    pub type_parameters: Vec<TypeParameter>,
    #[prost(message, optional, tag = "4")]
    pub underlying: Option<Type>,
    #[prost(int32, optional, tag = "5")]
    pub underlying_id: Option<i32>,
    #[prost(message, optional, tag = "6")]
    pub expanded: Option<Type>,
    #[prost(int32, optional, tag = "7")]
    pub expanded_id: Option<i32>,
}

#[derive(Message)]
pub(super) struct EnumEntry {
    #[prost(int32, optional, tag = "1")]
    pub name: Option<i32>,
}

#[derive(Message)]
pub(super) struct Class {
    #[prost(int32, optional, tag = "1")]
    pub flags: Option<i32>,
    #[prost(int32, repeated, packed = "true", tag = "2")]
    pub supertype_ids: Vec<i32>,
    #[prost(int32, optional, tag = "3")]
    pub name: Option<i32>,
    #[prost(int32, optional, tag = "4")]
    pub companion_name: Option<i32>,
    #[prost(message, repeated, tag = "5")]
    pub type_parameters: Vec<TypeParameter>,
    #[prost(message, repeated, tag = "6")]
    pub supertypes: Vec<Type>,
    #[prost(int32, repeated, packed = "true", tag = "7")]
    pub nested_names: Vec<i32>,
    #[prost(message, repeated, tag = "8")]
    pub constructors: Vec<Constructor>,
    #[prost(message, repeated, tag = "9")]
    pub functions: Vec<Function>,
    #[prost(message, repeated, tag = "10")]
    pub properties: Vec<Property>,
    #[prost(message, repeated, tag = "11")]
    pub type_aliases: Vec<TypeAlias>,
    #[prost(message, repeated, tag = "13")]
    pub enum_entries: Vec<EnumEntry>,
    #[prost(message, repeated, tag = "20")]
    pub context_receivers: Vec<Type>,
    #[prost(int32, repeated, packed = "true", tag = "21")]
    pub context_receiver_ids: Vec<i32>,
    #[prost(message, optional, tag = "30")]
    pub type_table: Option<TypeTable>,
}

#[derive(Message)]
pub(super) struct Package {
    #[prost(message, repeated, tag = "3")]
    pub functions: Vec<Function>,
    #[prost(message, repeated, tag = "4")]
    pub properties: Vec<Property>,
    #[prost(message, repeated, tag = "5")]
    pub type_aliases: Vec<TypeAlias>,
    #[prost(message, optional, tag = "30")]
    pub type_table: Option<TypeTable>,
}
