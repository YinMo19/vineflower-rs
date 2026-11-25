// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.attr`: the class-file attributes the decompiler understands. Each
//! type's `read` is upstream's `initContent`.
//!
//! Upstream parses annotations straight into expression objects. Expressions
//! belong to the class being decompiled here, so an annotation is loaded as
//! plain data ([`AnnotationData`], [`ElementValue`]) holding exactly what
//! upstream's constructors receive, and becomes an expression when written.

use std::cmp::Ordering;
use std::fmt;
use std::io;

use arcstr::ArcStr;

use super::consts::{ConstantPool, ConstantValue, LinkConstant, PooledConstant};
use super::struct_field::StructRecordComponent;
use super::struct_member::{self, Attributes};
use crate::code::BytecodeVersion;
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::Options;
use crate::types::{CodeType, FieldDescriptor, VarType};
use crate::util::data_input::DataInputFullStream;
use crate::util::jhash::JHashMap;

type Input<'a, 'b> = &'a mut DataInputFullStream<'b>;

/// The name the constant pool has at `index`; fails where upstream would
/// dereference `null` or cast a member reference.
fn string_at(pool: &ConstantPool, index: i32) -> ArcStr {
    pool.get_primitive_constant(index)
        .unwrap()
        .get_string()
        .clone()
}

/// The name at `index`, where index zero stands for "none".
fn optional_string_at(pool: &ConstantPool, index: i32) -> Option<ArcStr> {
    (index != 0).then(|| string_at(pool, index))
}

fn read_list<T>(
    count: i32,
    mut read: impl FnMut() -> io::Result<T>,
) -> io::Result<Vec<T>> {
    (0..count).map(|_| read()).collect()
}

/// `StructGeneralAttribute` itself: an attribute without content, such as
/// `Synthetic` and `Deprecated`.
#[derive(Clone, Copy, Debug, Default)]
pub struct StructGeneralAttribute;

/*
  u2 max_stack;
  u2 max_locals;
  u4 code_length;
  u1 code[];
  u2 exception_table_length;
  exception_table[] {
     u2 start_pc;
     u2 end_pc;
     u2 handler_pc;
     u2 catch_type;
  };
  u2 attributes_count;
  attribute_info attributes[];
*/
pub struct StructCodeAttribute {
    pub local_variables: i32,
    /// The code length, the code, the number of exception handlers and the
    /// handlers, as `StructMethod` decodes them.
    pub code_and_exception_data: Vec<u8>,
    pub code_attributes: Box<Attributes>,
}

impl StructCodeAttribute {
    pub fn read(
        data: Input<'_, '_>,
        pool: &ConstantPool,
        version: BytecodeVersion,
        options: &Options,
    ) -> io::Result<Self> {
        // Pre-java oak class files have a u1 max stack, u1 max locals, and a u2 code length
        let predates_java = version.predates_java();
        data.discard(if predates_java { 1 } else { 2 })?;
        let local_variables = if predates_java {
            data.read_unsigned_byte()?
        } else {
            data.read_unsigned_short()?
        };
        let code_length = if predates_java {
            data.read_unsigned_short()?
        } else {
            data.read_int()?
        };
        let code_data = data.read(code_length)?;
        let exc_length = data.read_unsigned_short()?;
        let exception_data = data.read(exc_length * 8)?;

        let mut code_and_exception_data =
            Vec::with_capacity(code_data.len() + 6 + exception_data.len());
        code_and_exception_data.extend_from_slice(&code_length.to_be_bytes());
        code_and_exception_data.extend_from_slice(code_data);
        code_and_exception_data.extend_from_slice(&(exc_length as u16).to_be_bytes());
        code_and_exception_data.extend_from_slice(exception_data);

        Ok(Self {
            local_variables,
            code_and_exception_data,
            code_attributes: Box::new(struct_member::read_attributes(
                data, pool, true, version, options,
            )?),
        })
    }
}

/*
  u2 local_variable_table_length;
  local_variable {
    u2 start_pc;
    u2 length;
    u2 name_index;
    u2 descriptor_index;
    u2 index;
  }
*/
#[derive(Clone, Debug, Default)]
pub struct StructLocalVariableTableAttribute {
    local_variables: Vec<LocalVariable>,
}

impl StructLocalVariableTableAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let len = data.read_unsigned_short()?;
        let mut local_variables = read_list(len, || {
            let start_pc = data.read_unsigned_short()?;
            let length = data.read_unsigned_short()?;
            let name_index = data.read_unsigned_short()?;
            let descriptor_index = data.read_unsigned_short()?;
            let var_index = data.read_unsigned_short()?;
            Ok(LocalVariable::new(
                start_pc,
                length,
                string_at(pool, name_index),
                string_at(pool, descriptor_index),
                var_index,
            ))
        })?;
        local_variables.sort_by(LocalVariable::compare_to);
        version_variables(&mut local_variables);

        Ok(Self { local_variables })
    }

    pub fn add(&mut self, attr: StructLocalVariableTableAttribute) {
        self.local_variables.extend(attr.local_variables);
        version_variables(&mut self.local_variables);
    }

    pub fn get_name(&self, index: i32, visible_offset: i32) -> Option<&ArcStr> {
        self.matching_vars_at(index, visible_offset)
            .map(|var| &var.name)
            .next()
    }

    pub fn get_descriptor(&self, index: i32, visible_offset: i32) -> Option<&ArcStr> {
        self.matching_vars_at(index, visible_offset)
            .map(|var| &var.descriptor)
            .next()
    }

    /// `matchingVars(index, visibleOffset)`: the variables of a slot that are
    /// in scope at a bytecode offset.
    pub fn matching_vars_at(
        &self,
        index: i32,
        visible_offset: i32,
    ) -> impl Iterator<Item = &LocalVariable> {
        self.local_variables.iter().filter(move |var| {
            var.index == index
                && visible_offset >= var.start_pc
                && visible_offset < var.start_pc + var.length
        })
    }

    /// `matchingVars(index)`.
    pub fn matching_vars(&self, index: i32) -> impl Iterator<Item = &LocalVariable> {
        self.local_variables
            .iter()
            .filter(move |var| var.index == index)
    }

    pub fn get_range(&self, start: i32, end: i32) -> impl Iterator<Item = &LocalVariable> {
        self.local_variables
            .iter()
            .filter(move |var| var.get_start() >= start && var.get_end() <= end)
    }

    pub fn contains_name(&self, name: &str) -> bool {
        self.local_variables.iter().any(|var| *var.name == *name)
    }

    pub fn get_map_names(&self) -> JHashMap<VarVersionPair, ArcStr> {
        let mut names = JHashMap::new();
        for var in &self.local_variables {
            names.insert(var.version, var.name.clone());
        }
        names
    }

    pub fn get_variables(&self) -> impl Iterator<Item = &LocalVariable> {
        self.local_variables.iter()
    }

    pub fn merge_signatures(&mut self, lvtt: &StructLocalVariableTypeTableAttribute) {
        for ty in &lvtt.backing_attribute.local_variables {
            if let Some(var) = self
                .local_variables
                .iter_mut()
                .find(|var| var.compare_to(ty) == Ordering::Equal)
            {
                var.signature = Some(ty.descriptor.clone());
            }
        }
    }
}

/// Upstream means to number the variables of each slot, but its counter
/// never advances, so every variable is version one of its slot.
fn version_variables(vars: &mut [LocalVariable]) {
    for var in vars {
        var.version = VarVersionPair::new(var.index, 1);
    }
}

#[derive(Clone, Debug)]
pub struct LocalVariable {
    start_pc: i32,
    length: i32,
    name: ArcStr,
    descriptor: ArcStr,
    index: i32,
    signature: Option<ArcStr>,
    version: VarVersionPair,
}

impl LocalVariable {
    pub fn new(start_pc: i32, length: i32, name: ArcStr, descriptor: ArcStr, index: i32) -> Self {
        Self {
            start_pc,
            length,
            name,
            descriptor,
            index,
            signature: None,
            version: VarVersionPair::new(index, 0),
        }
    }

    pub fn compare_to(&self, other: &LocalVariable) -> Ordering {
        (self.index, self.start_pc, self.length).cmp(&(other.index, other.start_pc, other.length))
    }

    pub fn get_name(&self) -> &ArcStr {
        &self.name
    }

    pub fn get_descriptor(&self) -> &ArcStr {
        &self.descriptor
    }

    pub fn get_signature(&self) -> Option<&ArcStr> {
        self.signature.as_ref()
    }

    pub fn get_start(&self) -> i32 {
        self.start_pc
    }

    pub fn get_end(&self) -> i32 {
        self.start_pc + self.length
    }

    pub fn get_version(&self) -> VarVersionPair {
        self.version
    }

    pub fn get_var_type(&self) -> VarType {
        VarType::from_signature(&self.descriptor)
    }

    pub fn rename(&self, new_name: ArcStr) -> LocalVariable {
        LocalVariable {
            signature: self.signature.clone(),
            ..LocalVariable::new(
                self.start_pc,
                self.length,
                new_name,
                self.descriptor.clone(),
                self.index,
            )
        }
    }
}

impl fmt::Display for LocalVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "'({},{}-{}){}",
            self.index,
            self.start_pc,
            self.get_end(),
            self.descriptor
        )?;
        match &self.signature {
            Some(signature) => write!(f, "<{signature}> ")?,
            None => f.write_str(" ")?,
        }
        write!(f, "{}'", self.name)
    }
}

/*
  u2 local_variable_type_table_length;
    {   u2 start_pc;
        u2 length;
        u2 name_index;
        u2 signature_index;
        u2 index;
    } local_variable_type_table[local_variable_type_table_length];
*/
#[derive(Clone, Debug, Default)]
pub struct StructLocalVariableTypeTableAttribute {
    // store signature instead of descriptor
    pub backing_attribute: StructLocalVariableTableAttribute,
}

impl StructLocalVariableTypeTableAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        Ok(Self {
            backing_attribute: StructLocalVariableTableAttribute::read(data, pool)?,
        })
    }

    pub fn add(&mut self, attr: StructLocalVariableTypeTableAttribute) {
        self.backing_attribute.add(attr.backing_attribute);
    }

    pub fn get_signature(&self, index: i32, visible_offset: i32) -> Option<&ArcStr> {
        self.backing_attribute.get_descriptor(index, visible_offset)
    }
}

/// u2 line_number_table_length;
/// {  u2 start_pc;
///    u2 line_number;
/// } line_number_table[line_number_table_length];
#[derive(Clone, Debug, Default)]
pub struct StructLineNumberTableAttribute {
    /// Pairs of a bytecode offset and the source line that starts there.
    line_info: Vec<i32>,
}

impl StructLineNumberTableAttribute {
    pub fn read(data: Input<'_, '_>) -> io::Result<Self> {
        let len = data.read_unsigned_short()? * 2;
        Ok(Self {
            line_info: read_list(len, || data.read_unsigned_short())?,
        })
    }

    pub fn find_line_number(&self, pc: i32) -> i32 {
        self.line_info
            .chunks_exact(2)
            .rev()
            .find(|entry| pc >= entry[0])
            .map_or(-1, |entry| entry[1])
    }

    pub fn get_raw_data(&self) -> &[i32] {
        &self.line_info
    }
}

#[derive(Clone, Debug)]
pub struct StructGenericSignatureAttribute {
    pub signature: ArcStr,
}

impl StructGenericSignatureAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let index = data.read_unsigned_short()?;
        Ok(Self {
            signature: string_at(pool, index),
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StructConstantValueAttribute {
    pub index: i32,
}

impl StructConstantValueAttribute {
    pub fn read(data: Input<'_, '_>) -> io::Result<Self> {
        Ok(Self {
            index: data.read_unsigned_short()?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct StructExceptionsAttribute {
    pub throws_exceptions: Vec<i32>,
}

impl StructExceptionsAttribute {
    pub fn read(data: Input<'_, '_>) -> io::Result<Self> {
        let len = data.read_unsigned_short()?;
        Ok(Self {
            throws_exceptions: read_list(len, || data.read_unsigned_short())?,
        })
    }

    pub fn get_exc_classname(&self, index: usize, pool: &ConstantPool) -> ArcStr {
        string_at(pool, self.throws_exceptions[index])
    }
}

#[derive(Clone, Debug)]
pub struct InnerClassEntry {
    pub outer_name_idx: i32,
    pub simple_name_idx: i32,
    pub access_flags: i32,
    pub inner_name: ArcStr,
    pub enclosing_name: Option<ArcStr>,
    pub simple_name: Option<ArcStr>,
}

#[derive(Clone, Debug)]
pub struct StructInnerClassesAttribute {
    pub entries: Vec<InnerClassEntry>,
}

impl StructInnerClassesAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let len = data.read_unsigned_short()?;
        let entries = read_list(len, || {
            let inner_name_idx = data.read_unsigned_short()?;
            let outer_name_idx = data.read_unsigned_short()?;
            let simple_name_idx = data.read_unsigned_short()?;
            let access_flags = data.read_unsigned_short()?;

            Ok(InnerClassEntry {
                outer_name_idx,
                simple_name_idx,
                access_flags,
                inner_name: string_at(pool, inner_name_idx),
                enclosing_name: optional_string_at(pool, outer_name_idx),
                simple_name: optional_string_at(pool, simple_name_idx),
            })
        })?;
        Ok(Self { entries })
    }
}

#[derive(Clone, Debug)]
pub struct StructEnclosingMethodAttribute {
    pub class_name: ArcStr,
    pub method_name: Option<ArcStr>,
    pub method_descriptor: Option<ArcStr>,
}

impl StructEnclosingMethodAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let class_index = data.read_unsigned_short()?;
        let method_index = data.read_unsigned_short()?;

        let method = (method_index != 0).then(|| pool.get_link_constant(method_index).unwrap());
        let (method_name, method_descriptor) = method
            .map(|method| (method.elementname, method.descriptor))
            .unzip();
        Ok(Self {
            class_name: string_at(pool, class_index),
            method_name,
            method_descriptor,
        })
    }
}

#[derive(Clone, Debug, Default)]
pub struct StructBootstrapMethodsAttribute {
    pub method_refs: Vec<LinkConstant>,
    pub method_arguments: Vec<Vec<Option<PooledConstant>>>,
}

impl StructBootstrapMethodsAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let mut attribute = Self::default();

        let method_number = data.read_unsigned_short()?;
        for _ in 0..method_number {
            let bootstrap_method_ref = data.read_unsigned_short()?;
            let num_bootstrap_arguments = data.read_unsigned_short()?;

            let list_arguments = read_list(num_bootstrap_arguments, || {
                let bootstrap_argument_ref = data.read_unsigned_short()?;
                Ok(pool.get_constant(bootstrap_argument_ref).cloned())
            })?;

            attribute
                .method_refs
                .push(pool.get_link_constant(bootstrap_method_ref).unwrap());
            attribute.method_arguments.push(list_arguments);
        }

        Ok(attribute)
    }

    pub fn get_methods_number(&self) -> i32 {
        self.method_refs.len() as i32
    }

    pub fn get_method_reference(&self, index: i32) -> &LinkConstant {
        &self.method_refs[index as usize]
    }

    pub fn get_method_arguments(&self, index: i32) -> &[Option<PooledConstant>] {
        &self.method_arguments[index as usize]
    }
}

/*
  u1 parameters_count;
  {   u2 name_index;
      u2 access_flags;
  } parameters[parameters_count];
*/
#[derive(Clone, Debug)]
pub struct StructMethodParametersAttribute {
    pub entries: Vec<MethodParameterEntry>,
}

#[derive(Clone, Debug)]
pub struct MethodParameterEntry {
    pub name: Option<ArcStr>,
    pub access_flags: i32,
}

impl StructMethodParametersAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let len = data.read_unsigned_byte()?;
        let entries = read_list(len, || {
            let name_index = data.read_unsigned_short()?;
            let name = optional_string_at(pool, name_index);
            let access_flags = data.read_unsigned_short()?;
            Ok(MethodParameterEntry { name, access_flags })
        })?;
        Ok(Self { entries })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StructSourceFileAttribute {
    pub const_pool_index: i32,
}

impl StructSourceFileAttribute {
    pub fn read(data: Input<'_, '_>) -> io::Result<Self> {
        Ok(Self {
            const_pool_index: data.read_unsigned_short()?,
        })
    }

    pub fn get_source_file(&self, pool: &ConstantPool) -> ArcStr {
        string_at(pool, self.const_pool_index)
    }
}

pub struct StructRecordAttribute {
    pub components: Vec<StructRecordComponent>,
}

impl StructRecordAttribute {
    pub fn read(
        data: Input<'_, '_>,
        pool: &ConstantPool,
        version: BytecodeVersion,
        options: &Options,
    ) -> io::Result<Self> {
        let component_count = data.read_unsigned_short()?;
        Ok(Self {
            components: read_list(component_count, || {
                StructRecordComponent::create_record_component(data, pool, version, options)
            })?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct StructPermittedSubclassesAttribute {
    pub classes: Vec<ArcStr>,
}

impl StructPermittedSubclassesAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let count = data.read_unsigned_short()?;
        Ok(Self {
            classes: read_list(count, || Ok(string_at(pool, data.read_unsigned_short()?)))?,
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StructNestHostAttribute {
    pub const_pool_index: i32,
}

impl StructNestHostAttribute {
    pub fn read(data: Input<'_, '_>) -> io::Result<Self> {
        Ok(Self {
            const_pool_index: data.read_unsigned_short()?,
        })
    }

    pub fn get_host_class(&self, pool: &ConstantPool) -> ArcStr {
        string_at(pool, self.const_pool_index)
    }
}

/// What `StructAnnotationAttribute.parseAnnotation` passes to
/// `new AnnotationExprent(className, names, values)`.
#[derive(Clone, Debug)]
pub struct AnnotationData {
    pub class_name: ArcStr,
    pub par_names: Vec<ArcStr>,
    pub par_values: Vec<ElementValue>,
}

/// An annotation element value, as far as `parseAnnotationElement` decodes
/// it before building an expression.
#[derive(Clone, Debug)]
pub enum ElementValue {
    /// `new FieldExprent(constName, descr.type.value, true, null, descr, null)`.
    EnumConstant {
        const_name: ArcStr,
        descriptor: FieldDescriptor,
    },
    /// `new ConstExprent(VarType.VARTYPE_CLASS, value, null)`.
    Class(ArcStr),
    /// A `NewExprent` with a direct array initializer of these elements.
    Array(Vec<ElementValue>),
    Annotation(AnnotationData),
    /// `new ConstExprent(type, value, null)`.
    Const { ty: VarType, value: ConstantValue },
}

impl AnnotationData {
    /// `StructAnnotationAttribute.parseAnnotations`.
    pub fn read_list(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Vec<AnnotationData>> {
        let len = data.read_unsigned_short()?;
        read_list(len, || Self::read(data, pool))
    }

    /// `StructAnnotationAttribute.parseAnnotation`.
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<AnnotationData> {
        let class_name = string_at(pool, data.read_unsigned_short()?);

        let len = data.read_unsigned_short()?;
        let mut par_names = Vec::with_capacity(len as usize);
        let mut par_values = Vec::with_capacity(len as usize);
        for _ in 0..len {
            par_names.push(string_at(pool, data.read_unsigned_short()?));
            par_values.push(ElementValue::read(data, pool)?);
        }

        Ok(AnnotationData {
            class_name: VarType::from_signature(&class_name).value.unwrap(),
            par_names,
            par_values,
        })
    }
}

impl ElementValue {
    /// `StructAnnotationAttribute.parseAnnotationElement`.
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<ElementValue> {
        let tag = data.read_unsigned_byte()? as u8;

        Ok(match tag {
            // enum constant
            b'e' => {
                let class_name = string_at(pool, data.read_unsigned_short()?);
                let const_name = string_at(pool, data.read_unsigned_short()?);
                ElementValue::EnumConstant {
                    const_name,
                    descriptor: FieldDescriptor::parse_descriptor(&class_name),
                }
            }
            // class
            b'c' => {
                let descriptor = string_at(pool, data.read_unsigned_short()?);
                let ty = FieldDescriptor::parse_descriptor(&descriptor).ty;
                ElementValue::Class(match ty.ty {
                    CodeType::Object => ty.value.unwrap(),
                    CodeType::Byte => arcstr::literal!("byte"),
                    CodeType::Char => arcstr::literal!("char"),
                    CodeType::Double => arcstr::literal!("double"),
                    CodeType::Float => arcstr::literal!("float"),
                    CodeType::Int => arcstr::literal!("int"),
                    CodeType::Long => arcstr::literal!("long"),
                    CodeType::Short => arcstr::literal!("short"),
                    CodeType::Boolean => arcstr::literal!("boolean"),
                    CodeType::Void => arcstr::literal!("void"),
                    other => panic!("invalid class type: {other:?}"),
                })
            }
            // array
            b'[' => {
                let len = data.read_unsigned_short()?;
                ElementValue::Array(read_list(len, || Self::read(data, pool))?)
            }
            // annotation
            b'@' => ElementValue::Annotation(AnnotationData::read(data, pool)?),
            _ => {
                let cn = pool
                    .get_primitive_constant(data.read_unsigned_short()?)
                    .unwrap();
                let ty = match tag {
                    b'B' => VarType::VARTYPE_BYTE,
                    b'C' => VarType::VARTYPE_CHAR,
                    b'D' => VarType::VARTYPE_DOUBLE,
                    b'F' => VarType::VARTYPE_FLOAT,
                    b'I' => VarType::VARTYPE_INT,
                    b'J' => VarType::VARTYPE_LONG,
                    b'S' => VarType::VARTYPE_SHORT,
                    b'Z' => VarType::VARTYPE_BOOLEAN,
                    b's' => VarType::VARTYPE_STRING,
                    _ => panic!("invalid element type!"),
                };
                ElementValue::Const {
                    ty,
                    value: cn.value,
                }
            }
        })
    }
}

#[derive(Clone, Debug)]
pub struct StructAnnotationAttribute {
    pub annotations: Vec<AnnotationData>,
}

impl StructAnnotationAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        Ok(Self {
            annotations: AnnotationData::read_list(data, pool)?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct StructAnnotationParameterAttribute {
    pub param_annotations: Vec<Vec<AnnotationData>>,
}

impl StructAnnotationParameterAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let len = data.read_unsigned_byte()?;
        Ok(Self {
            param_annotations: read_list(len, || AnnotationData::read_list(data, pool))?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct StructAnnDefaultAttribute {
    pub default_value: ElementValue,
}

impl StructAnnDefaultAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        Ok(Self {
            default_value: ElementValue::read(data, pool)?,
        })
    }
}

/// `TypeAnnotation.PathKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathKind {
    DeeperArray,
    DeeperNested,
    OnWildcard,
    GenericArgument,
}

impl PathKind {
    pub const VALUES: [PathKind; 4] = [
        PathKind::DeeperArray,
        PathKind::DeeperNested,
        PathKind::OnWildcard,
        PathKind::GenericArgument,
    ];
}

/// `TypeAnnotation.PathValue`: one step from a type towards the part of it
/// that an annotation is on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathValue {
    pub kind: PathKind,
    pub type_arg: i32,
}

impl PathValue {
    pub fn new(kind: PathKind, type_arg: i32) -> Self {
        if kind != PathKind::GenericArgument && type_arg != 0 {
            panic!("Illegal path data");
        }
        Self { kind, type_arg }
    }
}

/// What `StructTypeAnnotationAttribute.parse` passes to
/// `new TypeAnnotation(target, path, annotation)`.
#[derive(Clone, Debug)]
pub struct TypeAnnotationData {
    pub target: i32,
    pub path: Vec<PathValue>,
    pub annotation: AnnotationData,
}

impl TypeAnnotationData {
    pub const CLASS_TYPE_PARAMETER: i32 = 0x00;
    pub const METHOD_TYPE_PARAMETER: i32 = 0x01;
    pub const SUPER_TYPE_REFERENCE: i32 = 0x10;
    pub const CLASS_TYPE_PARAMETER_BOUND: i32 = 0x11;
    pub const METHOD_TYPE_PARAMETER_BOUND: i32 = 0x12;
    pub const FIELD: i32 = 0x13;
    pub const METHOD_RETURN_TYPE: i32 = 0x14;
    pub const METHOD_RECEIVER: i32 = 0x15;
    pub const METHOD_PARAMETER: i32 = 0x16;
    pub const THROWS_REFERENCE: i32 = 0x17;
    pub const LOCAL_VARIABLE: i32 = 0x40;
    pub const RESOURCE_VARIABLE: i32 = 0x41;
    pub const CATCH_CLAUSE: i32 = 0x42;
    pub const EXPR_INSTANCEOF: i32 = 0x43;
    pub const EXPR_NEW: i32 = 0x44;
    pub const EXPR_CONSTRUCTOR_REF: i32 = 0x45;
    pub const EXPR_METHOD_REF: i32 = 0x46;
    pub const TYPE_ARG_CAST: i32 = 0x47;
    pub const TYPE_ARG_CONSTRUCTOR_CALL: i32 = 0x48;
    pub const TYPE_ARG_METHOD_CALL: i32 = 0x49;
    pub const TYPE_ARG_CONSTRUCTOR_REF: i32 = 0x4A;
    pub const TYPE_ARG_METHOD_REF: i32 = 0x4B;

    fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let target_type = data.read_unsigned_byte()?;
        let mut target = target_type << 24;

        match target_type {
            Self::CLASS_TYPE_PARAMETER | Self::METHOD_TYPE_PARAMETER | Self::METHOD_PARAMETER => {
                target |= data.read_unsigned_byte()?;
            }
            Self::SUPER_TYPE_REFERENCE
            | Self::CLASS_TYPE_PARAMETER_BOUND
            | Self::METHOD_TYPE_PARAMETER_BOUND
            | Self::THROWS_REFERENCE
            | Self::CATCH_CLAUSE
            | Self::EXPR_INSTANCEOF
            | Self::EXPR_NEW
            | Self::EXPR_CONSTRUCTOR_REF
            | Self::EXPR_METHOD_REF => {
                target |= data.read_unsigned_short()?;
            }
            Self::TYPE_ARG_CAST
            | Self::TYPE_ARG_CONSTRUCTOR_CALL
            | Self::TYPE_ARG_METHOD_CALL
            | Self::TYPE_ARG_CONSTRUCTOR_REF
            | Self::TYPE_ARG_METHOD_REF => {
                data.skip_bytes(3);
            }
            Self::LOCAL_VARIABLE | Self::RESOURCE_VARIABLE => {
                let table_length = data.read_unsigned_short()?;
                data.skip_bytes(table_length * 6);
            }
            Self::FIELD | Self::METHOD_RETURN_TYPE | Self::METHOD_RECEIVER => {}
            _ => panic!("unknown target type: {target_type}"),
        }

        let path_length = data.read_unsigned_byte()?;
        let path = read_list(path_length, || {
            let kind = PathKind::VALUES[data.read_byte()? as usize];
            Ok(PathValue::new(kind, i32::from(data.read_byte()?)))
        })?;

        Ok(Self {
            target,
            path,
            annotation: AnnotationData::read(data, pool)?,
        })
    }

    pub fn get_target_type(&self) -> i32 {
        self.target >> 24
    }

    pub fn get_index(&self) -> i32 {
        self.target & 0xFFFF
    }

    pub fn is_top_level(&self) -> bool {
        self.path.is_empty()
    }
}

#[derive(Clone, Debug)]
pub struct StructTypeAnnotationAttribute {
    pub annotations: Vec<TypeAnnotationData>,
}

impl StructTypeAnnotationAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let len = data.read_unsigned_short()?;
        Ok(Self {
            annotations: read_list(len, || TypeAnnotationData::read(data, pool))?,
        })
    }
}

#[derive(Clone, Debug)]
pub struct StructModuleAttribute {
    pub module_name: ArcStr,
    pub module_flags: i32,
    pub module_version: Option<ArcStr>,
    pub requires: Vec<RequiresEntry>,
    pub exports: Vec<ExportsEntry>,
    pub opens: Vec<OpensEntry>,
    pub uses: Vec<ArcStr>,
    pub provides: Vec<ProvidesEntry>,
}

#[derive(Clone, Debug)]
pub struct RequiresEntry {
    pub module_name: ArcStr,
    pub flags: i32,
    pub module_version: Option<ArcStr>,
}

#[derive(Clone, Debug)]
pub struct ExportsEntry {
    pub package_name: ArcStr,
    pub flags: i32,
    pub export_to_modules: Vec<ArcStr>,
}

#[derive(Clone, Debug)]
pub struct OpensEntry {
    pub package_name: ArcStr,
    pub flags: i32,
    pub opens_to_modules: Vec<ArcStr>,
}

#[derive(Clone, Debug)]
pub struct ProvidesEntry {
    pub interface_name: ArcStr,
    pub implementation_names: Vec<ArcStr>,
}

impl StructModuleAttribute {
    pub fn read(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Self> {
        let module_name_index = data.read_unsigned_short()?;
        let module_name = string_at(pool, module_name_index);
        let module_flags = data.read_unsigned_short()?;
        let module_version = optional_string_at(pool, data.read_unsigned_short()?);

        let requires_count = data.read_unsigned_short()?;
        let requires = read_list(requires_count, || {
            let module_name_index = data.read_unsigned_short()?;
            let flags = data.read_unsigned_short()?;
            let version_index = data.read_unsigned_short()?;
            Ok(RequiresEntry {
                module_name: string_at(pool, module_name_index),
                flags,
                module_version: optional_string_at(pool, version_index),
            })
        })?;

        let exports_count = data.read_unsigned_short()?;
        let exports = read_list(exports_count, || {
            let package_name_index = data.read_unsigned_short()?;
            let flags = data.read_unsigned_short()?;
            let export_to_modules = read_string_list(data, pool)?;
            Ok(ExportsEntry {
                package_name: string_at(pool, package_name_index),
                flags,
                export_to_modules,
            })
        })?;

        let opens_count = data.read_unsigned_short()?;
        let opens = read_list(opens_count, || {
            let package_name_index = data.read_unsigned_short()?;
            let flags = data.read_unsigned_short()?;
            let opens_to_modules = read_string_list(data, pool)?;
            Ok(OpensEntry {
                package_name: string_at(pool, package_name_index),
                flags,
                opens_to_modules,
            })
        })?;

        let uses = read_string_list(data, pool)?;

        let provides_count = data.read_unsigned_short()?;
        let provides = read_list(provides_count, || {
            let interface_name = string_at(pool, data.read_unsigned_short()?);
            Ok(ProvidesEntry {
                interface_name,
                implementation_names: read_string_list(data, pool)?,
            })
        })?;

        Ok(Self {
            module_name,
            module_flags,
            module_version,
            requires,
            exports,
            opens,
            uses,
            provides,
        })
    }
}

fn read_string_list(data: Input<'_, '_>, pool: &ConstantPool) -> io::Result<Vec<ArcStr>> {
    let count = data.read_unsigned_short()?;
    read_list(count, || Ok(string_at(pool, data.read_unsigned_short()?)))
}
