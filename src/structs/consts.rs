// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.consts`: the constant pool of a class with its two kinds of
//! entries, `PrimitiveConstant` (a value, or a name) and `LinkConstant` (a
//! reference to a class member).
//!
//! Entries are immutable once the pool is built; the lookups hand out
//! copies, which is cheap because every string in them is shared.

use std::io;
use std::sync::Arc;

use arcstr::ArcStr;
use bit_set::BitSet;

use crate::code::code_constants::*;
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::types::{FieldDescriptor, MethodDescriptor, NewClassNameBuilder, VarType};
use crate::util::data_input::DataInputFullStream;
use crate::util::java_str::JavaString;

/// `ConstantPool.FIELD`.
pub const FIELD: i32 = 1;
/// `ConstantPool.METHOD`.
pub const METHOD: i32 = 2;

#[derive(Clone, Debug)]
pub enum PooledConstant {
    Primitive(PrimitiveConstant),
    Link(LinkConstant),
}

impl PooledConstant {
    /// The `CONSTANT_*` tag.
    pub fn ty(&self) -> i32 {
        match self {
            Self::Primitive(constant) => constant.ty,
            Self::Link(constant) => constant.ty,
        }
    }
}

/// The value of a constant: the `Object` upstream stores in
/// `PrimitiveConstant.value` and in constant expressions.
#[derive(Clone, Debug)]
pub enum ConstantValue {
    Null,
    Integer(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    String(JavaString),
}

/// `Object.equals` of the boxed values: floating-point numbers compare by
/// their bits, with all NaNs equal.
impl PartialEq for ConstantValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Integer(a), Self::Integer(b)) => a == b,
            (Self::Long(a), Self::Long(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => {
                a.to_bits() == b.to_bits() || a.is_nan() && b.is_nan()
            }
            (Self::Double(a), Self::Double(b)) => {
                a.to_bits() == b.to_bits() || a.is_nan() && b.is_nan()
            }
            (Self::String(a), Self::String(b)) => a == b,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PrimitiveConstant {
    pub ty: i32,
    pub index: i32,
    pub value: ConstantValue,
    pub is_array: bool,
}

impl PrimitiveConstant {
    /// `new PrimitiveConstant(type, value)`.
    pub fn new(ty: i32, value: ConstantValue) -> Self {
        let mut constant = Self {
            ty,
            index: 0,
            value,
            is_array: false,
        };
        constant.init_constant();
        constant
    }

    /// `new PrimitiveConstant(type, index)`: a constant that names another
    /// one, to be resolved once the whole pool is read.
    fn unresolved(ty: i32, index: i32) -> Self {
        Self {
            ty,
            index,
            value: ConstantValue::Null,
            is_array: false,
        }
    }

    fn init_constant(&mut self) {
        if self.ty == CONSTANT_CLASS {
            // empty string for a class name seems to be possible in some android files
            self.is_array = self.get_string().starts_with('[');
        }
    }

    /// `(String) value`.
    pub fn get_string(&self) -> &ArcStr {
        self.get_java_string().as_utf8_lossy()
    }

    /// Gets the original sequence of UTF-16 units for a string literal.
    pub fn get_java_string(&self) -> &JavaString {
        match &self.value {
            ConstantValue::String(value) => value,
            value => panic!("{value:?} cannot be cast to String"),
        }
    }
}

impl PartialEq for PrimitiveConstant {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty && self.is_array == other.is_array && self.value == other.value
    }
}

#[derive(Clone, Debug, Default)]
pub struct LinkConstant {
    pub ty: i32,
    pub index1: i32,
    pub index2: i32,
    /// Absent for name-and-type and dynamic constants.
    pub classname: Option<ArcStr>,
    pub elementname: ArcStr,
    pub descriptor: ArcStr,
}

impl LinkConstant {
    /// `new LinkConstant(type, classname, elementname, descriptor)`.
    pub fn new(ty: i32, classname: ArcStr, elementname: ArcStr, descriptor: ArcStr) -> Self {
        let constant = Self {
            ty,
            classname: Some(classname),
            elementname,
            descriptor,
            ..Self::default()
        };
        constant.init_constant();
        constant
    }

    /// `new LinkConstant(type, index1, index2)`.
    fn unresolved(ty: i32, index1: i32, index2: i32) -> Self {
        Self {
            ty,
            index1,
            index2,
            ..Self::default()
        }
    }

    fn init_constant(&self) {
        let is_method = matches!(
            self.ty,
            CONSTANT_METHODREF | CONSTANT_INTERFACEMETHODREF | CONSTANT_INVOKEDYNAMIC
        ) || self.ty == CONSTANT_METHODHANDLE
            && !matches!(
                self.index1,
                CONSTANT_METHODHANDLE_REF_GETFIELD
                    | CONSTANT_METHODHANDLE_REF_PUTFIELD
                    | CONSTANT_METHODHANDLE_REF_GETSTATIC
                    | CONSTANT_METHODHANDLE_REF_PUTSTATIC
            );
        if is_method && !(self.descriptor.starts_with('(') && self.descriptor.contains(')')) {
            panic!(
                "Invalid descriptor: {}; type = {}; classname = {}; elementname = {}; kind = {}",
                self.descriptor,
                self.ty,
                self.classname.as_deref().unwrap_or("null"),
                self.elementname,
                self.index1
            );
        }
    }
}

impl PartialEq for LinkConstant {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
            && self.elementname == other.elementname
            && self.descriptor == other.descriptor
            && (self.ty != CONSTANT_NAMEANDTYPE || self.classname == other.classname)
    }
}

pub struct ConstantPool {
    pool: Vec<Option<PooledConstant>>,
    interceptor: Option<Arc<PoolInterceptor>>,
}

impl ConstantPool {
    pub fn new(
        input: &mut DataInputFullStream<'_>,
        interceptor: Option<Arc<PoolInterceptor>>,
    ) -> io::Result<Self> {
        let size = input.read_unsigned_short()? as usize;
        let mut pool: Vec<Option<PooledConstant>> = Vec::with_capacity(size);
        let mut next_pass = [
            BitSet::with_capacity(size),
            BitSet::with_capacity(size),
            BitSet::with_capacity(size),
        ];

        // first dummy constant
        pool.push(None);

        // first pass: read the elements
        let mut i = 1;
        while i < size {
            let tag = i32::from(input.read_unsigned_byte()? as i8);

            let primitive = |value| PooledConstant::Primitive(PrimitiveConstant::new(tag, value));
            match tag {
                CONSTANT_UTF8 => {
                    pool.push(Some(primitive(ConstantValue::String(input.read_java_utf()?))));
                }
                CONSTANT_INTEGER => {
                    pool.push(Some(primitive(ConstantValue::Integer(input.read_int()?))));
                }
                CONSTANT_FLOAT => {
                    pool.push(Some(primitive(ConstantValue::Float(input.read_float()?))));
                }
                CONSTANT_LONG => {
                    pool.push(Some(primitive(ConstantValue::Long(input.read_long()?))));
                    pool.push(None);
                    i += 1;
                }
                CONSTANT_DOUBLE => {
                    pool.push(Some(primitive(ConstantValue::Double(input.read_double()?))));
                    pool.push(None);
                    i += 1;
                }
                CONSTANT_CLASS | CONSTANT_STRING | CONSTANT_METHODTYPE | CONSTANT_MODULE
                | CONSTANT_PACKAGE => {
                    let index = input.read_unsigned_short()?;
                    pool.push(Some(PooledConstant::Primitive(
                        PrimitiveConstant::unresolved(tag, index),
                    )));
                    next_pass[0].insert(i);
                }
                CONSTANT_NAMEANDTYPE => {
                    let (index1, index2) =
                        (input.read_unsigned_short()?, input.read_unsigned_short()?);
                    pool.push(Some(PooledConstant::Link(LinkConstant::unresolved(
                        tag, index1, index2,
                    ))));
                    next_pass[0].insert(i);
                }
                CONSTANT_FIELDREF
                | CONSTANT_METHODREF
                | CONSTANT_INTERFACEMETHODREF
                | CONSTANT_INVOKEDYNAMIC
                | CONSTANT_DYNAMIC => {
                    let (index1, index2) =
                        (input.read_unsigned_short()?, input.read_unsigned_short()?);
                    pool.push(Some(PooledConstant::Link(LinkConstant::unresolved(
                        tag, index1, index2,
                    ))));
                    next_pass[1].insert(i);
                }
                CONSTANT_METHODHANDLE => {
                    let (index1, index2) =
                        (input.read_unsigned_byte()?, input.read_unsigned_short()?);
                    pool.push(Some(PooledConstant::Link(LinkConstant::unresolved(
                        tag, index1, index2,
                    ))));
                    next_pass[2].insert(i);
                }
                _ => panic!("Invalid Constant Pool entry #{i} Type: {tag}"),
            }
            i += 1;
        }

        // resolving complex pool elements; no names are replaced while the pool is being built
        let mut pool = Self {
            pool,
            interceptor: None,
        };
        for pass in &next_pass {
            for idx in pass {
                pool.resolve_constant(idx);
            }
        }

        // get global constant pool interceptor instance, if any available
        pool.interceptor = interceptor;
        Ok(pool)
    }

    /// `PooledConstant.resolveConstant` for the constant at `idx`.
    fn resolve_constant(&mut self, idx: usize) {
        let string_at = |index| self.get_primitive_constant(index).unwrap().get_string().clone();

        let resolved = match self.pool[idx].clone().unwrap() {
            PooledConstant::Primitive(mut constant) => {
                let utf = self.get_primitive_constant(constant.index).unwrap();
                constant.value = ConstantValue::String(utf.get_java_string().clone());
                constant.init_constant();
                PooledConstant::Primitive(constant)
            }
            PooledConstant::Link(mut constant) => {
                if constant.ty == CONSTANT_NAMEANDTYPE {
                    constant.elementname = string_at(constant.index1);
                    constant.descriptor = string_at(constant.index2);
                } else if constant.ty == CONSTANT_METHODHANDLE {
                    let ref_info = self.get_link_constant(constant.index2).unwrap();
                    constant.classname = ref_info.classname;
                    constant.elementname = ref_info.elementname;
                    constant.descriptor = ref_info.descriptor;
                } else {
                    if constant.ty != CONSTANT_INVOKEDYNAMIC && constant.ty != CONSTANT_DYNAMIC {
                        constant.classname = Some(string_at(constant.index1));
                    }

                    let nametype = self.get_link_constant(constant.index2).unwrap();
                    constant.elementname = nametype.elementname;
                    constant.descriptor = nametype.descriptor;
                }
                constant.init_constant();
                PooledConstant::Link(constant)
            }
        };
        self.pool[idx] = Some(resolved);
    }

    /// The name and descriptor of a member of `class_name`, as they are
    /// after renaming.
    pub fn get_class_element(
        &self,
        element_type: i32,
        class_name: &str,
        name_index: i32,
        descriptor_index: i32,
    ) -> (ArcStr, ArcStr) {
        let string_at = |index| match self.get_constant(index) {
            Some(PooledConstant::Primitive(constant)) => constant.get_string().clone(),
            constant => panic!("{constant:?} cannot be cast to PrimitiveConstant"),
        };
        let mut element_name = string_at(name_index);
        let mut descriptor = string_at(descriptor_index);

        if let Some(interceptor) = &self.interceptor {
            let class_name = interceptor.get_old_name(class_name).unwrap_or(class_name);

            let key = format!("{class_name} {element_name} {descriptor}");
            if let Some(new_element) = interceptor.get_name(&key) {
                element_name = new_element.split(' ').nth(1).unwrap().into();
            }

            if let Some(new_descriptor) = self.build_new_descriptor(element_type == FIELD, &descriptor)
            {
                descriptor = new_descriptor.into();
            }
        }

        (element_name, descriptor)
    }

    pub fn get_constant(&self, index: i32) -> Option<&PooledConstant> {
        self.pool[index as usize].as_ref()
    }

    pub fn get_primitive_constant(&self, index: i32) -> Option<PrimitiveConstant> {
        let cn = match self.get_constant(index)? {
            PooledConstant::Primitive(constant) => constant,
            constant => panic!("{constant:?} cannot be cast to PrimitiveConstant"),
        };

        if self.interceptor.is_some()
            && cn.ty == CONSTANT_CLASS
            && let Some(new_name) = self.build_new_classname(cn.get_string())
        {
            return Some(PrimitiveConstant::new(
                CONSTANT_CLASS,
                ConstantValue::String(new_name.into()),
            ));
        }

        Some(cn.clone())
    }

    pub fn get_link_constant(&self, index: i32) -> Option<LinkConstant> {
        let ln = match self.get_constant(index)? {
            PooledConstant::Link(constant) => constant,
            constant => panic!("{constant:?} cannot be cast to LinkConstant"),
        };

        if let Some(interceptor) = &self.interceptor
            && matches!(
                ln.ty,
                CONSTANT_FIELDREF | CONSTANT_METHODREF | CONSTANT_INTERFACEMETHODREF
            )
        {
            let classname = ln.classname.as_ref().unwrap();
            let new_class_name = self.build_new_classname(classname);
            let new_element = interceptor.get_name(&format!(
                "{classname} {} {}",
                ln.elementname, ln.descriptor
            ));
            let new_descriptor =
                self.build_new_descriptor(ln.ty == CONSTANT_FIELDREF, &ln.descriptor);
            //TODO: Fix newElement being null caused by ln.classname being a leaf class instead of the class that declared the field/method.
            //See the comments of IDEA-137253 for more information.
            if new_class_name.is_some() || new_element.is_some() || new_descriptor.is_some() {
                return Some(LinkConstant::new(
                    ln.ty,
                    new_class_name.map_or_else(|| classname.clone(), ArcStr::from),
                    new_element.map_or_else(
                        || ln.elementname.clone(),
                        |element| element.split(' ').nth(1).unwrap().into(),
                    ),
                    new_descriptor.map_or_else(|| ln.descriptor.clone(), ArcStr::from),
                ));
            }
        }

        Some(ln.clone())
    }

    pub fn get_pool(&self) -> &[Option<PooledConstant>] {
        &self.pool
    }

    fn build_new_descriptor(&self, is_field: bool, descriptor: &str) -> Option<String> {
        if is_field {
            FieldDescriptor::parse_descriptor(descriptor).build_new_descriptor(self)
        } else {
            MethodDescriptor::parse_descriptor(descriptor).build_new_descriptor(self)
        }
    }
}

impl NewClassNameBuilder for ConstantPool {
    fn build_new_classname(&self, class_name: &str) -> Option<String> {
        let vt = VarType::from_signature_cl(class_name, true);

        let new_name = self.interceptor.as_ref().unwrap().get_name(vt.name())?;
        Some(if vt.array_dim > 0 {
            // No functional change, just a revert for J8 compatibility
            format!("{}L{new_name};", "[".repeat(vt.array_dim as usize))
        } else {
            new_name.to_owned()
        })
    }
}
