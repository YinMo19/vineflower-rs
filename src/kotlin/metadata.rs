// Copyright 2010-2025 JetBrains s.r.o. and Kotlin Programming Language contributors.
// Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{borrow::Cow, cell::Cell};

use prost::Message;

use crate::{
    classfile::{Annotation, ClassFile, Constant, ConstantPool, ElementValue},
    descriptor::{MethodDescriptor, Type as JvmType},
};

use super::{
    KotlinError,
    model::*,
    names::{Names, default_descriptor},
    proto,
};

const METADATA: &str = "Lkotlin/Metadata;";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MetadataHeader {
    pub kind: i32,
    pub version: Vec<i32>,
    pub bytecode_version: Vec<i32>,
    pub extra_int: i32,
    pub extra_string: Option<String>,
    pub package_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Metadata {
    pub header: MetadataHeader,
    pub declaration: Declaration,
}

/// Read Kotlin JVM metadata without requiring declaration bodies to be supported.
pub fn read_metadata(class: &ClassFile<'_>) -> Result<Option<Metadata>, KotlinError> {
    metadata_annotation(class)?
        .as_ref()
        .map(|annotation| read_annotation(annotation, &class.pool))
        .transpose()
}

/// Select Kotlin by annotation, without interpreting its metadata payload.
pub fn has_metadata(class: &ClassFile<'_>) -> Result<bool, KotlinError> {
    Ok(metadata_annotation(class)?.is_some())
}

pub(crate) fn metadata_kind(class: &ClassFile<'_>) -> Result<Option<i32>, KotlinError> {
    let Some(annotation) = metadata_annotation(class)? else { return Ok(None); };
    let mut kind = None;
    for (index, value) in annotation.elements {
        if class.pool.utf8(index)? == "k" && kind.replace(integer(&class.pool, &value)?).is_some() {
            return Err(KotlinError::Metadata("duplicate Kotlin annotation element"));
        }
    }
    Ok(Some(kind.unwrap_or(1)))
}

fn metadata_annotation(class: &ClassFile<'_>) -> Result<Option<Annotation>, KotlinError> {
    let mut metadata = None;
    for visible in [true, false] {
        for annotation in class.annotations(visible)? {
            if class.pool.utf8(annotation.type_index)? == METADATA
                && metadata.replace(annotation).is_some()
            {
                return Err(KotlinError::Metadata("duplicate Kotlin annotation"));
            }
        }
    }
    Ok(metadata)
}

fn read_annotation(
    annotation: &Annotation,
    pool: &ConstantPool<'_>,
) -> Result<Metadata, KotlinError> {
    let mut header = MetadataHeader {
        kind: 1,
        version: Vec::new(),
        bytecode_version: Vec::new(),
        extra_int: 0,
        extra_string: None,
        package_name: None,
    };
    let mut d1 = &[][..];
    let mut d2 = &[][..];
    let mut seen = 0u16;
    for (name_index, value) in &annotation.elements {
        let name = pool.utf8(*name_index)?;
        let bit = match name {
            "k" => 1,
            "mv" => 2,
            "bv" => 4,
            "xi" => 8,
            "xs" => 16,
            "pn" => 32,
            "d1" => 64,
            "d2" => 128,
            _ => continue,
        };
        if seen & bit != 0 {
            return Err(KotlinError::Metadata("duplicate Kotlin annotation element"));
        }
        seen |= bit;
        match bit {
            1 => header.kind = integer(pool, value)?,
            2 => header.version = integer_array(pool, value)?,
            4 => header.bytecode_version = integer_array(pool, value)?,
            8 => header.extra_int = integer(pool, value)?,
            16 => header.extra_string = Some(pool.utf8(string_index(value)?)?.to_owned()),
            32 => header.package_name = Some(pool.utf8(string_index(value)?)?.to_owned()),
            64 => d1 = array(value)?,
            128 => d2 = array(value)?,
            _ => unreachable!(),
        }
    }
    if !matches!(header.version.as_slice(), [1, 1..=9, ..] | [2, 0..=2, ..])
        || header.version.iter().any(|&n| n < 0)
    {
        return Err(KotlinError::Version(header.version));
    }
    let declaration = match header.kind {
        4 => Declaration::MultifileFacade(
            strings(pool, d1)?.into_iter().map(str::to_owned).collect(),
        ),
        3 if d1.is_empty() => Declaration::Synthetic(None),
        1 | 2 | 3 | 5 => {
            let chunks = d1
                .iter()
                .map(|value| Ok(pool.utf16(string_index(value)?)?))
                .collect::<Result<Vec<_>, KotlinError>>()?;
            let bytes = decode_payload(&chunks)?;
            let mut payload = bytes.as_slice();
            let names = Names::new(
                proto::StringTableTypes::decode_length_delimited(&mut payload)?,
                strings(pool, d2)?,
            )?;
            // Table references are a graph, not the recursion-limited protobuf tree.
            // Bound expanded nodes as well as depth to reject cycles and repeated expansion.
            let budget = Cell::new(100_000);
            let reader = Reader {
                names: &names,
                table: None,
                budget: &budget,
            };
            match header.kind {
                1 => Declaration::Class(reader.class(&proto::Class::decode(payload)?)?),
                2 => Declaration::FileFacade(reader.package(&proto::Package::decode(payload)?)?),
                3 => Declaration::Synthetic(Some(Box::new(
                    reader.function(&proto::Function::decode(payload)?)?,
                ))),
                5 => Declaration::MultifilePart(reader.package(&proto::Package::decode(payload)?)?),
                _ => unreachable!(),
            }
        }
        _ => return Err(KotlinError::Metadata("unknown Kotlin metadata kind")),
    };
    Ok(Metadata {
        header,
        declaration,
    })
}

fn integer(pool: &ConstantPool<'_>, value: &ElementValue) -> Result<i32, KotlinError> {
    if let ElementValue::Constant { tag: b'I', index } = value
        && let Constant::Integer(n) = pool.get(*index)?
    {
        return Ok(*n);
    }
    Err(KotlinError::Metadata(
        "expected an integer annotation value",
    ))
}

fn array(value: &ElementValue) -> Result<&[ElementValue], KotlinError> {
    match value {
        ElementValue::Array(values) => Ok(values),
        _ => Err(KotlinError::Metadata("expected an array annotation value")),
    }
}

fn integer_array(pool: &ConstantPool<'_>, value: &ElementValue) -> Result<Vec<i32>, KotlinError> {
    array(value)?
        .iter()
        .map(|value| integer(pool, value))
        .collect()
}

fn string_index(value: &ElementValue) -> Result<u16, KotlinError> {
    match *value {
        ElementValue::Constant { tag: b's', index } => Ok(index),
        _ => Err(KotlinError::Metadata("expected a string annotation value")),
    }
}

fn strings<'a>(
    pool: &'a ConstantPool<'_>,
    values: &[ElementValue],
) -> Result<Vec<&'a str>, KotlinError> {
    values
        .iter()
        .map(|value| Ok(pool.utf8(string_index(value)?)?))
        .collect()
}

/// Kotlin BitEncoding packs each byte in a UTF-16 code unit in its current
/// format; older metadata groups the bit stream into biased seven-bit units.
pub(super) fn decode_payload(chunks: &[Cow<'_, [u16]>]) -> Result<Vec<u8>, KotlinError> {
    let (first, rest) = chunks
        .split_first()
        .ok_or(KotlinError::Metadata("missing data payload"))?;
    let marker = first.first().copied();
    let raw = marker == Some(0);
    let first = if matches!(marker, Some(0 | 0xffff)) {
        &first[1..]
    } else {
        first.as_ref()
    };
    let mut count = first.len();
    for chunk in rest {
        count = count
            .checked_add(chunk.len())
            .ok_or(KotlinError::Metadata("data payload too large"))?;
    }
    let units = first
        .iter()
        .copied()
        .chain(rest.iter().flat_map(|chunk| chunk.iter().copied()));
    if raw {
        return units
            .map(|unit| {
                u8::try_from(unit)
                    .map_err(|_| KotlinError::Metadata("non-byte in raw data payload"))
            })
            .collect();
    }
    let mut bytes = Vec::with_capacity(count / 8 * 7 + (count % 8) * 7 / 8);
    let mut buffer = 0u16;
    let mut bits = 0u32;
    for unit in units {
        if unit > 0x7f {
            return Err(KotlinError::Metadata("non-seven-bit unit in data payload"));
        }
        buffer |= (unit.wrapping_sub(1) & 0x7f) << bits;
        bits += 7;
        if bits >= 8 {
            bytes.push(buffer as u8);
            buffer >>= 8;
            bits -= 8;
        }
    }
    Ok(bytes)
}

struct Reader<'a, 'strings> {
    names: &'a Names<'strings>,
    table: Option<&'a proto::TypeTable>,
    budget: &'a Cell<usize>,
}

impl<'strings> Reader<'_, 'strings> {
    fn table<'a>(
        &'a self,
        table: Option<&'a proto::TypeTable>,
    ) -> Result<Reader<'a, 'strings>, KotlinError> {
        let table = table.or(self.table);
        if let Some(table) = table
            && let Some(n) = table.first_nullable
            && n != -1
            && usize::try_from(n).map_or(true, |n| n > table.types.len())
        {
            return Err(KotlinError::Metadata(
                "invalid nullable type-table boundary",
            ));
        }
        Ok(Reader {
            names: self.names,
            table,
            budget: self.budget,
        })
    }

    fn name(&self, index: Option<i32>) -> Result<String, KotlinError> {
        Ok(self
            .names
            .text(index.ok_or(KotlinError::Metadata("missing declaration name"))?)?
            .into_owned())
    }

    fn annotations(
        &self,
        annotations: &[proto::Annotation],
    ) -> Result<Vec<ClassName>, KotlinError> {
        annotations
            .iter()
            .map(|annotation| {
                self.names.class(
                    annotation
                        .id
                        .ok_or(KotlinError::Metadata("annotation lacks class ID"))?,
                )
            })
            .collect()
    }

    fn ty(
        &self,
        inline: Option<&proto::Type>,
        index: Option<i32>,
        depth: usize,
    ) -> Result<Option<Type>, KotlinError> {
        let (ty, force_nullable) = match (inline, index) {
            (None, None) => return Ok(None),
            (Some(ty), None) => (ty, false),
            (None, Some(i)) => {
                let (ty, table) = usize::try_from(i)
                    .ok()
                    .and_then(|i| {
                        self.table
                            .and_then(|table| table.types.get(i).map(|ty| (ty, table)))
                    })
                    .ok_or(KotlinError::Metadata(
                        "type index outside Kotlin type table",
                    ))?;
                (
                    ty,
                    table
                        .first_nullable
                        .is_some_and(|first| first >= 0 && i >= first),
                )
            }
            _ => {
                return Err(KotlinError::Metadata(
                    "both inline type and type-table index supplied",
                ));
            }
        };
        if depth >= 64 || self.budget.get() == 0 {
            return Err(KotlinError::Metadata(
                "Kotlin type graph exceeds expansion limit",
            ));
        }
        self.budget.set(self.budget.get() - 1);
        let depth = depth + 1;
        let classifier = match (
            ty.class_name,
            ty.type_parameter,
            ty.type_parameter_name,
            ty.type_alias_name,
        ) {
            (Some(index), None, None, None) => Classifier::Class(self.names.class(index)?),
            (None, Some(id), None, None) if id >= 0 => Classifier::TypeParameter(id),
            (None, None, Some(index), None) => {
                Classifier::TypeParameterName(self.name(Some(index))?)
            }
            (None, None, None, Some(index)) => Classifier::TypeAlias(self.names.class(index)?),
            _ => {
                return Err(KotlinError::Metadata(
                    "missing or conflicting classifiers in Kotlin type",
                ));
            }
        };
        let arguments = ty
            .arguments
            .iter()
            .map(|argument| {
                let projection = argument.projection.unwrap_or(2);
                if projection == 3 && argument.ty.is_none() && argument.type_id.is_none() {
                    return Ok(TypeArgument::Star);
                }
                Ok(TypeArgument::Type(
                    variance(projection)?,
                    self.required_type(argument.ty.as_ref(), argument.type_id, depth)?,
                ))
            })
            .collect::<Result<Vec<_>, KotlinError>>()?;
        let flexible = match (
            ty.flexible_capabilities,
            self.ty(ty.flexible_upper.as_deref(), ty.flexible_upper_id, depth)?,
        ) {
            (Some(index), Some(upper)) => Some((self.name(Some(index))?, Box::new(upper))),
            (None, None) => None,
            _ => return Err(KotlinError::Metadata("incomplete flexible type")),
        };
        let flags = Flags(ty.flags.unwrap_or(0) as u32);
        Ok(Some(Type {
            classifier,
            arguments,
            flexible,
            nullable: force_nullable || ty.nullable.unwrap_or(false),
            suspend: flags.has(0),
            definitely_not_null: flags.has(1),
            outer: self
                .ty(ty.outer.as_deref(), ty.outer_id, depth)?
                .map(Box::new),
            abbreviated: self
                .ty(ty.abbreviated.as_deref(), ty.abbreviated_id, depth)?
                .map(Box::new),
            raw: ty.raw.unwrap_or(false),
            annotations: self.annotations(&ty.annotations)?,
        }))
    }

    fn required_type(
        &self,
        inline: Option<&proto::Type>,
        index: Option<i32>,
        depth: usize,
    ) -> Result<Type, KotlinError> {
        self.ty(inline, index, depth)?
            .ok_or(KotlinError::Metadata("missing required Kotlin type"))
    }

    fn types(&self, inline: &[proto::Type], indices: &[i32]) -> Result<Vec<Type>, KotlinError> {
        if inline.is_empty() {
            indices
                .iter()
                .map(|&index| self.required_type(None, Some(index), 0))
                .collect()
        } else if indices.is_empty() {
            inline
                .iter()
                .map(|ty| self.required_type(Some(ty), None, 0))
                .collect()
        } else {
            Err(KotlinError::Metadata(
                "both inline types and type-table indices supplied",
            ))
        }
    }

    fn type_parameters(
        &self,
        parameters: &[proto::TypeParameter],
    ) -> Result<Vec<TypeParameter>, KotlinError> {
        parameters
            .iter()
            .map(|param| {
                Ok(TypeParameter {
                    id: param.id.filter(|&id| id >= 0).ok_or(KotlinError::Metadata(
                        "missing or negative type parameter ID",
                    ))?,
                    name: self.name(param.name)?,
                    variance: variance(param.variance.unwrap_or(2))?,
                    reified: param.reified.unwrap_or(false),
                    upper_bounds: self.types(&param.upper_bounds, &param.upper_bound_ids)?,
                    annotations: self.annotations(&param.annotations)?,
                })
            })
            .collect()
    }

    fn parameter(&self, param: &proto::ValueParameter) -> Result<ValueParameter, KotlinError> {
        Ok(ValueParameter {
            name: self.name(param.name)?,
            ty: self.required_type(param.ty.as_ref(), param.type_id, 0)?,
            vararg_element: self.ty(param.vararg_element.as_ref(), param.vararg_element_id, 0)?,
            flags: Flags(param.flags.unwrap_or(0) as u32),
        })
    }

    fn parameters(
        &self,
        parameters: &[proto::ValueParameter],
    ) -> Result<Vec<ValueParameter>, KotlinError> {
        parameters
            .iter()
            .map(|param| self.parameter(param))
            .collect()
    }

    fn method_signature<'a>(
        &self,
        signature: Option<&proto::JvmSignature>,
        name: &str,
        parameters: impl Iterator<Item = &'a Type>,
        returns: Option<&Type>,
        suspending: bool,
    ) -> Result<Option<JvmMethodSignature>, KotlinError> {
        let name = match signature.and_then(|s| s.name) {
            Some(index) => self.name(Some(index))?,
            None => name.to_owned(),
        };
        let descriptor = if let Some(index) = signature.and_then(|s| s.descriptor) {
            MethodDescriptor::parse(&self.names.text(index)?)?
        } else {
            let mut descriptor = String::from("(");
            for param in parameters {
                let Some(param) = default_descriptor(param) else {
                    return Ok(None);
                };
                if param == "V" {
                    return Ok(None);
                }
                descriptor.push_str(&param);
            }
            if suspending {
                descriptor.push_str(super::model::CONTINUATION_DESCRIPTOR);
            }
            descriptor.push(')');
            if suspending {
                descriptor.push_str("Ljava/lang/Object;");
            } else if let Some(returns) = returns {
                let Some(returns) = default_descriptor(returns) else {
                    return Ok(None);
                };
                descriptor.push_str(&returns);
            } else {
                descriptor.push('V');
            }
            MethodDescriptor::parse(&descriptor)?
        };
        Ok(Some(JvmMethodSignature { name, descriptor }))
    }

    fn accessor(
        &self,
        signature: Option<&proto::JvmSignature>,
    ) -> Result<Option<JvmMethodSignature>, KotlinError> {
        signature
            .map(|s| {
                let descriptor = s
                    .descriptor
                    .ok_or(KotlinError::Metadata("accessor lacks JVM descriptor"))?;
                Ok(JvmMethodSignature {
                    name: self.name(s.name)?,
                    descriptor: MethodDescriptor::parse(&self.names.text(descriptor)?)?,
                })
            })
            .transpose()
    }

    fn property_signature(
        &self,
        signature: Option<&proto::JvmPropertySignature>,
        name: &str,
        ty: &Type,
    ) -> Result<JvmPropertySignature, KotlinError> {
        let Some(signature) = signature else {
            return Ok(JvmPropertySignature::default());
        };
        let field = signature
            .field
            .as_ref()
            .map(|field| {
                let name = match field.name {
                    Some(index) => self.name(Some(index))?,
                    None => name.to_owned(),
                };
                let descriptor = match field.descriptor {
                    Some(index) => self.names.text(index)?,
                    None => default_descriptor(ty)
                        .ok_or(KotlinError::Metadata("property field lacks JVM descriptor"))?,
                };
                Ok::<_, KotlinError>(JvmFieldSignature {
                    name,
                    descriptor: JvmType::parse(&descriptor)?,
                })
            })
            .transpose()?;
        Ok(JvmPropertySignature {
            field,
            getter: self.accessor(signature.getter.as_ref())?,
            setter: self.accessor(signature.setter.as_ref())?,
            annotations_method: self.accessor(signature.annotations_method.as_ref())?,
            delegate_method: self.accessor(signature.delegate_method.as_ref())?,
        })
    }

    fn property(&self, property: &proto::Property) -> Result<Property, KotlinError> {
        let name = self.name(property.name)?;
        let ty = self.required_type(property.ty.as_ref(), property.type_id, 0)?;
        let signature = self.property_signature(property.signature.as_ref(), &name, &ty)?;
        Ok(Property {
            name,
            ty,
            signature,
            type_parameters: self.type_parameters(&property.type_parameters)?,
            receiver: self.ty(property.receiver.as_ref(), property.receiver_id, 0)?,
            context_receivers: self
                .types(&property.context_receivers, &property.context_receiver_ids)?,
            context_parameters: self.parameters(&property.context_parameters)?,
            setter_parameter: property
                .setter_parameter
                .as_ref()
                .map(|param| self.parameter(param))
                .transpose()?,
            flags: flags(property.flags, property.old_flags, 518),
            getter_flags: property.getter_flags.map(|flags| Flags(flags as u32)),
            setter_flags: property.setter_flags.map(|flags| Flags(flags as u32)),
            jvm_flags: property.jvm_flags.unwrap_or(0) as u32,
        })
    }

    fn function(&self, function: &proto::Function) -> Result<Function, KotlinError> {
        let reader = self.table(function.type_table.as_ref())?;
        let name = reader.name(function.name)?;
        let parameters = reader.parameters(&function.parameters)?;
        let returns = reader.required_type(function.returns.as_ref(), function.returns_id, 0)?;
        let receiver = reader.ty(function.receiver.as_ref(), function.receiver_id, 0)?;
        let flags = flags(function.flags, function.old_flags, 6);
        let signature = reader.method_signature(
            function.signature.as_ref(),
            &name,
            receiver.iter().chain(parameters.iter().map(|p| &p.ty)),
            Some(&returns),
            flags.has(13),
        )?;
        Ok(Function {
            name,
            returns,
            receiver,
            signature,
            parameters,
            context_receivers: reader
                .types(&function.context_receivers, &function.context_receiver_ids)?,
            context_parameters: reader.parameters(&function.context_parameters)?,
            type_parameters: reader.type_parameters(&function.type_parameters)?,
            flags,
            has_contract: function.contract.is_some(),
        })
    }

    fn constructor(&self, con: &proto::Constructor) -> Result<Constructor, KotlinError> {
        let parameters = self.parameters(&con.parameters)?;
        let signature = self.method_signature(
            con.signature.as_ref(),
            "<init>",
            parameters.iter().map(|p| &p.ty),
            None,
            false,
        )?;
        Ok(Constructor {
            signature,
            parameters,
            flags: Flags(con.flags.unwrap_or(6) as u32),
        })
    }

    fn type_alias(&self, alias: &proto::TypeAlias) -> Result<TypeAlias, KotlinError> {
        Ok(TypeAlias {
            name: self.name(alias.name)?,
            flags: Flags(alias.flags.unwrap_or(6) as u32),
            type_parameters: self.type_parameters(&alias.type_parameters)?,
            underlying: self.required_type(alias.underlying.as_ref(), alias.underlying_id, 0)?,
            expanded: self.required_type(alias.expanded.as_ref(), alias.expanded_id, 0)?,
        })
    }

    fn declarations(
        &self,
        properties: &[proto::Property],
        functions: &[proto::Function],
        type_aliases: &[proto::TypeAlias],
    ) -> Result<PackageDeclaration, KotlinError> {
        Ok(PackageDeclaration {
            properties: properties
                .iter()
                .map(|p| self.property(p))
                .collect::<Result<_, _>>()?,
            functions: functions
                .iter()
                .map(|f| self.function(f))
                .collect::<Result<_, _>>()?,
            type_aliases: type_aliases
                .iter()
                .map(|t| self.type_alias(t))
                .collect::<Result<_, _>>()?,
        })
    }

    fn package(&self, package: &proto::Package) -> Result<PackageDeclaration, KotlinError> {
        self.table(package.type_table.as_ref())?.declarations(
            &package.properties,
            &package.functions,
            &package.type_aliases,
        )
    }

    fn class(&self, class: &proto::Class) -> Result<ClassDeclaration, KotlinError> {
        let reader = self.table(class.type_table.as_ref())?;
        let flags = Flags(class.flags.unwrap_or(6) as u32);
        Ok(ClassDeclaration {
            name: reader.names.class(
                class
                    .name
                    .ok_or(KotlinError::Metadata("missing Kotlin class ID"))?,
            )?,
            kind: flags.class_kind()?,
            flags,
            companion_name: class
                .companion_name
                .map(|index| reader.name(Some(index)))
                .transpose()?,
            nested_names: class
                .nested_names
                .iter()
                .map(|&index| reader.name(Some(index)))
                .collect::<Result<_, _>>()?,
            sealed_subclasses: class
                .sealed_subclasses
                .iter()
                .map(|&index| reader.names.class(index))
                .collect::<Result<_, _>>()?,
            enum_entries: class
                .enum_entries
                .iter()
                .map(|entry| reader.name(entry.name))
                .collect::<Result<_, _>>()?,
            supertypes: reader.types(&class.supertypes, &class.supertype_ids)?,
            context_receivers: reader
                .types(&class.context_receivers, &class.context_receiver_ids)?,
            type_parameters: reader.type_parameters(&class.type_parameters)?,
            constructors: class
                .constructors
                .iter()
                .map(|con| reader.constructor(con))
                .collect::<Result<_, _>>()?,
            members: reader.declarations(
                &class.properties,
                &class.functions,
                &class.type_aliases,
            )?,
        })
    }
}

fn variance(value: i32) -> Result<Variance, KotlinError> {
    match value {
        0 => Ok(Variance::In),
        1 => Ok(Variance::Out),
        2 => Ok(Variance::Invariant),
        _ => Err(KotlinError::Metadata("unknown Kotlin type variance")),
    }
}

fn flags(current: Option<i32>, old: Option<i32>, default: u32) -> Flags {
    Flags(
        current
            .map(|flags| flags as u32)
            .or_else(|| {
                old.map(|old| {
                    let old = old as u32;
                    (old & 0x3f) | ((old >> 8) << 6)
                })
            })
            .unwrap_or(default),
    )
}
