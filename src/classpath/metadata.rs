use crate::classfile::{ClassError, ClassFile, ConstantPool, Member};

use super::{ClassPathError, source::Source};

/// Owned declaration metadata for a classpath class. Names are JVM internal
/// names; descriptors and signatures retain their class-file encoding.
#[derive(Debug, PartialEq, Eq)]
pub struct ClassMetadata {
    pub name: String,
    pub super_name: Option<String>,
    pub interfaces: Vec<String>,
    pub permitted_subclasses: Vec<String>,
    pub access_flags: u16,
    pub signature: Option<String>,
    pub methods: Vec<MemberMetadata>,
    pub fields: Vec<MemberMetadata>,
}

/// The declaration of a field or method, without code or initializer data.
#[derive(Debug, PartialEq, Eq)]
pub struct MemberMetadata {
    pub name: String,
    pub descriptor: String,
    pub access_flags: u16,
    pub signature: Option<String>,
}

impl ClassMetadata {
    pub(super) fn read(name: &str, source: &Source, bytes: &[u8]) -> Result<Self, ClassPathError> {
        let invalid_class = |error| ClassPathError::InvalidClass {
            location: source.location(),
            name: name.into(),
            source: error,
        };
        let class = ClassFile::parse(bytes).map_err(invalid_class)?;
        let declared = class.pool.class_name(class.this_class).map_err(invalid_class)?;
        if declared != name {
            return Err(ClassPathError::WrongClassName {
                location: source.location(),
                requested: name.into(),
                declared: declared.into(),
            });
        }
        Self::from_class(name, &class).map_err(invalid_class)
    }

    fn from_class(name: &str, class: &ClassFile<'_>) -> Result<Self, ClassError> {
        let pool = &class.pool;
        Ok(Self {
            name: name.into(),
            super_name: if class.super_class == 0 {
                None
            } else {
                Some(pool.class_name(class.super_class)?.into())
            },
            interfaces: class.interfaces.iter().map(|&index| pool.class_name(index).map(str::to_owned))
                .collect::<Result<_, _>>()?,
            permitted_subclasses: class.permitted_subclasses()?.into_iter()
                .map(|index| pool.class_name(index).map(str::to_owned))
                .collect::<Result<_, _>>()?,
            access_flags: class.access_flags,
            signature: class.signature()?.map(str::to_owned),
            methods: class.methods.iter().map(|m| MemberMetadata::from_member(m, pool))
                .collect::<Result<_, _>>()?,
            fields: class.fields.iter().map(|m| MemberMetadata::from_member(m, pool))
                .collect::<Result<_, _>>()?,
        })
    }
}

impl MemberMetadata {
    fn from_member<'a>(member: &Member<'a>, pool: &ConstantPool<'a>) -> Result<Self, ClassError> {
        Ok(Self {
            name: pool.utf8(member.name_index)?.into(),
            descriptor: pool.utf8(member.descriptor_index)?.into(),
            access_flags: member.access_flags,
            signature: member.signature(pool)?.map(str::to_owned),
        })
    }
}
