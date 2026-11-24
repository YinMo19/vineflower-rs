// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! Stack map frames and verification types (JVMS §4.7.4).

use std::borrow::Cow;

use super::{ClassError, ClassFile, Code, ConstantPool, Member, Reader};
use crate::{
    bytecode::Instruction,
    descriptor::{MethodDescriptor, Primitive, Type},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VerificationType<'types> {
    Top,
    Integer,
    Float,
    Double,
    Long,
    Null,
    UninitializedThis,
    /// Index of a `CONSTANT_Class_info` entry (including array classes).
    Object(u16),
    /// Bytecode offset of the allocation's `new` instruction.
    Uninitialized(u16),
    /// Reference inherited from the implicit entry frame. The descriptor type
    /// need not have a `CONSTANT_Class_info` entry in this class file.
    DescriptorReference(&'types Type),
}

impl VerificationType<'_> {
    pub const fn slots(self) -> u16 {
        match self {
            Self::Long | Self::Double => 2,
            _ => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StackMapFrame<'frame, 'types> {
    pub offset: u16,
    /// Local types, in slot order. Wide types occupy a single entry here.
    /// Local slots not described by this slice have type `Top`.
    pub locals: &'frame [VerificationType<'types>],
    /// Operand types, from bottom to top. Wide types occupy a single entry here.
    pub stack: &'frame [VerificationType<'types>],
}

impl<'types> StackMapFrame<'_, 'types> {
    /// Lookup by JVM local slot, rather than by verification-type index.
    pub fn local(&self, mut slot: u16) -> VerificationType<'types> {
        for &ty in self.locals {
            if slot == 0 {
                return ty;
            }
            let Some(next) = slot.checked_sub(ty.slots()) else {
                break;
            };
            slot = next;
        }
        VerificationType::Top
    }
}

#[derive(Debug, thiserror::Error)]
pub enum StackMapError {
    #[error(transparent)]
    Class(#[from] ClassError),
    #[error("Code has multiple StackMapTable attributes")]
    DuplicateAttribute,
    #[error("StackMapTable has {count} frames for code_length {code_length}")]
    TooManyFrames { count: u16, code_length: usize },
    #[error("reserved StackMapTable frame tag {0}")]
    ReservedFrameTag(u8),
    #[error("invalid StackMapTable verification type tag {0}")]
    InvalidTypeTag(u8),
    #[error("StackMapTable frame offset {0} is outside the code array")]
    FrameOutOfBounds(u32),
    #[error("StackMapTable frame offset {0} is not an instruction start")]
    FrameNotInstruction(u16),
    #[error("StackMapTable uninitialized offset {0} is outside the code array")]
    UninitializedOutOfBounds(u16),
    #[error("StackMapTable uninitialized offset {0} does not identify a new instruction")]
    UninitializedNotNew(u16),
    #[error("StackMapTable chop of {count} locals exceeds previous frame's {available} entries")]
    InvalidChop { count: usize, available: usize },
    #[error("StackMapTable {kind} exceed the limit of {limit} slots")]
    TooManySlots { kind: &'static str, limit: u16 },
}

/// The receiver and parameters of the implicit initial frame (JVMS §4.10.1.5).
/// Supply the parsed descriptor of `member` in `class`.
pub fn initial_stack_map_locals<'types>(
    class: &ClassFile<'_>,
    member: &Member<'_>,
    descriptor: &'types MethodDescriptor,
) -> Result<Vec<VerificationType<'types>>, ClassError> {
    use VerificationType::*;

    let has_receiver = member.access_flags & 0x0008 == 0; // ACC_STATIC
    let mut locals = Vec::with_capacity(descriptor.parameters.len() + usize::from(has_receiver));
    if has_receiver {
        let receiver = if class.super_class != 0
            && class.pool.expect_utf8(member.name_index)?.as_str() == Some("<init>")
        {
            UninitializedThis
        } else {
            Object(class.this_class)
        };
        locals.push(receiver);
    }
    locals.extend(
        descriptor
            .parameters
            .iter()
            .map(|parameter| match parameter {
                Type::Primitive(primitive) => match primitive {
                    Primitive::Boolean
                    | Primitive::Byte
                    | Primitive::Char
                    | Primitive::Short
                    | Primitive::Int => Integer,
                    Primitive::Float => Float,
                    Primitive::Double => Double,
                    Primitive::Long => Long,
                },
                Type::Object(_) | Type::Array(_) => DescriptorReference(parameter),
                Type::Void => unreachable!("void is not a parsed parameter type"),
            }),
    );
    Ok(locals)
}

impl Code<'_> {
    /// Visit explicit stack map frames in ascending bytecode-offset order,
    /// reusing the local and operand buffers across frames. Returns `false`
    /// if the attribute is absent (an implicit empty table since version 50.0).
    ///
    /// `initial_locals` is the compact list from the method's implicit entry
    /// frame, e.g. [`initial_stack_map_locals`]. If supplied, `instructions`
    /// must be the decoded, ordered instruction list for this code array. It
    /// lets this decoder validate instruction boundaries and `new` opcodes;
    /// offsets are still range-checked without it. This is not a verifier.
    ///
    /// The visitor may have received valid frames before an error is found.
    pub fn visit_stack_map_frames<'types>(
        &self,
        pool: &ConstantPool<'_>,
        initial_locals: &[VerificationType<'types>],
        instructions: Option<&[Instruction]>,
        mut visit: impl FnMut(StackMapFrame<'_, 'types>),
    ) -> Result<bool, StackMapError> {
        let mut attribute = None;
        for item in &self.attributes {
            if pool.expect_utf8(item.name_index)?.as_str() == Some("StackMapTable")
                && attribute.replace(item.data).is_some()
            {
                return Err(StackMapError::DuplicateAttribute);
            }
        }
        let Some(data) = attribute else {
            return Ok(false);
        };
        let mut reader = Reader::new(data);
        let count = reader.u16()?;
        let code_length = self.bytes.len();
        if usize::from(count) > code_length {
            return Err(StackMapError::TooManyFrames { count, code_length });
        }
        reader.require(usize::from(count))?;
        if count != 0 {
            let context = Context {
                pool,
                instructions,
                code_length,
            };
            let mut locals = Types::new(self.max_locals, "locals");
            let mut stack = Types::new(self.max_stack, "operand stack entries");
            locals.seed(initial_locals)?;
            let mut previous = None;
            for _ in 0..count {
                let tag = reader.u8()?;
                let delta = match tag {
                    0..=63 => u16::from(tag),
                    64..=127 => u16::from(tag - 64),
                    247..=255 => reader.u16()?,
                    _ => return Err(StackMapError::ReservedFrameTag(tag)),
                };
                let offset = context.frame_offset(previous, delta)?;
                stack.clear();
                match tag {
                    0..=63 | 251 => {}
                    64..=127 | 247 => stack.read(&context, &mut reader, 1)?,
                    248..=250 => locals.chop(usize::from(251 - tag))?,
                    252..=254 => locals.read(&context, &mut reader, u16::from(tag - 251))?,
                    255 => {
                        locals.clear();
                        let count = reader.u16()?;
                        locals.read(&context, &mut reader, count)?;
                        let count = reader.u16()?;
                        stack.read(&context, &mut reader, count)?;
                    }
                    _ => unreachable!("reserved frame tags were rejected"),
                }
                visit(StackMapFrame {
                    offset,
                    locals: &locals.entries,
                    stack: &stack.entries,
                });
                previous = Some(offset);
            }
        }
        reader.finish("StackMapTable")?;
        Ok(true)
    }
}

struct Context<'pool, 'class, 'code> {
    pool: &'pool ConstantPool<'class>,
    instructions: Option<&'code [Instruction]>,
    code_length: usize,
}

impl Context<'_, '_, '_> {
    fn frame_offset(&self, previous: Option<u16>, delta: u16) -> Result<u16, StackMapError> {
        let offset = previous.map_or(0, |pc| u32::from(pc) + 1) + u32::from(delta);
        let pc = u16::try_from(offset).map_err(|_| StackMapError::FrameOutOfBounds(offset))?;
        if usize::from(pc) >= self.code_length {
            return Err(StackMapError::FrameOutOfBounds(offset));
        }
        if self
            .instructions
            .is_some_and(|code| instruction_at(code, pc).is_none())
        {
            return Err(StackMapError::FrameNotInstruction(pc));
        }
        Ok(pc)
    }

    fn read_type(
        &self,
        reader: &mut Reader<'_>,
    ) -> Result<VerificationType<'static>, StackMapError> {
        use VerificationType::*;

        Ok(match reader.u8()? {
            0 => Top,
            1 => Integer,
            2 => Float,
            3 => Double,
            4 => Long,
            5 => Null,
            6 => UninitializedThis,
            7 => {
                let index = reader.u16()?;
                self.pool.expect_class(index)?;
                Object(index)
            }
            8 => {
                let offset = reader.u16()?;
                if usize::from(offset) >= self.code_length {
                    return Err(StackMapError::UninitializedOutOfBounds(offset));
                }
                if self.instructions.is_some_and(|code| {
                    !matches!(
                        instruction_at(code, offset),
                        Some(Instruction { opcode: 0xbb, .. })
                    )
                }) {
                    return Err(StackMapError::UninitializedNotNew(offset));
                }
                Uninitialized(offset)
            }
            tag => return Err(StackMapError::InvalidTypeTag(tag)),
        })
    }
}

fn instruction_at(instructions: &[Instruction], offset: u16) -> Option<&Instruction> {
    let i = instructions
        .binary_search_by_key(&u32::from(offset), |instruction| instruction.offset)
        .ok()?;
    Some(&instructions[i])
}

struct Types<'entries, 'types> {
    entries: Cow<'entries, [VerificationType<'types>]>,
    slots: u16,
    limit: u16,
    kind: &'static str,
}

impl<'entries, 'types> Types<'entries, 'types> {
    fn new(limit: u16, kind: &'static str) -> Self {
        Self {
            entries: Cow::Owned(Vec::new()),
            slots: 0,
            limit,
            kind,
        }
    }

    fn seed(&mut self, entries: &'entries [VerificationType<'types>]) -> Result<(), StackMapError> {
        for &ty in entries {
            let slots = ty.slots();
            if slots > self.limit - self.slots {
                return Err(self.limit_error());
            }
            self.slots += slots;
        }
        self.entries = Cow::Borrowed(entries);
        Ok(())
    }

    fn clear(&mut self) {
        self.truncate(0);
        self.slots = 0;
    }

    fn chop(&mut self, count: usize) -> Result<(), StackMapError> {
        let available = self.entries.len();
        let remaining = available
            .checked_sub(count)
            .ok_or(StackMapError::InvalidChop { count, available })?;
        self.slots -= self.entries[remaining..]
            .iter()
            .map(|ty| ty.slots())
            .sum::<u16>();
        self.truncate(remaining);
        Ok(())
    }

    fn truncate(&mut self, count: usize) {
        match &mut self.entries {
            Cow::Borrowed(entries) => *entries = &entries[..count],
            Cow::Owned(entries) => entries.truncate(count),
        }
    }

    fn read(
        &mut self,
        context: &Context<'_, '_, '_>,
        reader: &mut Reader<'_>,
        count: u16,
    ) -> Result<(), StackMapError> {
        if count == 0 {
            return Ok(());
        }
        // Every entry needs at least one slot and one tag byte.
        if count > self.limit - self.slots {
            return Err(self.limit_error());
        }
        reader.require(usize::from(count))?;
        let count = usize::from(count);
        if let Cow::Borrowed(previous) = self.entries {
            let mut entries = Vec::with_capacity(previous.len() + count);
            entries.extend_from_slice(previous);
            self.entries = Cow::Owned(entries);
        }
        let entries = self.entries.to_mut();
        entries.reserve(count);
        for _ in 0..count {
            let ty = context.read_type(reader)?;
            let slots = ty.slots();
            if slots > self.limit - self.slots {
                return Err(StackMapError::TooManySlots {
                    kind: self.kind,
                    limit: self.limit,
                });
            }
            self.slots += slots;
            entries.push(ty);
        }
        Ok(())
    }

    fn limit_error(&self) -> StackMapError {
        StackMapError::TooManySlots {
            kind: self.kind,
            limit: self.limit,
        }
    }
}
