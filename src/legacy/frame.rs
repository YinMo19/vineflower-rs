// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::BTreeMap;

use crate::bytecode::{Instruction, Operand};
use crate::classfile::{Constant, ConstantPool};
use crate::descriptor::{MethodDescriptor, Type};

use super::{LegacyError, invalid};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Value {
    One,
    Two,
    Address(usize),
}

impl Value {
    fn width(self) -> u16 {
        if self == Self::Two { 2 } else { 1 }
    }

    fn runtime_width(self) -> u16 {
        if matches!(self, Self::Address(_)) {
            0
        } else {
            self.width()
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Local {
    Address(usize),
    // An address may reach this slot, but its identity is not known on every path.
    Conflict,
}

/// Track only operand widths and the special return-address type. Other JVM
/// verification types are not needed to distinguish real Java stack effects.
#[derive(Clone, Debug, Default)]
pub(super) struct Frame {
    stack: Vec<Value>,
    addresses: BTreeMap<u16, Local>,
}

impl Frame {
    pub(super) fn exception(&self) -> Self {
        Self {
            stack: vec![Value::One],
            addresses: self.addresses.clone(),
        }
    }

    pub(super) fn merge(&mut self, incoming: &Self, offset: u32) -> Result<bool, LegacyError> {
        if self.stack != incoming.stack {
            return Err(invalid(offset, "incompatible operand stacks at a join"));
        }
        Ok(self.merge_locals(incoming))
    }

    pub(super) fn merge_locals(&mut self, incoming: &Self) -> bool {
        let mut changed = false;
        for (index, local) in &mut self.addresses {
            if *local != Local::Conflict && incoming.addresses.get(index) != Some(&*local) {
                *local = Local::Conflict;
                changed = true;
            }
        }
        for &index in incoming.addresses.keys() {
            self.addresses.entry(index).or_insert_with(|| {
                changed = true;
                Local::Conflict
            });
        }
        changed
    }

    pub(super) fn push_address(&mut self, context: usize) {
        self.stack.push(Value::Address(context));
    }

    pub(super) fn check_ret(
        &self,
        index: u16,
        context: usize,
        offset: u32,
    ) -> Result<(), LegacyError> {
        if self.addresses.get(&index) == Some(&Local::Address(context)) {
            Ok(())
        } else {
            Err(invalid(
                offset,
                "ret does not read the active subroutine's returnAddress",
            ))
        }
    }

    /// Return the projected opcode after removing any returnAddress operands.
    pub(super) fn step(&mut self, op: &Instruction, effect: Effect) -> Result<u8, LegacyError> {
        let bad = |reason| invalid(op.offset, reason);
        match effect {
            Effect::Ordinary { pop, push } => {
                let start = self.group(self.stack.len(), pop, op.offset)?;
                if self.stack[start..]
                    .iter()
                    .any(|value| matches!(value, Value::Address(_)))
                {
                    return Err(bad("returnAddress used as a Java operand"));
                }
                self.stack.truncate(start);
                self.push(push);
            }
            Effect::Read { index, width } => {
                if self.addresses.contains_key(&index)
                    || (width == 2 && self.addresses.contains_key(&second_slot(index, op.offset)?))
                {
                    return Err(bad("returnAddress read as a Java local"));
                }
                self.push(width);
            }
            Effect::Write {
                index,
                width,
                address_allowed,
            } => {
                let value = self
                    .stack
                    .pop()
                    .ok_or_else(|| bad("operand stack underflow"))?;
                if value.width() != width {
                    return Err(bad("local store has the wrong operand width"));
                }
                if let Value::Address(context) = value {
                    if !address_allowed {
                        return Err(bad("returnAddress used as a Java local value"));
                    }
                    self.addresses.insert(index, Local::Address(context));
                    return Ok(0x00);
                }
                self.addresses.remove(&index);
                if width == 2 {
                    self.addresses.remove(&second_slot(index, op.offset)?);
                }
            }
            Effect::Stack => return self.stack_op(op.opcode, op.offset),
        }
        Ok(op.opcode)
    }

    fn push(&mut self, width: u16) {
        match width {
            0 => (),
            1 => self.stack.push(Value::One),
            2 => self.stack.push(Value::Two),
            _ => unreachable!("a value takes at most two slots"),
        }
    }

    fn group(&self, mut end: usize, mut width: u16, offset: u32) -> Result<usize, LegacyError> {
        while width != 0 {
            end = end
                .checked_sub(1)
                .ok_or_else(|| invalid(offset, "operand stack underflow"))?;
            width = width
                .checked_sub(self.stack[end].width())
                .ok_or_else(|| invalid(offset, "stack operation splits a category-2 value"))?;
        }
        Ok(end)
    }

    fn stack_op(&mut self, opcode: u8, offset: u32) -> Result<u8, LegacyError> {
        let end = self.stack.len();
        match opcode {
            0x57 | 0x58 => {
                let start = self.group(end, u16::from(opcode - 0x56), offset)?;
                let runtime = runtime_width(&self.stack[start..]);
                self.stack.truncate(start);
                Ok(if runtime == 0 {
                    0x00
                } else {
                    0x56 + runtime as u8
                })
            }
            0x59..=0x5e => {
                let width = u16::from((opcode - 0x59) / 3 + 1);
                let beneath = u16::from((opcode - 0x59) % 3);
                let start = self.group(end, width, offset)?;
                let insert = self.group(start, beneath, offset)?;
                let runtime = runtime_width(&self.stack[start..]);
                let underneath = runtime_width(&self.stack[insert..start]);
                self.stack.extend_from_within(start..end);
                self.stack[insert..].rotate_right(end - start);
                Ok(if runtime == 0 {
                    0x00
                } else {
                    0x59 + (runtime as u8 - 1) * 3 + underneath as u8
                })
            }
            0x5f => {
                let top = self.group(end, 1, offset)?;
                let lower = self.group(top, 1, offset)?;
                let runtime = runtime_width(&self.stack[lower..]);
                self.stack.swap(top, lower);
                Ok(if runtime == 2 { opcode } else { 0x00 })
            }
            _ => unreachable!("not a JVM stack manipulation opcode"),
        }
    }
}

fn second_slot(index: u16, offset: u32) -> Result<u16, LegacyError> {
    index
        .checked_add(1)
        .ok_or_else(|| invalid(offset, "category-2 local index overflows"))
}

fn runtime_width(values: &[Value]) -> u16 {
    values.iter().copied().map(Value::runtime_width).sum()
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Effect {
    Ordinary {
        pop: u16,
        push: u16,
    },
    Read {
        index: u16,
        width: u16,
    },
    Write {
        index: u16,
        width: u16,
        address_allowed: bool,
    },
    Stack,
}

impl Effect {
    pub(super) fn of(op: &Instruction, pool: &ConstantPool<'_>) -> Result<Self, LegacyError> {
        let opcode = op.opcode;
        let bad = |reason| invalid(op.offset, reason);
        let local = || match op.operand {
            Operand::Local(index) => Ok(index),
            _ => Err(bad("missing local index")),
        };
        let read = |index, width| Ok(Self::Read { index, width });
        let write = |index, kind| {
            Ok(Self::Write {
                index,
                width: numeric_width(kind),
                address_allowed: kind == 4,
            })
        };
        let plain = |pop, push| Ok(Self::Ordinary { pop, push });
        match opcode {
            0x00 | 0xa7 | 0xb1 | 0xc8 => plain(0, 0),
            0x01..=0x08 | 0x0b..=0x0d | 0x10..=0x13 | 0xbb => plain(0, 1),
            0x09..=0x0a | 0x0e..=0x0f | 0x14 => plain(0, 2),
            0x15..=0x19 => read(local()?, numeric_width(opcode - 0x15)),
            0x1a..=0x2d => read(
                u16::from((opcode - 0x1a) % 4),
                numeric_width((opcode - 0x1a) / 4),
            ),
            0x2e..=0x35 => plain(2, numeric_width(opcode - 0x2e)),
            0x36..=0x3a => write(local()?, opcode - 0x36),
            0x3b..=0x4e => write(u16::from((opcode - 0x3b) % 4), (opcode - 0x3b) / 4),
            0x4f..=0x56 => plain(2 + numeric_width(opcode - 0x4f), 0),
            0x57..=0x5f => Ok(Self::Stack),
            0x60..=0x73 => {
                let width = numeric_width((opcode - 0x60) % 4);
                plain(width * 2, width)
            }
            0x74..=0x77 => {
                let width = numeric_width(opcode - 0x74);
                plain(width, width)
            }
            0x78..=0x7d => {
                let width = u16::from(opcode % 2 + 1);
                plain(width + 1, width)
            }
            0x7e..=0x83 => {
                let width = u16::from(opcode % 2 + 1);
                plain(width * 2, width)
            }
            0x84 => match op.operand {
                Operand::Increment { index, .. } => read(index, 0),
                _ => Err(bad("missing iinc local index")),
            },
            0x85 | 0x87 | 0x8c | 0x8d => plain(1, 2),
            0x86 | 0x8b | 0x91..=0x93 => plain(1, 1),
            0x88 | 0x89 | 0x8e | 0x90 => plain(2, 1),
            0x8a | 0x8f => plain(2, 2),
            0x94 | 0x97 | 0x98 => plain(4, 1),
            0x95 | 0x96 => plain(2, 1),
            0x99..=0x9e | 0xaa | 0xab | 0xbf | 0xc2 | 0xc3 | 0xc6 | 0xc7 => plain(1, 0),
            0x9f..=0xa6 => plain(2, 0),
            0xac..=0xb0 => plain(numeric_width(opcode - 0xac), 0),
            0xb2..=0xb5 => {
                let Operand::Constant(index) = op.operand else {
                    return Err(bad("missing field constant index"));
                };
                let (_, _, descriptor) = pool
                    .member_ref(index)
                    .map_err(|_| bad("invalid field constant"))?;
                let width = Type::parse(descriptor)
                    .map_err(|_| bad("invalid field descriptor"))?
                    .slots();
                let receiver = u16::from(opcode >= 0xb4);
                if opcode % 2 == 0 {
                    plain(receiver, width)
                } else {
                    plain(receiver + width, 0)
                }
            }
            0xb6..=0xba => {
                let index = match op.operand {
                    Operand::Constant(index) | Operand::InvokeInterface { index, .. } => index,
                    _ => return Err(bad("missing invocation constant index")),
                };
                let descriptor = if opcode == 0xba {
                    let Ok(Constant::InvokeDynamic {
                        name_and_type_index,
                        ..
                    }) = pool.get(index)
                    else {
                        return Err(bad("invalid invokedynamic constant"));
                    };
                    pool.name_and_type(*name_and_type_index)
                        .map_err(|_| bad("invalid invokedynamic name and type"))?
                        .1
                } else {
                    pool.member_ref(index)
                        .map_err(|_| bad("invalid method constant"))?
                        .2
                };
                let method = MethodDescriptor::parse(descriptor)
                    .map_err(|_| bad("invalid method descriptor"))?;
                let receiver = u16::from(!matches!(opcode, 0xb8 | 0xba));
                plain(
                    receiver + method.parameters.iter().map(Type::slots).sum::<u16>(),
                    method.return_type.slots(),
                )
            }
            0xbc..=0xbe | 0xc0 | 0xc1 => plain(1, 1),
            0xc5 => match op.operand {
                Operand::MultiANewArray { dimensions, .. } => plain(u16::from(dimensions), 1),
                _ => Err(bad("missing multianewarray dimensions")),
            },
            _ => Err(bad("unexpected opcode during returnAddress analysis")),
        }
    }
}

fn numeric_width(kind: u8) -> u16 {
    if matches!(kind, 1 | 3) { 2 } else { 1 }
}
