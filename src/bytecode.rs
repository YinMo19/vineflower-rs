// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    /// Byte offset relative to the start of the method's code array.
    pub offset: u32,
    /// JVM opcode, or the modified opcode for a `wide` instruction.
    pub opcode: u8,
    pub operand: Operand,
    /// Encoded length, including any prefix or padding bytes.
    pub len: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    None,
    Immediate(i32),
    Local(u16),
    Constant(u16),
    Increment {
        index: u16,
        amount: i16,
    },
    Branch(u32),
    Switch {
        default: u32,
        cases: Vec<(i32, u32)>,
    },
    NewArray(u8),
    InvokeInterface {
        index: u16,
        count: u8,
    },
    MultiANewArray {
        index: u16,
        dimensions: u8,
    },
}

impl Instruction {
    /// Slots touched by a load, store, or increment, and whether the instruction
    /// reads the incoming value. An increment reads before writing its slot.
    pub(crate) fn local_access(&self) -> Option<(std::ops::Range<u32>, bool)> {
        let (slot, kind, read) = match (self.opcode, &self.operand) {
            (code @ 0x15..=0x19, Operand::Local(slot)) => (*slot, code - 0x15, true),
            (code @ 0x1a..=0x2d, _) => (u16::from((code - 0x1a) % 4), (code - 0x1a) / 4, true),
            (code @ 0x36..=0x3a, Operand::Local(slot)) => (*slot, code - 0x36, false),
            (code @ 0x3b..=0x4e, _) => (u16::from((code - 0x3b) % 4), (code - 0x3b) / 4, false),
            (0x84, Operand::Increment { index, .. }) => (*index, 0, true),
            _ => return None,
        };
        let slot = u32::from(slot);
        Some((slot..slot + if matches!(kind, 1 | 3) { 2 } else { 1 }, read))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum BytecodeError {
    #[error("bytecode exceeds the representable size")]
    CodeTooLong,
    #[error("truncated instruction at bytecode offset {offset}")]
    Truncated { offset: u32 },
    #[error("unknown or reserved opcode {opcode:#04x} at bytecode offset {offset}")]
    InvalidOpcode { offset: u32, opcode: u8 },
    #[error("invalid operand at bytecode offset {offset}: {reason}")]
    InvalidOperand { offset: u32, reason: &'static str },
    #[error("branch at bytecode offset {offset} targets {target}, not an instruction start")]
    InvalidTarget { offset: u32, target: i64 },
}

/// Decode a method's code array. Branch and switch operands contain absolute
/// code-array offsets; targets must point to the start of an instruction.
/// Class-version, constant-pool entry types, and stack/local constraints are
/// not checked here.
pub fn decode(bytes: &[u8]) -> Result<Vec<Instruction>, BytecodeError> {
    let code_len = u32::try_from(bytes.len()).map_err(|_| BytecodeError::CodeTooLong)?;
    let mut instructions = Vec::new();
    let mut reader = Reader {
        rest: bytes,
        offset: 0,
        code_len,
    };
    while !reader.rest.is_empty() {
        reader.offset = code_len - reader.rest.len() as u32;
        let (opcode, operand) = reader.instruction()?;
        instructions.push(Instruction {
            offset: reader.offset,
            opcode,
            operand,
            len: code_len - reader.rest.len() as u32 - reader.offset,
        });
    }

    for instruction in &instructions {
        let check = |target: u32| {
            instructions
                .binary_search_by_key(&target, |insn| insn.offset)
                .map(|_| ())
                .map_err(|_| BytecodeError::InvalidTarget {
                    offset: instruction.offset,
                    target: i64::from(target),
                })
        };
        match &instruction.operand {
            Operand::Branch(target) => check(*target)?,
            Operand::Switch { default, cases } => {
                check(*default)?;
                for &(_, target) in cases {
                    check(target)?;
                }
            }
            _ => {}
        }
    }
    Ok(instructions)
}

struct Reader<'a> {
    rest: &'a [u8],
    offset: u32,
    code_len: u32,
}

impl Reader<'_> {
    fn read<const N: usize>(&mut self) -> Result<[u8; N], BytecodeError> {
        let (prefix, rest) = self.rest.split_first_chunk::<N>().ok_or(self.truncated())?;
        self.rest = rest;
        Ok(*prefix)
    }

    fn byte(&mut self) -> Result<u8, BytecodeError> {
        let [byte] = self.read()?;
        Ok(byte)
    }

    fn truncated(&self) -> BytecodeError {
        BytecodeError::Truncated {
            offset: self.offset,
        }
    }

    fn invalid(&self, reason: &'static str) -> BytecodeError {
        BytecodeError::InvalidOperand {
            offset: self.offset,
            reason,
        }
    }

    fn nonzero_index(&self, index: u16) -> Result<u16, BytecodeError> {
        if index == 0 {
            return Err(self.invalid("constant-pool index is zero"));
        }
        Ok(index)
    }

    fn constant_index(&mut self) -> Result<u16, BytecodeError> {
        let index = u16::from_be_bytes(self.read()?);
        self.nonzero_index(index)
    }

    fn target(&self, delta: i32) -> Result<u32, BytecodeError> {
        let target = i64::from(self.offset) + i64::from(delta);
        if !(0..i64::from(self.code_len)).contains(&target) {
            return Err(BytecodeError::InvalidTarget {
                offset: self.offset,
                target,
            });
        }
        Ok(target as u32)
    }

    fn instruction(&mut self) -> Result<(u8, Operand), BytecodeError> {
        use Operand::*;

        let opcode = self.byte()?;
        let operand = match opcode {
            // Compact forms have implicit operands and retain their original opcodes.
            0x00..=0x0f
            | 0x1a..=0x35
            | 0x3b..=0x83
            | 0x85..=0x98
            | 0xac..=0xb1
            | 0xbe..=0xbf
            | 0xc2..=0xc3 => None,
            0x10 => Immediate(i32::from(i8::from_be_bytes(self.read()?))),
            0x11 => Immediate(i32::from(i16::from_be_bytes(self.read()?))),
            0x12 => {
                let index = u16::from(self.byte()?);
                Constant(self.nonzero_index(index)?)
            }
            0x13..=0x14 | 0xb2..=0xb8 | 0xbb | 0xbd | 0xc0..=0xc1 => {
                Constant(self.constant_index()?)
            }
            0x15..=0x19 | 0x36..=0x3a | 0xa9 => Local(u16::from(self.byte()?)),
            0x84 => Increment {
                index: u16::from(self.byte()?),
                amount: i16::from(i8::from_be_bytes(self.read()?)),
            },
            0x99..=0xa8 | 0xc6..=0xc7 => {
                let delta = i16::from_be_bytes(self.read()?);
                Branch(self.target(i32::from(delta))?)
            }
            0xaa | 0xab => self.switch(opcode == 0xaa)?,
            0xb9 => {
                let index = self.constant_index()?;
                let [count, zero] = self.read()?;
                if count == 0 || zero != 0 {
                    return Err(self.invalid(
                        "invokeinterface needs a nonzero count and a zero trailing byte",
                    ));
                }
                InvokeInterface { index, count }
            }
            0xba => {
                let index = self.constant_index()?;
                if self.read()? != [0, 0] {
                    return Err(self.invalid("invokedynamic needs two zero trailing bytes"));
                }
                Constant(index)
            }
            0xbc => {
                let atype = self.byte()?;
                if !(4..=11).contains(&atype) {
                    return Err(self.invalid("invalid newarray type"));
                }
                NewArray(atype)
            }
            0xc4 => return self.wide(),
            0xc5 => {
                let index = self.constant_index()?;
                let dimensions = self.byte()?;
                if dimensions == 0 {
                    return Err(self.invalid("multianewarray dimensions must be nonzero"));
                }
                MultiANewArray { index, dimensions }
            }
            0xc8..=0xc9 => {
                let delta = i32::from_be_bytes(self.read()?);
                Branch(self.target(delta)?)
            }
            _ => {
                return Err(BytecodeError::InvalidOpcode {
                    offset: self.offset,
                    opcode,
                });
            }
        };
        Ok((opcode, operand))
    }

    fn wide(&mut self) -> Result<(u8, Operand), BytecodeError> {
        let opcode = self.byte()?;
        let operand = match opcode {
            0x15..=0x19 | 0x36..=0x3a | 0xa9 => Operand::Local(u16::from_be_bytes(self.read()?)),
            0x84 => Operand::Increment {
                index: u16::from_be_bytes(self.read()?),
                amount: i16::from_be_bytes(self.read()?),
            },
            _ => return Err(self.invalid("opcode cannot be modified by wide")),
        };
        Ok((opcode, operand))
    }

    fn switch(&mut self, table: bool) -> Result<Operand, BytecodeError> {
        // Word alignment is relative to the code array, not the switch opcode.
        let padding = (3 - self.offset % 4) as usize;
        self.rest = self.rest.get(padding..).ok_or(self.truncated())?;
        let default_delta = i32::from_be_bytes(self.read()?);
        let (count, low, entry_len) = if table {
            let low = i32::from_be_bytes(self.read()?);
            let high = i32::from_be_bytes(self.read()?);
            if high < low {
                return Err(self.invalid("tableswitch high key is below low key"));
            }
            (i64::from(high) - i64::from(low) + 1, low, 4)
        } else {
            let count = i32::from_be_bytes(self.read()?);
            if count < 0 {
                return Err(self.invalid("negative lookupswitch pair count"));
            }
            (i64::from(count), 0, 8)
        };
        let count = usize::try_from(count).map_err(|_| self.truncated())?;
        if count > self.rest.len() / entry_len {
            return Err(self.truncated());
        }

        let default = self.target(default_delta)?;
        let mut cases = Vec::with_capacity(count);
        for i in 0..count {
            let key = if table {
                // The encoded high key guarantees that this sum fits in i32.
                (i64::from(low) + i as i64) as i32
            } else {
                let key = i32::from_be_bytes(self.read()?);
                if cases.last().is_some_and(|&(previous, _)| key <= previous) {
                    return Err(self.invalid("lookupswitch keys are not strictly increasing"));
                }
                key
            };
            let delta = i32::from_be_bytes(self.read()?);
            cases.push((key, self.target(delta)?));
        }
        Ok(Operand::Switch { default, cases })
    }
}

/// JVM opcode mnemonic, including the three named reserved opcodes.
pub fn opcode_name(opcode: u8) -> Option<&'static str> {
    const NAMES: [&str; 203] = [
        "nop",
        "aconst_null",
        "iconst_m1",
        "iconst_0",
        "iconst_1",
        "iconst_2",
        "iconst_3",
        "iconst_4",
        "iconst_5",
        "lconst_0",
        "lconst_1",
        "fconst_0",
        "fconst_1",
        "fconst_2",
        "dconst_0",
        "dconst_1",
        "bipush",
        "sipush",
        "ldc",
        "ldc_w",
        "ldc2_w",
        "iload",
        "lload",
        "fload",
        "dload",
        "aload",
        "iload_0",
        "iload_1",
        "iload_2",
        "iload_3",
        "lload_0",
        "lload_1",
        "lload_2",
        "lload_3",
        "fload_0",
        "fload_1",
        "fload_2",
        "fload_3",
        "dload_0",
        "dload_1",
        "dload_2",
        "dload_3",
        "aload_0",
        "aload_1",
        "aload_2",
        "aload_3",
        "iaload",
        "laload",
        "faload",
        "daload",
        "aaload",
        "baload",
        "caload",
        "saload",
        "istore",
        "lstore",
        "fstore",
        "dstore",
        "astore",
        "istore_0",
        "istore_1",
        "istore_2",
        "istore_3",
        "lstore_0",
        "lstore_1",
        "lstore_2",
        "lstore_3",
        "fstore_0",
        "fstore_1",
        "fstore_2",
        "fstore_3",
        "dstore_0",
        "dstore_1",
        "dstore_2",
        "dstore_3",
        "astore_0",
        "astore_1",
        "astore_2",
        "astore_3",
        "iastore",
        "lastore",
        "fastore",
        "dastore",
        "aastore",
        "bastore",
        "castore",
        "sastore",
        "pop",
        "pop2",
        "dup",
        "dup_x1",
        "dup_x2",
        "dup2",
        "dup2_x1",
        "dup2_x2",
        "swap",
        "iadd",
        "ladd",
        "fadd",
        "dadd",
        "isub",
        "lsub",
        "fsub",
        "dsub",
        "imul",
        "lmul",
        "fmul",
        "dmul",
        "idiv",
        "ldiv",
        "fdiv",
        "ddiv",
        "irem",
        "lrem",
        "frem",
        "drem",
        "ineg",
        "lneg",
        "fneg",
        "dneg",
        "ishl",
        "lshl",
        "ishr",
        "lshr",
        "iushr",
        "lushr",
        "iand",
        "land",
        "ior",
        "lor",
        "ixor",
        "lxor",
        "iinc",
        "i2l",
        "i2f",
        "i2d",
        "l2i",
        "l2f",
        "l2d",
        "f2i",
        "f2l",
        "f2d",
        "d2i",
        "d2l",
        "d2f",
        "i2b",
        "i2c",
        "i2s",
        "lcmp",
        "fcmpl",
        "fcmpg",
        "dcmpl",
        "dcmpg",
        "ifeq",
        "ifne",
        "iflt",
        "ifge",
        "ifgt",
        "ifle",
        "if_icmpeq",
        "if_icmpne",
        "if_icmplt",
        "if_icmpge",
        "if_icmpgt",
        "if_icmple",
        "if_acmpeq",
        "if_acmpne",
        "goto",
        "jsr",
        "ret",
        "tableswitch",
        "lookupswitch",
        "ireturn",
        "lreturn",
        "freturn",
        "dreturn",
        "areturn",
        "return",
        "getstatic",
        "putstatic",
        "getfield",
        "putfield",
        "invokevirtual",
        "invokespecial",
        "invokestatic",
        "invokeinterface",
        "invokedynamic",
        "new",
        "newarray",
        "anewarray",
        "arraylength",
        "athrow",
        "checkcast",
        "instanceof",
        "monitorenter",
        "monitorexit",
        "wide",
        "multianewarray",
        "ifnull",
        "ifnonnull",
        "goto_w",
        "jsr_w",
        "breakpoint",
    ];
    match opcode {
        0xfe => Some("impdep1"),
        0xff => Some("impdep2"),
        _ => NAMES.get(usize::from(opcode)).copied(),
    }
}
