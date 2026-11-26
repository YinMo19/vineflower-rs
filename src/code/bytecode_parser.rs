// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The bytecode decoder of `struct.StructMethod`: `parseBytecode` and the
//! tables it expands the single-byte forms of instructions with.

use std::io;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::bytecode_version::BytecodeVersion;
use super::code_constants::*;
use super::exception_table::{ExceptionHandler, ExceptionTable};
use super::instruction::{Instruction, Operands};
use super::instruction_sequence::FullInstructionSequence;
use crate::structs::consts::ConstantPool;
use crate::util::data_input::DataInputFullStream;

const OPR_ICONST: [i32; 7] = [-1, 0, 1, 2, 3, 4, 5];
const OPR_LOADSTORE: [i32; 20] = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3];
const OPCS_LOAD: [i32; 5] = [OPC_ILOAD, OPC_LLOAD, OPC_FLOAD, OPC_DLOAD, OPC_ALOAD];
const OPCS_STORE: [i32; 5] = [OPC_ISTORE, OPC_LSTORE, OPC_FSTORE, OPC_DSTORE, OPC_ASTORE];

/// `StructMethod.parseBytecode`: decodes the code array and the exception
/// table of a `Code` attribute, laid out as `StructCodeAttribute` keeps them.
pub fn parse_bytecode(
    code_and_exceptions: &[u8],
    pool: &ConstantPool,
    bytecode_version: BytecodeVersion,
) -> io::Result<FullInstructionSequence> {
    let mut input = DataInputFullStream::new(code_and_exceptions);

    let mut instructions = Vec::new();
    let mut offset_to_index = FxHashMap::default();

    let length = input.read_int()?;
    let mut i = 0;
    while i < length {
        let offset = i;

        let mut opcode = input.read_unsigned_byte()?;
        let mut group = GROUP_GENERAL;

        let wide = opcode == OPC_WIDE;

        if wide {
            i += 1;
            opcode = input.read_unsigned_byte()?;
        }

        let mut operands = Operands::default();

        if (OPC_ICONST_M1..=OPC_ICONST_5).contains(&opcode) {
            operands.push(OPR_ICONST[(opcode - OPC_ICONST_M1) as usize]);
            opcode = OPC_BIPUSH;
        } else if (OPC_ILOAD_0..=OPC_ALOAD_3).contains(&opcode) {
            operands.push(OPR_LOADSTORE[(opcode - OPC_ILOAD_0) as usize]);
            opcode = OPCS_LOAD[((opcode - OPC_ILOAD_0) / 4) as usize];
        } else if (OPC_ISTORE_0..=OPC_ASTORE_3).contains(&opcode) {
            operands.push(OPR_LOADSTORE[(opcode - OPC_ISTORE_0) as usize]);
            opcode = OPCS_STORE[((opcode - OPC_ISTORE_0) / 4) as usize];
        } else {
            match opcode {
                OPC_BIPUSH => {
                    operands.push(i32::from(input.read_byte()?));
                    i += 1;
                }
                OPC_LDC | OPC_NEWARRAY => {
                    operands.push(input.read_unsigned_byte()?);
                    i += 1;
                }
                OPC_SIPUSH
                | OPC_IFEQ
                | OPC_IFNE
                | OPC_IFLT
                | OPC_IFGE
                | OPC_IFGT
                | OPC_IFLE
                | OPC_IF_ICMPEQ
                | OPC_IF_ICMPNE
                | OPC_IF_ICMPLT
                | OPC_IF_ICMPGE
                | OPC_IF_ICMPGT
                | OPC_IF_ICMPLE
                | OPC_IF_ACMPEQ
                | OPC_IF_ACMPNE
                | OPC_GOTO
                | OPC_JSR
                | OPC_IFNULL
                | OPC_IFNONNULL => {
                    if opcode != OPC_SIPUSH {
                        group = GROUP_JUMP;
                    }
                    operands.push(i32::from(input.read_short()?));
                    i += 2;
                }
                OPC_LDC_W
                | OPC_LDC2_W
                | OPC_GETSTATIC
                | OPC_PUTSTATIC
                | OPC_GETFIELD
                | OPC_PUTFIELD
                | OPC_INVOKEVIRTUAL
                | OPC_INVOKESPECIAL
                | OPC_INVOKESTATIC
                | OPC_NEW
                | OPC_ANEWARRAY
                | OPC_CHECKCAST
                | OPC_INSTANCEOF => {
                    operands.push(input.read_unsigned_short()?);
                    i += 2;
                    if (OPC_GETSTATIC..=OPC_PUTFIELD).contains(&opcode) {
                        group = GROUP_FIELDACCESS;
                    } else if (OPC_INVOKEVIRTUAL..=OPC_INVOKESTATIC).contains(&opcode) {
                        group = GROUP_INVOCATION;
                    }
                }
                OPC_INVOKEDYNAMIC => {
                    // instruction unused in Java 6 and before
                    if bytecode_version.has_invoke_dynamic() {
                        operands.push(input.read_unsigned_short()?);
                        input.discard(2)?;
                        group = GROUP_INVOCATION;
                        i += 4;
                    }
                }
                OPC_ILOAD | OPC_LLOAD | OPC_FLOAD | OPC_DLOAD | OPC_ALOAD | OPC_ISTORE
                | OPC_LSTORE | OPC_FSTORE | OPC_DSTORE | OPC_ASTORE | OPC_RET => {
                    if wide {
                        operands.push(input.read_unsigned_short()?);
                        i += 2;
                    } else {
                        operands.push(input.read_unsigned_byte()?);
                        i += 1;
                    }
                    if opcode == OPC_RET {
                        group = GROUP_RETURN;
                    }
                }
                OPC_IINC => {
                    if wide {
                        operands.push(input.read_unsigned_short()?);
                        operands.push(i32::from(input.read_short()?));
                        i += 4;
                    } else {
                        operands.push(input.read_unsigned_byte()?);
                        operands.push(i32::from(input.read_byte()?));
                        i += 2;
                    }
                }
                OPC_GOTO_W | OPC_JSR_W => {
                    opcode = if opcode == OPC_JSR_W { OPC_JSR } else { OPC_GOTO };
                    operands.push(input.read_int()?);
                    group = GROUP_JUMP;
                    i += 4;
                }
                OPC_INVOKEINTERFACE => {
                    operands.push(input.read_unsigned_short()?);
                    operands.push(input.read_unsigned_byte()?);
                    input.discard(1)?;
                    group = GROUP_INVOCATION;
                    i += 4;
                }
                OPC_MULTIANEWARRAY => {
                    operands.push(input.read_unsigned_short()?);
                    operands.push(input.read_unsigned_byte()?);
                    i += 3;
                }
                OPC_TABLESWITCH => {
                    let padding = (4 - (i + 1) % 4) % 4;
                    input.discard(padding)?;
                    i += padding;
                    operands.push(input.read_int()?);
                    i += 4;
                    let low = input.read_int()?;
                    operands.push(low);
                    i += 4;
                    let high = input.read_int()?;
                    operands.push(high);
                    i += 4;

                    for _ in 0..high.wrapping_sub(low).wrapping_add(1) {
                        operands.push(input.read_int()?);
                        i += 4;
                    }
                    group = GROUP_SWITCH;
                }
                OPC_LOOKUPSWITCH => {
                    let padding = (4 - (i + 1) % 4) % 4;
                    input.discard(padding)?;
                    i += padding;
                    operands.push(input.read_int()?);
                    i += 4;
                    let npairs = input.read_int()?;
                    operands.push(npairs);
                    i += 4;

                    for _ in 0..npairs {
                        operands.push(input.read_int()?);
                        i += 4;
                        operands.push(input.read_int()?);
                        i += 4;
                    }
                    group = GROUP_SWITCH;
                }
                OPC_IRETURN | OPC_LRETURN | OPC_FRETURN | OPC_DRETURN | OPC_ARETURN
                | OPC_RETURN | OPC_ATHROW => {
                    group = GROUP_RETURN;
                }
                _ => {}
            }
        }

        i += 1;

        let instr = Instruction::create_with_operands(
            opcode,
            wide,
            group,
            bytecode_version,
            operands,
            offset,
            i - offset,
        );

        offset_to_index.insert(offset, instructions.len() as i32);
        instructions.push(instr);
    }

    // initialize exception table
    let exception_count = input.read_unsigned_short()?;
    let mut lst_handlers = Vec::with_capacity(exception_count as usize);
    for _ in 0..exception_count {
        let from = offset_to_index[&input.read_unsigned_short()?];
        // catch block can go to the end of the method
        let to = offset_to_index
            .get(&input.read_unsigned_short()?)
            .copied()
            .unwrap_or(instructions.len() as i32);
        let handler = offset_to_index[&input.read_unsigned_short()?];
        let exc_class = input.read_unsigned_short()?;
        let exception_class = (exc_class != 0).then(|| {
            pool.get_primitive_constant(exc_class)
                .unwrap()
                .get_string()
                .clone()
        });
        lst_handlers.push(ExceptionHandler {
            from,
            to,
            handler,
            exception_class,
        });
    }

    let mut seq = FullInstructionSequence {
        instructions: Vec::with_capacity(instructions.len()),
        offset_to_index,
        exception_table: ExceptionTable::new(lst_handlers),
    };

    // An instruction is shared, and so can no longer change, once it is in the
    // sequence; its targets depend on nothing but the offsets, which are complete.
    for mut instr in instructions {
        instr.init_instruction(&seq);
        seq.instructions.push(Arc::new(instr));
    }

    Ok(seq)
}
