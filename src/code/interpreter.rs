// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.interpreter.InstructionImpact`: applies the local and stack effects
//! of a decoded instruction. Wide values normally occupy two slots, with a
//! `Group2empty` marker in the second slot.

use super::code_constants::*;
use super::instruction::Instruction;
use crate::structs::consts::{ConstantPool, PooledConstant};
use crate::types::data_point::DataPoint;
use crate::types::{CodeType, FieldDescriptor, MethodDescriptor, VarType};
use crate::util::list_stack::ListStack;

const PRIMITIVE_ARRAY_TYPES: [CodeType; 8] = [
    CodeType::Boolean,
    CodeType::Char,
    CodeType::Float,
    CodeType::Double,
    CodeType::Byte,
    CodeType::Short,
    CodeType::Int,
    CodeType::Long,
];

pub fn step_types(data: &mut DataPoint, instr: &Instruction, pool: &ConstantPool) {
    let stack = data.stack_mut();
    let (pop_slots, push) = match instr.opcode {
        OPC_NOP | OPC_IINC | OPC_GOTO | OPC_GOTO_W | OPC_RET | OPC_RETURN => return,

        // The decoder expands these forms before the interpreter sees them.
        OPC_ICONST_M1..=OPC_ICONST_5
        | OPC_ILOAD_0..=OPC_ALOAD_3
        | OPC_ISTORE_0..=OPC_ASTORE_3
        | OPC_WIDE => return,

        OPC_BIPUSH | OPC_SIPUSH | OPC_ILOAD => (0, CodeType::Int),
        OPC_LCONST_0 | OPC_LCONST_1 | OPC_LLOAD => (0, CodeType::Long),
        OPC_FCONST_0..=OPC_FCONST_2 | OPC_FLOAD => (0, CodeType::Float),
        OPC_DCONST_0 | OPC_DCONST_1 | OPC_DLOAD => (0, CodeType::Double),
        OPC_ACONST_NULL => (0, CodeType::Null),
        OPC_JSR | OPC_JSR_W => (0, CodeType::Address),

        OPC_IALOAD | OPC_BALOAD | OPC_CALOAD | OPC_SALOAD => (2, CodeType::Int),
        OPC_LALOAD => (2, CodeType::Long),
        OPC_FALOAD => (2, CodeType::Float),
        OPC_DALOAD => (2, CodeType::Double),
        OPC_ARRAYLENGTH => (1, CodeType::Int),

        // Only astore updates the types of local variables upstream.
        OPC_ISTORE | OPC_FSTORE | OPC_POP => (1, CodeType::Void),
        OPC_LSTORE | OPC_DSTORE | OPC_POP2 => (2, CodeType::Void),
        OPC_IASTORE | OPC_FASTORE | OPC_AASTORE | OPC_BASTORE | OPC_CASTORE | OPC_SASTORE => {
            (3, CodeType::Void)
        }
        OPC_LASTORE | OPC_DASTORE => (4, CodeType::Void),

        OPC_IADD | OPC_ISUB | OPC_IMUL | OPC_IDIV | OPC_IREM | OPC_ISHL | OPC_ISHR | OPC_IUSHR
        | OPC_IAND | OPC_IOR | OPC_IXOR => (2, CodeType::Int),
        OPC_LADD | OPC_LSUB | OPC_LMUL | OPC_LDIV | OPC_LREM | OPC_LAND | OPC_LOR | OPC_LXOR => {
            (4, CodeType::Long)
        }
        OPC_LSHL | OPC_LSHR | OPC_LUSHR => (3, CodeType::Long),
        OPC_FADD | OPC_FSUB | OPC_FMUL | OPC_FDIV | OPC_FREM => (2, CodeType::Float),
        OPC_DADD | OPC_DSUB | OPC_DMUL | OPC_DDIV | OPC_DREM => (4, CodeType::Double),

        OPC_INEG | OPC_I2B | OPC_I2C | OPC_I2S => (1, CodeType::Int),
        OPC_LNEG => (2, CodeType::Long),
        OPC_FNEG => (1, CodeType::Float),
        OPC_DNEG => (2, CodeType::Double),
        OPC_I2L | OPC_F2L => (1, CodeType::Long),
        OPC_I2F => (1, CodeType::Float),
        OPC_I2D | OPC_F2D => (1, CodeType::Double),
        OPC_L2I | OPC_D2I => (2, CodeType::Int),
        OPC_L2F | OPC_D2F => (2, CodeType::Float),
        OPC_L2D => (2, CodeType::Double),
        OPC_F2I => (1, CodeType::Int),
        OPC_D2L => (2, CodeType::Long),
        OPC_LCMP | OPC_DCMPL | OPC_DCMPG => (4, CodeType::Int),
        OPC_FCMPL | OPC_FCMPG => (2, CodeType::Int),

        OPC_IFEQ..=OPC_IFLE
        | OPC_IFNULL
        | OPC_IFNONNULL
        | OPC_TABLESWITCH
        | OPC_LOOKUPSWITCH
        | OPC_IRETURN
        | OPC_FRETURN
        | OPC_ARETURN
        | OPC_MONITORENTER
        | OPC_MONITOREXIT => (1, CodeType::Void),
        OPC_IF_ICMPEQ..=OPC_IF_ACMPNE | OPC_LRETURN | OPC_DRETURN => (2, CodeType::Void),

        _ => {
            step_special_types(data, instr, pool);
            return;
        }
    };

    stack.remove_multiple(pop_slots);
    if push != CodeType::Void {
        push_value(stack, VarType::new(push));
    }
}

fn step_special_types(data: &mut DataPoint, instr: &Instruction, pool: &ConstantPool) {
    let stack = data.stack_mut();
    match instr.opcode {
        OPC_LDC | OPC_LDC_W | OPC_LDC2_W => push_constant_type(stack, pool, instr.operand(0)),
        OPC_ALOAD => {
            let variable = data.get_variable(instr.operand(0) as usize);
            data.stack_mut().push(variable);
        }
        OPC_AALOAD => {
            let array = stack.pop_count(2).unwrap();
            let mut element = VarType::with_dim(array.ty, array.array_dim - 1);
            element.value = array.value;
            stack.push(element);
        }
        OPC_ASTORE => {
            let value = stack.pop().unwrap();
            data.set_variable(instr.operand(0) as usize, value);
        }
        OPC_DUP..=OPC_DUP_X2 => {
            let offset = -1 - (instr.opcode - OPC_DUP);
            stack.insert_by_offset(offset, stack.get_by_offset(-1).clone());
        }
        OPC_DUP2..=OPC_DUP2_X2 => {
            let offset = -2 - (instr.opcode - OPC_DUP2);
            stack.insert_by_offset(offset, stack.get_by_offset(-2).clone());
            stack.insert_by_offset(offset, stack.get_by_offset(-1).clone());
        }
        OPC_SWAP => {
            let value = stack.pop().unwrap();
            stack.insert_by_offset(-1, value);
        }
        OPC_GETSTATIC | OPC_GETFIELD | OPC_PUTSTATIC | OPC_PUTFIELD => {
            let field = pool.get_link_constant(instr.operand(0)).unwrap();
            let ty = VarType::from_signature(&field.descriptor);
            let receiver = i32::from(matches!(instr.opcode, OPC_GETFIELD | OPC_PUTFIELD));
            if matches!(instr.opcode, OPC_GETSTATIC | OPC_GETFIELD) {
                stack.remove_multiple(receiver);
                push_value(stack, ty);
            } else {
                stack.remove_multiple(receiver + ty.stack_size);
            }
        }
        OPC_INVOKEDYNAMIC if !instr.bytecode_version.has_invoke_dynamic() => {}
        OPC_INVOKEVIRTUAL..=OPC_INVOKEDYNAMIC => {
            let method = pool.get_link_constant(instr.operand(0)).unwrap();
            let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
            let receiver = i32::from(!matches!(
                instr.opcode,
                OPC_INVOKESTATIC | OPC_INVOKEDYNAMIC
            ));
            let arguments: i32 = descriptor.params.iter().map(|param| param.stack_size).sum();
            stack.remove_multiple(receiver + arguments);
            if descriptor.ret.ty != CodeType::Void {
                push_value(stack, descriptor.ret);
            }
        }
        OPC_NEW | OPC_CHECKCAST | OPC_INSTANCEOF => {
            if instr.opcode != OPC_NEW {
                stack.pop().unwrap();
            }
            let class = pool.get_primitive_constant(instr.operand(0)).unwrap();
            // Upstream uses the tested class as the result of instanceof as well as checkcast.
            stack.push(VarType::with_value(
                CodeType::Object,
                0,
                class.get_string().clone(),
            ));
        }
        OPC_NEWARRAY => {
            stack.pop().unwrap();
            let element_type = PRIMITIVE_ARRAY_TYPES[(instr.operand(0) - 4) as usize];
            stack.push(VarType::with_dim(element_type, 1));
        }
        OPC_ATHROW => {
            let thrown = stack.pop().unwrap();
            stack.clear();
            stack.push(thrown);
        }
        OPC_ANEWARRAY | OPC_MULTIANEWARRAY => {
            let dimensions = if instr.opcode == OPC_ANEWARRAY {
                1
            } else {
                instr.operand(1)
            };
            stack.remove_multiple(dimensions);
            let class = pool.get_primitive_constant(instr.operand(0)).unwrap();
            // Keep an array class descriptor in the name. Upstream uses the instruction's
            // dimension count for array_dim.
            stack.push(VarType::with_value(
                CodeType::Object,
                dimensions,
                class.get_string().clone(),
            ));
        }
        opcode => panic!("Unhandled opcode: {opcode}"),
    }
}

fn push_constant_type(stack: &mut Vec<VarType>, pool: &ConstantPool, index: i32) {
    let ty = match pool.get_constant(index).unwrap() {
        PooledConstant::Primitive(constant) => match constant.ty {
            CONSTANT_INTEGER => VarType::VARTYPE_INT,
            CONSTANT_FLOAT => VarType::VARTYPE_FLOAT,
            CONSTANT_LONG => VarType::VARTYPE_LONG,
            CONSTANT_DOUBLE => VarType::VARTYPE_DOUBLE,
            CONSTANT_STRING => VarType::VARTYPE_STRING,
            CONSTANT_CLASS => VarType::VARTYPE_CLASS,
            CONSTANT_METHODTYPE => VarType::VARTYPE_METHODTYPE,
            ty => panic!("Unhandled constant type: {ty}"),
        },
        PooledConstant::Link(constant) => match constant.ty {
            // Upstream pushes the referenced member's descriptor as a single slot.
            CONSTANT_METHODHANDLE => {
                stack.push(VarType::from_signature(&constant.descriptor));
                return;
            }
            CONSTANT_DYNAMIC => {
                let field = FieldDescriptor::parse_descriptor(&constant.descriptor);
                if field.ty.ty == CodeType::Void {
                    return;
                }
                field.ty
            }
            ty => panic!("Unhandled constant type: {ty}"),
        },
    };
    push_value(stack, ty);
}

fn push_value(stack: &mut Vec<VarType>, ty: VarType) {
    let wide = ty.stack_size == 2;
    stack.push(ty);
    if wide {
        stack.push(VarType::new(CodeType::Group2empty));
    }
}
