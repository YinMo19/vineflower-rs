//! jlink stores the built-in loader assignments in a generated class. Read
//! only the operands used to construct the Set assigned to bootModules.

use super::{CLASS_SUFFIX, ContextSource, RuntimeModule};
use crate::code::{code_constants::*, instruction::Instruction};
use crate::engine::Options;
use crate::structs::{
    StructClass,
    consts::{ConstantPool, ConstantValue},
};
use crate::types::MethodDescriptor;
use crate::util::data_input::DataInputFullStream;
use rustc_hash::FxHashSet;
use std::sync::Arc;

pub(super) fn read(base: &RuntimeModule) -> Option<FxHashSet<String>> {
    let owner = "jdk/internal/module/ModuleLoaderMap$Modules";
    let bytes = base
        .get_input_stream(&format!("{owner}{CLASS_SUFFIX}"))
        .ok()??;
    let class = StructClass::create(
        &mut DataInputFullStream::new(&bytes),
        true,
        &Options::default(),
        None,
    )
    .ok()?;
    let init = class
        .get_method(CLINIT_NAME, "()V")?
        .expand_data(&class)
        .ok()??;
    let code = init.iter().as_slice();
    let store = code.iter().position(|op| {
        op.opcode == OPC_PUTSTATIC
            && class
                .pool
                .get_link_constant(op.operand(0))
                .is_some_and(|field| {
                    field.classname.as_deref() == Some(owner)
                        && field.elementname == "bootModules"
                        && field.descriptor == "Ljava/util/Set;"
                })
    })?;
    let (factory, args) = code[..store].split_last()?;
    if factory.opcode != OPC_INVOKESTATIC {
        return None;
    }
    let method = class.pool.get_link_constant(factory.operand(0))?;
    if method.classname.as_deref() != Some("java/util/Set") || method.elementname != "of" {
        return None;
    }
    let desc = MethodDescriptor::parse_descriptor(&method.descriptor);
    if desc.ret.value.as_deref() != Some("java/util/Set") {
        return None;
    }
    if let [param] = desc.params.as_slice()
        && param.array_dim == 1
        && param.value.as_deref() == Some("java/lang/Object")
    {
        string_array(&class.pool, args)
    } else {
        let start = args.len().checked_sub(desc.params.len())?;
        args[start..]
            .iter()
            .map(|op| string(&class.pool, op))
            .collect()
    }
}

fn string_array(pool: &ConstantPool, mut args: &[Arc<Instruction>]) -> Option<FxHashSet<String>> {
    let mut indices = FxHashSet::default();
    let mut names = FxHashSet::default();
    while args.last()?.opcode == OPC_AASTORE {
        let (rest, [dup, index, value, _]) = args.split_last_chunk::<4>()?;
        let index = integer(pool, index)?;
        if dup.opcode != OPC_DUP
            || index < 0
            || !indices.insert(index)
            || !names.insert(string(pool, value)?)
        {
            return None;
        }
        args = rest;
    }
    let (_, [size, array]) = args.split_last_chunk::<2>()?;
    if array.opcode != OPC_ANEWARRAY
        || pool.get_primitive_constant(array.operand(0))?.get_string() != "java/lang/String"
    {
        return None;
    }
    let size = integer(pool, size)?;
    (size >= 0 && size as usize == indices.len() && indices.iter().all(|&i| i < size))
        .then_some(names)
}

fn string(pool: &ConstantPool, op: &Instruction) -> Option<String> {
    if !matches!(op.opcode, OPC_LDC | OPC_LDC_W) {
        return None;
    }
    let value = pool.get_primitive_constant(op.operand(0))?;
    (value.ty == CONSTANT_STRING).then(|| value.get_string().to_string())
}

fn integer(pool: &ConstantPool, op: &Instruction) -> Option<i32> {
    match op.opcode {
        OPC_BIPUSH | OPC_SIPUSH => Some(op.operand(0)),
        OPC_LDC | OPC_LDC_W => match pool.get_primitive_constant(op.operand(0))?.value {
            ConstantValue::Integer(n) => Some(n),
            _ => None,
        },
        _ => None,
    }
}
