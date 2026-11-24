// Based on Vineflower's AssertProcessor (Apache-2.0).
// Copyright 2000-2020 JetBrains s.r.o.

use std::collections::BTreeMap;

use crate::{
    ClassGroup,
    bytecode::{Instruction, Operand, decode},
    cfg::ControlFlowGraph,
    classfile::{ClassFile, Constant, ConstantPool},
    context::NestedKind,
};

use super::{Guard, SYNTHETIC, canonical_guard_field};

const STATIC: u16 = 0x0008;
const INTERFACE: u16 = 0x0200;

/// Javac places interface guards in an anonymous, non-instantiable class
/// underneath the top-level type. The interface eagerly initializes this
/// holder, even when its own static fields do not depend on assertions.
pub(crate) fn interface_guards<'g>(
    group: &'g ClassGroup<'_>,
    root: &str,
) -> BTreeMap<&'g str, Guard<'g>> {
    let mut holders = group.children(root).filter_map(|(name, node)| {
        if !matches!(node.kind, NestedKind::Anonymous)
            || node.method.is_some()
            || node.access_flags & !SYNTHETIC != STATIC
        {
            return None;
        }
        let suffix = name.strip_prefix(root)?.strip_prefix('$')?;
        if suffix.is_empty() || !suffix.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        prove_holder(group.get(name)?, root)
    });
    let Some(holder) = holders.next() else {
        return BTreeMap::new();
    };
    if holders.next().is_some() {
        return BTreeMap::new();
    }
    prove_consumers(group, root, holder).unwrap_or_default()
}

fn prove_holder<'c>(class: &'c ClassFile<'_>, root: &str) -> Option<Guard<'c>> {
    let pool = &class.pool;
    if class.access_flags != (SYNTHETIC | 0x0020)
        || pool.class_name(class.super_class).ok()? != "java/lang/Object"
        || !class.interfaces.is_empty()
    {
        return None;
    }
    let [field] = &class.fields[..] else {
        return None;
    };
    let [method] = &class.methods[..] else {
        return None;
    };
    if !canonical_guard_field(class, field)
        || field.access_flags & 0x0007 != 0
        || method.access_flags != STATIC
        || pool.utf8(method.name_index).ok()? != "<clinit>"
        || pool.utf8(method.descriptor_index).ok()? != "()V"
    {
        return None;
    }
    let guard = Guard {
        owner: pool.class_name(class.this_class).ok()?,
        field: pool.utf8(field.name_index).ok()?,
        initializer: 0,
        declares_field: false,
        methods: BTreeMap::new(),
    };
    let code = method.code(pool).ok()??;
    let instructions = decode(code.bytes).ok()?;
    if code.max_locals != 0
        || !code.exceptions.is_empty()
        || instructions.len() != 8
        || instructions[7].opcode != 0xb1
    {
        return None;
    }
    let graph = ControlFlowGraph::build(&instructions, &[]).ok()?;
    guard.prove_initializer(pool, root, &instructions, &graph)?;
    Some(guard)
}

fn prove_consumers<'g>(
    group: &'g ClassGroup<'_>,
    root: &str,
    holder: Guard<'g>,
) -> Option<BTreeMap<&'g str, Guard<'g>>> {
    let mut consumers = BTreeMap::new();
    let descriptor = format!("L{};", holder.owner);
    for (owner, class) in group.classes() {
        if owner == holder.owner {
            continue;
        }
        let pool = &class.pool;
        let names_holder = |index| pool.class_name(index).ok() == Some(holder.owner);
        let class_constant =
            |index| matches!(pool.get(index), Ok(Constant::Class(_))) && names_holder(index);
        let mut field_reference = false;
        let mut has_holder_class = false;
        for constant in pool.iter() {
            match constant {
                Constant::Class(name) if pool.utf8(*name).ok() == Some(holder.owner) => {
                    has_holder_class = true
                }
                Constant::Fieldref {
                    class_index,
                    name_and_type_index,
                } if names_holder(*class_index) => {
                    if pool.name_and_type(*name_and_type_index).ok()? != (holder.field, "Z") {
                        return None;
                    }
                    field_reference = true;
                }
                Constant::Methodref { class_index, .. }
                | Constant::InterfaceMethodref { class_index, .. }
                    if names_holder(*class_index) =>
                {
                    return None;
                }
                Constant::MethodHandle {
                    reference_index, ..
                } if holder.is_field_ref(pool, *reference_index) => return None,
                Constant::Utf8(text)
                    if text.as_str().is_some_and(|text| text.contains(&descriptor)) =>
                {
                    return None;
                }
                _ => {}
            }
        }
        if !has_holder_class {
            continue;
        }
        // An InnerClasses or nest-mate entry can name the holder, but no
        // executable type use may require this class independently of assert.
        if names_holder(class.super_class)
            || class.interfaces.iter().any(|&index| names_holder(index))
            || class
                .bootstrap_methods()
                .ok()?
                .iter()
                .any(|method| method.arguments.iter().copied().any(class_constant))
        {
            return None;
        }
        let mut guard = Guard {
            owner: holder.owner,
            field: holder.field,
            initializer: 0,
            declares_field: false,
            methods: BTreeMap::new(),
        };
        for method in &class.methods {
            if method
                .exceptions(pool)
                .ok()?
                .iter()
                .copied()
                .any(names_holder)
            {
                return None;
            }
            let Some(code) = method.code(pool).ok()? else {
                continue;
            };
            let instructions = decode(code.bytes).ok()?;
            if code
                .exceptions
                .iter()
                .any(|handler| names_holder(handler.catch_type))
                || instructions.iter().any(
                    |op| matches!(op.operand, Operand::Constant(index) if class_constant(index)),
                )
            {
                return None;
            }
            if !field_reference {
                continue;
            }
            let name = pool.utf8(method.name_index).ok()?;
            let desc = pool.utf8(method.descriptor_index).ok()?;
            if name == "<clinit>" {
                if desc != "()V" || guard.initializer != 0 || method.access_flags & STATIC == 0 {
                    return None;
                }
                let graph = ControlFlowGraph::build(&instructions, &code.exceptions).ok()?;
                let load = prove_trigger(&guard, pool, &instructions, &graph)?;
                if guard.count_uses(pool, &instructions, Some(load)) != 0 {
                    return None;
                }
                guard.initializer = 2;
            } else {
                let uses = guard.count_uses(pool, &instructions, None);
                if uses != 0 {
                    let graph = ControlFlowGraph::build(&instructions, &code.exceptions).ok()?;
                    guard.record_method(pool, method, &code, &instructions, &graph, uses)?;
                }
            }
        }
        if field_reference {
            if class.access_flags & INTERFACE == 0
                || group.compilation_root(owner) != root
                || guard.initializer == 0
                || guard.methods.is_empty()
            {
                return None;
            }
            consumers.insert(owner, guard);
        }
    }
    Some(consumers)
}

fn prove_trigger(
    guard: &Guard<'_>,
    pool: &ConstantPool<'_>,
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
) -> Option<u32> {
    let [load, test, next, ..] = instructions else {
        return None;
    };
    let entry = graph.blocks.first()?;
    // Both sides of ifeq go directly to the same instruction. The only
    // effect of the pair is initializing the proven assertion holder.
    if load.opcode != 0xb2
        || !matches!(load.operand, Operand::Constant(index) if guard.is_field_ref(pool, index))
        || test.opcode != 0x99
        || test.operand != Operand::Branch(next.offset)
        || entry.instructions != (0..2)
        || entry.successors.as_slice() != [1]
        || !entry.predecessors.is_empty()
        || !entry.exception_successors.is_empty()
        || !entry.exception_predecessors.is_empty()
    {
        return None;
    }
    Some(load.offset)
}
