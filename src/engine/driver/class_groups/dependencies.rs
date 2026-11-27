use rustc_hash::FxHashMap;

use super::super::PendingClass;
use crate::code::code_constants::{
    ACC_FINAL, ACC_STATIC, ACC_SYNTHETIC, CONSTANT_CLASS, CONSTANT_DYNAMIC, CONSTANT_FIELDREF,
    CONSTANT_INTERFACEMETHODREF, CONSTANT_METHODREF, CONSTANT_UTF8, INIT_NAME,
};
use crate::decompiler::exps::expr_util::is_static_member;
use crate::engine::class_nodes::{ClassKind, ClassNode, ClassNodes};
use crate::structs::consts::PooledConstant;

/// Group roots that need another root's nested-class state or enum map.
/// The caller handles components in separate sessions. References to such
/// state outside this input unit must use the shared session instead.
pub(super) fn connected_roots(
    nodes: &ClassNodes,
    roots: &[PendingClass],
    expand_dynamic_constants: bool,
) -> Option<Vec<Vec<usize>>> {
    let mut owners = FxHashMap::default();
    for (index, root) in roots.iter().enumerate() {
        let mut pending = vec![root.node];
        while let Some(id) = pending.pop() {
            if owners.insert(id, index).is_some() {
                return None;
            }
            pending.extend(&nodes[id].nested);
        }
    }

    let mut groups = Components::new(roots.len());
    for (&id, &owner) in &owners {
        let node = &nodes[id];
        if node.class.qualified_name.contains("##Lambda_") {
            return None;
        }
        let mut connect = |name: &str| -> Option<()> {
            if let Some(target) = nodes.id(name) {
                groups.join(owner, *owners.get(&target)?);
            }
            Some(())
        };
        if node.kind != ClassKind::Root {
            for enclosing in node.enclosing_classes.iter() {
                connect(enclosing)?;
            }
        }
        let pool = &node.class.pool;
        for (index, constant) in pool.get_pool().iter().enumerate() {
            match constant {
                // Expanding a bootstrap can load annotated library classes in a
                // method's import scope. Keep that first load and its diagnostics
                // in the same root order as shared method preparation.
                Some(PooledConstant::Link(link))
                    if expand_dynamic_constants && link.ty == CONSTANT_DYNAMIC =>
                {
                    return None;
                }
                // Ordinary bytecode obtains synthesized lambda names from its
                // bootstrap call sites. A literal reference can observe another
                // root replacing a real class or a previous miss at publication.
                Some(PooledConstant::Primitive(value))
                    if value.ty == CONSTANT_UTF8 && value.get_string().contains("##Lambda_") =>
                {
                    return None;
                }
                Some(PooledConstant::Primitive(value)) if value.ty == CONSTANT_CLASS => {
                    let name = pool
                        .get_primitive_constant(index as i32)?
                        .get_string()
                        .clone();
                    if nodes.get(&name).is_some_and(|target| {
                        matches!(target.kind, ClassKind::Anonymous | ClassKind::Local)
                            || target.simple_name.is_none()
                    }) {
                        connect(&name)?;
                    }
                }
                Some(PooledConstant::Link(link))
                    if matches!(
                        link.ty,
                        CONSTANT_FIELDREF | CONSTANT_METHODREF | CONSTANT_INTERFACEMETHODREF
                    ) =>
                {
                    // The same lookup as bytecode decoding applies any member
                    // and class renaming before resolving the target node.
                    let reference = pool.get_link_constant(index as i32)?;
                    let name = reference.classname.as_deref()?;
                    let Some(target) = nodes.get(name) else {
                        continue;
                    };
                    let member = reference.elementname.as_str();
                    let descriptor = reference.descriptor.as_str();
                    let dependent = if reference.ty == CONSTANT_FIELDREF {
                        switch_map_field(target, member, descriptor)
                    } else if member == INIT_NAME {
                        // A declared static member constructor has no enclosing
                        // instance or capture mask, with or without its wrapper.
                        let needs_captures = match target.kind {
                            ClassKind::Root => false,
                            ClassKind::Member => {
                                target.access & ACC_STATIC == 0 || !is_static_member(&target.class)
                            }
                            _ => true,
                        };
                        needs_captures || target.class.get_method(member, descriptor).is_none()
                    } else {
                        member.starts_with("$SWITCH_TABLE$")
                    };
                    if dependent {
                        connect(name)?;
                    }
                }
                _ => {}
            }
        }
    }
    Some(groups.into_ordered_groups())
}

fn switch_map_field(target: &ClassNode, name: &str, descriptor: &str) -> bool {
    if descriptor != "[I" {
        return false;
    }
    // SwitchHelper checks all three flags on fields of a synthetic holder.
    // A missing declaration also depends on whether its own node is visible.
    const REQUIRED: i32 = ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC;
    target
        .class
        .get_field(name, descriptor)
        .is_none_or(|field| {
            target.class.access_flags & ACC_SYNTHETIC != 0
                && field.access_flags & REQUIRED == REQUIRED
        })
}

struct Components {
    parent: Vec<usize>,
}

impl Components {
    fn new(count: usize) -> Self {
        Self {
            parent: (0..count).collect(),
        }
    }

    fn root(&mut self, mut index: usize) -> usize {
        while self.parent[index] != index {
            self.parent[index] = self.parent[self.parent[index]];
            index = self.parent[index];
        }
        index
    }

    fn join(&mut self, left: usize, right: usize) {
        let left = self.root(left);
        let right = self.root(right);
        self.parent[right] = left;
    }

    fn into_ordered_groups(mut self) -> Vec<Vec<usize>> {
        let mut groups: Vec<Vec<usize>> = Vec::new();
        let mut positions = FxHashMap::default();
        for index in 0..self.parent.len() {
            let id = self.root(index);
            let slot = positions.entry(id).or_insert_with(|| {
                groups.push(Vec::new());
                groups.len() - 1
            });
            groups[*slot].push(index);
        }
        groups
    }
}
