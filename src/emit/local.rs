// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::Peekable,
    rc::Rc,
};

use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::{BootstrapMethod, ClassError, ClassFile, Code, Constant, LocalVariable},
    context::{NestedClass, NestedKind},
    lift::{AnonymousBindings, AnonymousSites},
    structure::Line,
};

use super::{DecompileError, STATIC, SYNTHETIC, Writer};

impl<'a, 'c> Writer<'a, 'c> {
    pub(in crate::emit) fn local_declarations(
        &self,
        name: &str,
        descriptor: &str,
        code: &Code<'a>,
        lines: &[Line],
        sites: Option<&AnonymousSites>,
    ) -> Result<Vec<LocalDeclaration<'c>>, DecompileError> {
        if !self.options.decompile_inner {
            return Ok(Vec::new());
        }
        let group = self.group;
        let mut declarations: BTreeMap<_, _> = group
            .children(self.owner)
            .filter_map(|(child, node)| {
                let NestedKind::Local(simple) = &node.kind else {
                    return None;
                };
                let (method, signature) = node.method.as_ref()?;
                (method == name && signature == descriptor).then_some((
                    child,
                    LocalDeclaration {
                        child,
                        node,
                        simple,
                        uses: None,
                        references: None,
                        insertion: 0,
                        scope_end: None,
                        captures: BTreeSet::new(),
                        bindings: None,
                    },
                ))
            })
            .collect();
        if declarations.is_empty() {
            return Ok(Vec::new());
        }
        let sites = sites.map(|sites| sites.borrow());
        let pool = &self.class.pool;
        for declaration in declarations.values_mut() {
            let child = declaration.child;
            let mut observed = sites.iter().flat_map(|sites| sites.local_sites(child));
            if let Some(first) = observed.next() {
                if observed.any(|candidate| !first.same_bindings(candidate)) {
                    return Err(DecompileError::Unsupported {
                        feature: "different capture bindings at local-class constructions",
                    });
                }
                declaration.bindings = Some(first.bindings(self.anonymous_bindings.clone()));
                continue;
            }
            let class = group
                .get(declaration.child)
                .expect("local class is registered");
            for field in &class.fields {
                let name = class.pool.utf8(field.name_index)?;
                let descriptor = class.pool.utf8(field.descriptor_index)?;
                if field.access_flags & (STATIC | 0x0010) == 0x0010
                    && (field.access_flags & SYNTHETIC != 0
                        || crate::classfile::find_attribute(
                            &field.attributes,
                            &class.pool,
                            "Synthetic",
                        )?
                        .is_some())
                    && group
                        .outer_field(declaration.child, name, descriptor)
                        .is_none()
                {
                    return Err(DecompileError::Unsupported {
                        feature: "captured local class without a recoverable construction site",
                    });
                }
            }
            declaration.bindings = sites
                .as_ref()
                .and_then(|sites| sites.uncaptured_local_bindings(child, self.anonymous_bindings.clone()));
        }
        let method_error = |source| DecompileError::Method {
            name: name.into(),
            descriptor: descriptor.into(),
            source: Box::new(source),
        };
        let instructions = bytecode::decode(code.bytes).map_err(method_error)?;
        let locations: BTreeMap<_, _> = lines
            .iter()
            .enumerate()
            .flat_map(|(index, line)| {
                line.offsets
                    .iter()
                    .copied()
                    .map(move |offset| (offset, index))
            })
            .collect();
        for declaration in declarations
            .values_mut()
            .filter(|declaration| declaration.bindings.is_some())
        {
            let registry = sites
                .as_ref()
                .expect("binding was recovered from site registry");
            for site in registry.local_sites(declaration.child) {
                if let Some(&line) = locations.get(&site.offset()) {
                    declaration.add_use(line);
                }
                for capture in site.declarations() {
                    let Some(&line) = locations.get(&capture) else {
                        return Err(DecompileError::Unsupported {
                            feature: "cannot locate captured variable in the enclosing source",
                        });
                    };
                    declaration.captures.insert(line);
                }
            }
        }
        let mut bootstraps = None;
        for op in &instructions {
            let line = locations.get(&op.offset).copied();
            if let Some(class) = referenced_class(self.class, op)?
                && let Some(declaration) = declarations.get_mut(class)
            {
                let (first, _) = declaration.references.unwrap_or((op.offset, op.offset));
                declaration.references = Some((first, op.offset));
                if let Some(line) = line {
                    declaration.add_use(line);
                }
            }
            let Some(line) = line.filter(|_| op.opcode == 0xba) else {
                continue;
            };
            let bootstraps = match &mut bootstraps {
                Some(bootstraps) => bootstraps,
                place @ None => place.insert(self.class.bootstrap_methods()?),
            };
            for (name, descriptor) in lambda_targets(self.class, bootstraps, op)? {
                for method in &self.class.methods {
                    if pool.utf8(method.name_index)? != name
                        || pool.utf8(method.descriptor_index)? != descriptor
                    {
                        continue;
                    }
                    let Some(code) = method.code(pool)? else {
                        break;
                    };
                    for op in bytecode::decode(code.bytes).map_err(method_error)? {
                        if let Some(class) = referenced_class(self.class, &op)?
                            && let Some(declaration) = declarations.get_mut(class)
                        {
                            if self
                                .dynamic_helpers
                                .borrow()
                                .contains(&(method.name_index, method.descriptor_index))
                            {
                                return Err(DecompileError::Unsupported {
                                    feature: "local class escaping to a synthetic lambda helper",
                                });
                            }
                            declaration.add_use(line);
                        }
                    }
                    break;
                }
            }
        }
        let locals = code.local_variables(pool)?;
        for local in &locals {
            let Some(class) = array_or_object_class(local.descriptor) else {
                continue;
            };
            let Some(declaration) = declarations.get_mut(class) else {
                continue;
            };
            // A local-variable scope normally begins after its first store.
            let line = locations
                .range(..u32::from(local.start_pc))
                .next_back()
                .map_or(0, |(_, &line)| line);
            declaration.add_use(line);
        }
        let dependencies = self.local_dependencies(&declarations)?;
        let mut order = Vec::with_capacity(declarations.len());
        while !declarations.is_empty() {
            let Some((&next, _)) = declarations.iter().find(|(candidate, _)| {
                !dependencies
                    .iter()
                    .any(|(user, deps)| declarations.contains_key(user) && deps.contains(candidate))
            }) else {
                return Err(DecompileError::Unsupported {
                    feature: "cyclic local class declarations",
                });
            };
            let mut declaration = declarations
                .remove(next)
                .expect("sorted declaration exists");
            declaration.place(lines, name == "<init>");
            if !declaration.captures_are_in_scope(lines) {
                return Err(DecompileError::Unsupported {
                    feature: "local-class declaration is outside its capture scope",
                });
            }
            for dependency in &dependencies[next] {
                declarations
                    .get_mut(dependency)
                    .expect("dependency follows its user")
                    .add_use(declaration.insertion);
            }
            order.push(declaration);
        }
        order.reverse();
        order.sort_by_key(|declaration| declaration.insertion);
        if code.exceptions.is_empty() {
            for index in 0..order.len() {
                order[index].scope_end =
                    isolated_scope(index, &order, lines, &instructions, &locations, &locals);
            }
        }
        Ok(order)
    }

    fn local_dependencies<'d>(
        &self,
        declarations: &BTreeMap<&'d str, LocalDeclaration<'_>>,
    ) -> Result<BTreeMap<&'d str, Vec<&'d str>>, ClassError> {
        declarations
            .keys()
            .map(|&child| {
                let class = self.group.get(child).expect("local class is registered");
                let mut required = Vec::new();
                for constant in class.pool.iter() {
                    let Constant::Class(name) = *constant else {
                        continue;
                    };
                    let name = class.pool.utf8(name)?;
                    let name = array_or_object_class(name).unwrap_or(name);
                    if name != child
                        && let Some((&dependency, _)) = declarations.get_key_value(name)
                        && !required.contains(&dependency)
                    {
                        required.push(dependency);
                    }
                }
                Ok((child, required))
            })
            .collect()
    }

    pub(in crate::emit) fn write_local_declarations(
        &mut self,
        index: usize,
        depth: usize,
        declarations: &mut Peekable<impl Iterator<Item = LocalDeclaration<'c>>>,
    ) -> Result<(), DecompileError> {
        let mut any = false;
        while declarations
            .peek()
            .is_some_and(|declaration| declaration.insertion == index)
        {
            let declaration = declarations.next().expect("peeked declaration");
            let after_open = self.body.ends_with(" {\n")
                || self
                    .body
                    .rsplit_terminator('\n')
                    .next()
                    .is_some_and(|line| {
                        let line = line.trim_start();
                        (line.starts_with("case ") || line.starts_with("default:"))
                            && line.ends_with(':')
                    });
            if (index != 0 || any) && !after_open && !self.body.ends_with("\n\n") {
                self.line(0, "");
            }
            let previous = declaration
                .bindings
                .as_ref()
                .map(|bindings| self.anonymous_bindings.replace(Rc::clone(bindings)));
            let result = self.write_nested(
                declaration.child,
                declaration.node,
                declaration.simple,
                self.depth + depth + 2,
            );
            if let Some(previous) = previous {
                self.anonymous_bindings = previous;
            }
            result?;
            any = true;
        }
        // Like Java's ExprProcessor.listToJava, add an expression separator
        // after the class's own newline, even at the end of a method.
        if any {
            self.line(0, "");
        }
        Ok(())
    }
}

pub(in crate::emit) struct LocalDeclaration<'a> {
    child: &'a str,
    node: &'a NestedClass,
    simple: &'a str,
    uses: Option<(usize, usize)>,
    references: Option<(u32, u32)>,
    insertion: usize,
    scope_end: Option<usize>,
    captures: BTreeSet<usize>,
    bindings: Option<AnonymousBindings>,
}

impl LocalDeclaration<'_> {
    pub(in crate::emit) fn scope_at(&self, index: usize) -> Option<usize> {
        self.scope_end.filter(|_| self.insertion == index)
    }

    fn add_use(&mut self, index: usize) {
        self.uses = Some(self.uses.map_or((index, index), |(first, last)| {
            (first.min(index), last.max(index))
        }));
    }

    fn captures_are_in_scope(&self, lines: &[Line]) -> bool {
        let insertion_depth = lines.get(self.insertion).map_or(0, |line| line.depth);
        self.captures.iter().all(|&capture| {
            if capture >= self.insertion {
                return false;
            }
            let depth = lines[capture].depth;
            depth <= insertion_depth
                && lines[capture + 1..self.insertion]
                    .iter()
                    .all(|line| line.depth >= depth)
        })
    }

    fn place(&mut self, lines: &[Line], constructor: bool) {
        let (first, last) = self.uses.unwrap_or((0, 0));
        if first >= lines.len() {
            self.insertion = lines.len();
            return;
        }
        let depth = if last >= lines.len() {
            0
        } else {
            lines[first..=last]
                .iter()
                .map(|line| line.depth)
                .min()
                .expect("has uses")
        };
        let mut insertion = first;
        while insertion > 0
            && (lines[insertion].depth > depth
                || lines[insertion].text.starts_with('}')
                || lines[insertion].text.starts_with("case ")
                || lines[insertion].text.starts_with("default:"))
        {
            insertion -= 1;
        }
        if insertion == 0
            && constructor
            && (lines[0].text.starts_with("this(") || lines[0].text.starts_with("super("))
        {
            insertion = 1;
        }
        self.insertion = insertion;
    }
}

/// Recover a lost block only for a straight-line run with a fresh, dead binding.
/// Other scopes already present in the structured lines keep their ownership.
fn isolated_scope(
    index: usize,
    declarations: &[LocalDeclaration<'_>],
    lines: &[Line],
    instructions: &[Instruction],
    locations: &BTreeMap<u32, usize>,
    locals: &[LocalVariable<'_>],
) -> Option<usize> {
    let declaration = &declarations[index];
    let (_, last) = declaration.uses?;
    let start = declaration.insertion;
    let depth = lines.get(start)?.depth;
    let end = last + 1;
    let body = lines.get(start..end)?;
    if body.is_empty()
        || body
            .iter()
            .any(|line| line.depth != depth || line.offsets.is_empty())
        || !declarations[index + 1..].iter().any(|later| {
            later.simple == declaration.simple
                && lines
                    .get(start..later.insertion)
                    .is_some_and(|between| between.iter().all(|line| line.depth >= depth))
                && lines.get(later.insertion).map_or(0, |line| line.depth) >= depth
        })
        || declarations.iter().enumerate().any(|(other, sibling)| {
            other != index
                && ((start..end).contains(&sibling.insertion)
                    || sibling.captures.range(start..end).next().is_some())
        })
    {
        return None;
    }

    let first_mapped = body.iter().flat_map(|line| &line.offsets).min().copied()?;
    let last_mapped = body.iter().flat_map(|line| &line.offsets).max().copied()?;
    let (first_ref, last_ref) = declaration.references?;
    // Allocation and constructor instructions can be unanchored.
    let first_offset = first_mapped.min(first_ref);
    let cut = last_mapped.checked_add(1)?;
    let enter = instructions
        .binary_search_by_key(&first_offset, |op| op.offset)
        .ok()?;
    let exit = instructions
        .binary_search_by_key(&cut, |op| op.offset)
        .ok()?;
    if last_ref >= cut
        || (first_ref < first_mapped && instructions[enter].opcode != 0xbb)
        || locations
            .range(first_offset..cut)
            .any(|(_, line)| !(start..end).contains(line))
        || instructions.iter().any(|op| {
            let inside = |target| (first_offset + 1..cut).contains(&target);
            match &op.operand {
                Operand::Branch(target) => inside(*target),
                Operand::Switch { default, cases } => {
                    inside(*default) || cases.iter().any(|&(_, target)| inside(target))
                }
                _ => op.opcode == 0xa9,
            }
        })
    {
        return None;
    }

    let mut binding = None;
    for op in &instructions[enter..exit] {
        if transfers_control(op) {
            return None;
        }
        // Do not absorb an earlier unmapped construction statement into this binding.
        if binding.is_none()
            && first_ref < first_mapped
            && op.offset != first_ref
            && matches!(op.opcode, 0x57 | 0x58 | 0xbb)
        {
            return None;
        }
        let Some((slots, false)) = op.local_access() else {
            continue;
        };
        if binding.is_some()
            || !matches!(op.opcode, 0x3a | 0x4b..=0x4e)
            || locations.get(&op.offset) != Some(&start)
        {
            return None;
        }
        binding = Some((slots.start, op.offset + op.len));
    }
    let (slot, initialized) = binding?;
    let mut has_binding = false;
    for local in locals
        .iter()
        .filter(|local| array_or_object_class(local.descriptor) == Some(declaration.child))
    {
        let start_pc = u32::from(local.start_pc);
        if start_pc < first_offset || start_pc + u32::from(local.length) > cut {
            return None;
        }
        has_binding |= u32::from(local.index) == slot && start_pc == initialized;
    }
    // The debug lifetime can end before the actual JVM value is dead.
    (has_binding && dead_in_straight_line(&instructions[exit..], slot)).then_some(end)
}

fn transfers_control(op: &Instruction) -> bool {
    matches!(op.operand, Operand::Branch(_) | Operand::Switch { .. })
        || matches!(op.opcode, 0xa9 | 0xac..=0xb1 | 0xbf)
}

fn dead_in_straight_line(instructions: &[Instruction], slot: u32) -> bool {
    for op in instructions {
        if let Some((slots, read)) = op.local_access()
            && slots.contains(&slot)
        {
            return !read;
        }
        if transfers_control(op) {
            return matches!(op.opcode, 0xac..=0xb1 | 0xbf);
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{bytecode, dead_in_straight_line};

    #[test]
    fn slot_read_before_redefinition_prevents_a_scope_cut() {
        let instructions = bytecode::decode(&[
            0x2c, 0x57, // aload_2; pop
            0x01, 0x4d, 0xb1, // aconst_null; astore_2; return
        ])
        .unwrap();
        assert!(!dead_in_straight_line(&instructions, 2));
        assert!(dead_in_straight_line(&instructions[2..], 2));
    }
}

fn referenced_class<'a>(
    class: &'a ClassFile<'_>,
    op: &Instruction,
) -> Result<Option<&'a str>, ClassError> {
    let index = match op.operand {
        Operand::Constant(index)
        | Operand::InvokeInterface { index, .. }
        | Operand::MultiANewArray { index, .. } => index,
        _ => return Ok(None),
    };
    let pool = &class.pool;
    Ok(match pool.get(index)? {
        Constant::Class(_) => {
            let name = pool.class_name(index)?;
            Some(array_or_object_class(name).unwrap_or(name))
        }
        Constant::Fieldref { .. }
        | Constant::Methodref { .. }
        | Constant::InterfaceMethodref { .. } => Some(pool.member_ref(index)?.0),
        _ => None,
    })
}

fn lambda_targets<'a>(
    class: &'a ClassFile<'_>,
    bootstraps: &[BootstrapMethod],
    op: &Instruction,
) -> Result<Vec<(&'a str, &'a str)>, ClassError> {
    let Operand::Constant(index) = op.operand else {
        return Ok(Vec::new());
    };
    let pool = &class.pool;
    let Constant::InvokeDynamic {
        bootstrap_index, ..
    } = *pool.get(index)?
    else {
        return Ok(Vec::new());
    };
    let Some(bootstrap) = bootstraps.get(usize::from(bootstrap_index)) else {
        return Ok(Vec::new());
    };
    let Constant::MethodHandle {
        reference_index, ..
    } = *pool.get(bootstrap.method_ref)?
    else {
        return Ok(Vec::new());
    };
    if pool.member_ref(reference_index)?.0 != "java/lang/invoke/LambdaMetafactory" {
        return Ok(Vec::new());
    }
    let owner = pool.class_name(class.this_class)?;
    let mut targets = Vec::new();
    for &argument in &bootstrap.arguments {
        if let Constant::MethodHandle {
            reference_index, ..
        } = *pool.get(argument)?
        {
            let (class, name, descriptor) = pool.member_ref(reference_index)?;
            if class == owner && name != "<init>" {
                targets.push((name, descriptor));
            }
        }
    }
    Ok(targets)
}

fn array_or_object_class(descriptor: &str) -> Option<&str> {
    descriptor
        .trim_start_matches('[')
        .strip_prefix('L')?
        .strip_suffix(';')
}
