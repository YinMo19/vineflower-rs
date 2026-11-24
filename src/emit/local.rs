// Based on Vineflower NestedClassProcessor (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::Peekable,
    rc::Rc,
};

use crate::{
    bytecode::{self, Instruction, Operand},
    classfile::{BootstrapMethod, ClassError, ClassFile, Code, Constant},
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
                        insertion: 0,
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
            let Some(&line) = locations.get(&op.offset) else {
                continue;
            };
            if let Some(class) = referenced_class(self.class, op)?
                && let Some(declaration) = declarations.get_mut(class)
            {
                declaration.add_use(line);
            }
            if op.opcode != 0xba {
                continue;
            }
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
        for local in code.local_variables(pool)? {
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
        has_following_line: bool,
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
        if any && has_following_line {
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
    insertion: usize,
    captures: BTreeSet<usize>,
    bindings: Option<AnonymousBindings>,
}

impl LocalDeclaration<'_> {
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
