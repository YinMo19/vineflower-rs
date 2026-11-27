//! Match synthetic constructor slots to captured fields and enclosing locals.

use crate::code::code_constants::{
    ACC_FINAL, ACC_INTERFACE, ACC_MANDATED, ACC_PRIVATE, ACC_STATIC, ACC_SYNTHETIC, INIT_NAME,
};
use crate::decompiler::{
    exps::{Expr, ExprKind},
    flow::DirectEdgeType,
    ir::{ExprListId, Ir},
    vars::{var_version_pair::VarVersionPair as Version, versions::FinalType},
};
use crate::engine::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId},
    class_wrapper::MethodSlot,
};
use crate::structs::{StructMember, StructMethod};
use crate::types::MethodDescriptor;
use crate::util::{interpreter_util::make_unique_key, jhash::JHashMap};
use arcstr::ArcStr;
use index_vec::{IndexVec, define_index_type};
use std::{io, sync::Arc};

define_index_type! { struct CaptureId = u32; }
type Mask = Vec<Option<CaptureId>>;
type Constructors = JHashMap<ArcStr, Mask>;

// A shallow copy of a Java mask shares its mutable VarFieldPair objects.
// Merging different constructor masks can refine a pair in both copies.
#[derive(Clone, PartialEq, Eq)]
struct Capture {
    field: String,
    variable: Version,
    assigned: bool,
}

#[derive(Default)]
struct Captures(IndexVec<CaptureId, Capture>);

pub(super) fn compute(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    let mut captures = Captures::default();
    let mut masks = JHashMap::new();
    let mut has_member = false;
    let mut has_local = false;
    for i in 0..cx.class_nodes[node].nested.len() {
        let child = cx.class_nodes[node].nested[i];
        let nested = &cx.class_nodes[child];
        if nested.kind == ClassKind::Lambda
            || nested.class.is_synthetic()
            || nested.access & (ACC_STATIC | ACC_INTERFACE) != 0
            || nested.class.get_record_components().is_some()
        {
            continue;
        }
        has_member |= nested.kind == ClassKind::Member;
        has_local |= nested.kind != ClassKind::Member;
        let name = nested.class.qualified_name.clone();
        let constructors = captures.constructors(cx, child)?;
        if constructors.is_empty() {
            log::warn!("Nested class {name} has no constructor!");
        } else {
            masks.insert(name, (child, constructors));
        }
    }

    let mut call_sites = JHashMap::<ArcStr, Constructors>::new();
    if !has_member || has_local {
        let class = Arc::clone(&cx.class_nodes[node].class);
        for (index, method) in class.methods.iter().enumerate() {
            if !has_root(cx, node, index)? {
                continue;
            }
            for list in cx.wrapper_expr_lists(MethodSlot { node, index }) {
                for ix in 0..cx.ir[list].len() {
                    let expr = cx.ir[list][ix];
                    for id in Expr::all_exprents(&cx.ir, expr, true, true) {
                        let ExprKind::New {
                            constructor: Some(call),
                            ..
                        } = cx.ir[id].kind
                        else {
                            continue;
                        };
                        let ExprKind::Invocation(invoke) = &cx.ir[call].kind else {
                            unreachable!()
                        };
                        let Some(name) = &invoke.classname else {
                            continue;
                        };
                        let Some((child, constructors)) = masks.get(name) else {
                            continue;
                        };
                        if cx.class_nodes[*child].kind == ClassKind::Member {
                            continue;
                        }
                        let descriptor = invoke.descriptor.as_str();
                        let template = constructors
                            .get(descriptor)
                            .ok_or_else(|| invalid("Missing nested constructor mask"))?;
                        if !call_sites.contains_key(name) {
                            call_sites.insert(name.clone(), Constructors::new());
                        }
                        let sites = call_sites.get_mut(name).unwrap();
                        let current = captures.at_call(&cx.ir, template, &invoke.parameters)?;
                        if let Some(previous) = sites.get_mut(descriptor) {
                            for (slot, other) in previous.iter_mut().zip(&current) {
                                if slot.map(|id| &captures.0[id]) != other.map(|id| &captures.0[id])
                                {
                                    *slot = None;
                                }
                            }
                        } else {
                            sites.insert(descriptor.into(), current);
                        }
                        let child = &mut cx.class_nodes[*child];
                        if child
                            .enclosing_method
                            .as_ref()
                            .is_none_or(|key| class.get_method_by_key(key).is_none())
                        {
                            child.enclosing_method =
                                Some(make_unique_key(&method.name, &method.descriptor).into());
                        }
                    }
                }
            }
        }
    }

    for (name, (child, constructors)) in masks.iter() {
        let mut common = captures.intersection(constructors).unwrap();
        let mut callers = call_sites
            .get(name)
            .and_then(|sites| captures.intersection(sites))
            .unwrap_or_else(|| {
                let mut first = true;
                common
                    .iter()
                    .map(|&slot| slot.filter(|_| std::mem::take(&mut first)))
                    .collect()
            });
        captures.merge(&mut callers, &mut common, true);
        let nested = &mut cx.class_nodes[*child];
        for &pair in callers.iter().flatten() {
            let capture = &captures.0[pair];
            if capture.assigned && !capture.field.is_empty() {
                nested
                    .fields_to_vars
                    .insert(capture.field.clone(), capture.variable);
            }
        }
        for (descriptor, mask) in constructors.iter() {
            let mut mask = mask.clone();
            captures.merge(&mut mask, &mut callers, false);
            let index = nested
                .class
                .methods
                .index_of_key(make_unique_key(INIT_NAME, descriptor).as_str())
                .unwrap();
            nested.wrapper.as_mut().unwrap().methods[index].synthetic_parameters = Some(
                mask.into_iter()
                    .map(|id| {
                        id.and_then(|id| {
                            let capture = &captures.0[id];
                            (!capture.field.is_empty()).then_some(capture.variable)
                        })
                    })
                    .collect(),
            );
        }
    }
    Ok(())
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn has_root(cx: &Cx, node: ClassNodeId, index: usize) -> io::Result<bool> {
    let wrapper = cx.class_nodes[node]
        .wrapper
        .as_ref()
        .ok_or_else(|| invalid("Missing nested class wrapper"))?;
    Ok(matches!(wrapper.methods[index].body, Ok(Some(_))))
}

impl Captures {
    fn constructors(&mut self, cx: &mut Cx, child: ClassNodeId) -> io::Result<Constructors> {
        let class = Arc::clone(&cx.class_nodes[child].class);
        let mut masks = Constructors::new();
        for retry in [false, true] {
            let mut found = false;
            for (index, method) in class.methods.iter().enumerate() {
                if method.name != INIT_NAME || !has_root(cx, child, index)? {
                    continue;
                }
                let slot = MethodSlot { node: child, index };
                let graph = cx.wrapper_graph(slot);
                let first = &graph[graph.first];
                let head = first
                    .predecessors(DirectEdgeType::Regular)
                    .is_empty()
                    .then_some(first.exprents);
                let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
                let mut mask = Vec::with_capacity(descriptor.params.len());
                for (position, (var, _)) in descriptor.parameter_slots(false).enumerate() {
                    let capture = enclosing_field(
                        cx,
                        slot,
                        method,
                        head,
                        (position, var),
                        retry || class.methods.len() == 1,
                    )?;
                    found |= capture
                        .as_ref()
                        .is_some_and(|capture| !capture.field.is_empty());
                    mask.push(capture.map(|capture| self.0.push(capture)));
                }
                masks.insert(method.descriptor.clone(), mask);
            }
            if found {
                break;
            }
        }
        Ok(masks)
    }

    fn at_call(
        &mut self,
        ir: &Ir,
        mask: &Mask,
        arguments: &[crate::decompiler::ir::ExprId],
    ) -> io::Result<Mask> {
        if mask.len() > arguments.len() {
            return Err(invalid("Nested constructor has too few operands"));
        }
        Ok(mask
            .iter()
            .zip(arguments)
            .map(|(slot, &id)| {
                let template = &self.0[(*slot)?];
                let pair = Expr::variable(ir, id)?.pair();
                Some(self.0.push(Capture {
                    variable: pair,
                    ..template.clone()
                }))
            })
            .collect())
    }

    fn intersection(&mut self, constructors: &Constructors) -> Option<Mask> {
        let mut masks = constructors.values();
        let mut common = masks.next()?.clone();
        for mask in masks {
            self.merge(&mut common, &mut mask.clone(), false);
        }
        Some(common)
    }

    fn merge(&mut self, first: &mut Mask, second: &mut Mask, both: bool) {
        // The enclosing instance can occupy slot zero. All other captures
        // align from the end, allowing different user-written parameter counts.
        let suffix = first.len().min(second.len()).saturating_sub(1);
        for distance in 1..=suffix {
            let (left, right) = (first.len() - distance, second.len() - distance);
            self.merge_slot(&mut first[left], &mut second[right], both);
        }
        for slot in first.iter_mut().skip(1).rev().skip(suffix) {
            *slot = None;
        }
        if both {
            for slot in second.iter_mut().skip(1).rev().skip(suffix) {
                *slot = None;
            }
        }
        match (first.first_mut(), second.first_mut()) {
            (Some(left), Some(right)) => self.merge_slot(left, right, both),
            (Some(left), None) => *left = None,
            (None, Some(right)) if both => *right = None,
            _ => {}
        }
    }

    fn merge_slot(
        &mut self,
        left: &mut Option<CaptureId>,
        right: &mut Option<CaptureId>,
        both: bool,
    ) {
        if let (Some(first), Some(second)) = (*left, *right) {
            if !self.0[first].assigned || self.0[first].field.is_empty() {
                self.0[first].field = self.0[second].field.clone();
                self.0[first].assigned = self.0[second].assigned;
            } else if !self.0[second].assigned || self.0[second].field.is_empty() {
                if both {
                    self.0[second].field = self.0[first].field.clone();
                    self.0[second].assigned = self.0[first].assigned;
                }
            } else if self.0[first].field != self.0[second].field {
                *left = None;
                if both {
                    *right = None;
                }
                return;
            }
            if self.0[first].variable.var == -1 {
                self.0[first].variable = self.0[second].variable;
            } else {
                self.0[second].variable = self.0[first].variable;
            }
        } else {
            *left = None;
            if both {
                *right = None;
            }
        }
    }
}

fn enclosing_field(
    cx: &Cx,
    slot: MethodSlot,
    method: &StructMethod,
    head: Option<ExprListId>,
    (position, index): (usize, i32),
    heuristic: bool,
) -> io::Result<Option<Capture>> {
    let node = &cx.class_nodes[slot.node];
    let class = &node.class;
    let processor = &cx.ir[node.wrapper.as_ref().unwrap().methods[slot.index].variables];
    let parameter = Version::new(index, 0);
    if processor.versions.final_vars.get(&parameter) == Some(&FinalType::NonFinal) {
        return Ok(None);
    }

    let unknown = Version::new(-1, 0);
    if let Some(head) = head {
        for &expr in &cx.ir[head] {
            let Some((left, right)) = cx.ir[expr].as_assignment() else {
                continue;
            };
            if Expr::variable(&cx.ir, right).is_none_or(|var| var.index != index) {
                continue;
            }
            let ExprKind::Field(field) = &cx.ir[left].kind else {
                continue;
            };
            if field.classname.as_ref() == Some(&class.qualified_name)
                && let Some(declaration) =
                    class.get_field(&field.name, &field.descriptor.descriptor_string)
                && (declaration.is_synthetic()
                    || cx.options.synthetic_not_set
                        && declaration.name.contains('$')
                        && declaration.has_modifier(ACC_FINAL | ACC_PRIVATE))
            {
                return Ok(Some(Capture {
                    field: make_unique_key(&field.name, &field.descriptor.descriptor_string),
                    variable: unknown,
                    assigned: true,
                }));
            }
        }
    }

    // Upstream compares the raw class-file major here. An unused enclosing
    // instance may still be recorded in the parameter or nest metadata.
    let mut field = String::new();
    if class.version.major >= 21 {
        let ty = || {
            processor
                .versions
                .lower
                .get(&parameter)
                .ok_or_else(|| invalid("Missing enclosing parameter type"))
        };
        let name = processor
            .names
            .get(&parameter)
            .and_then(Option::as_deref)
            .unwrap_or("null");
        if method
            .attributes
            .method_parameters
            .as_ref()
            .and_then(|attr| attr.entries.get(position))
            .is_some_and(|entry| entry.access_flags & (ACC_MANDATED | ACC_SYNTHETIC) != 0)
        {
            field = make_unique_key(name, &ty()?.to_string());
        } else if index == 1
            && let Some(host) = &class.attributes.nest_host
        {
            let ty = ty()?;
            if let Some(outer) = &ty.value
                && (heuristic && host.get_host_class(&class.pool) == *outer
                    || node.kind == ClassKind::Anonymous && node.enclosing_classes.contains(outer))
            {
                field = make_unique_key(name, &ty.to_string());
            }
        }
    }
    Ok(Some(Capture {
        field,
        variable: unknown,
        assigned: false,
    }))
}
