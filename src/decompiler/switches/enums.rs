// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Resolve selectors lowered to enum ordinals or synthetic enum maps.

use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::io;

use super::{switch, switch_mut};
use crate::code::code_constants::{ACC_ENUM, ACC_FINAL, ACC_STATIC, ACC_SYNTHETIC};
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, Field, FunctionType};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::patterns::record::is_statement_match_throw;
use crate::decompiler::stats::Statement;
use crate::engine::class_wrapper::{MethodSlot, WrapperMethod};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::{FieldDescriptor, TypeFamily, VarType};
use crate::util::jhash::{JHashMap, JHashSet, JavaHash};

const SWITCH_MAP_FLAGS: i32 = ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC;

/// A failed synthetic map prevents string-switch recognition. A failed
/// direct ordinal probe still allows the other selector forms to be checked.
pub(super) fn simplify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    root: StatId,
) -> io::Result<Option<bool>> {
    let head = switch(&cx.ir, stat)
        .head_exprents
        .and_then(|list| cx.ir[list].first().copied())
        .ok_or_else(|| invalid("Switch has no expression header"))?;
    let ExprKind::SwitchHead {
        value: selector, ..
    } = cx.ir[head].kind
    else {
        unreachable!("Switch header must be a SwitchHeadExprent");
    };
    if simplify_ordinal(cx, counters, stat, root, head, selector)? {
        return Ok(Some(true));
    }

    let Some(array) = enum_array(cx, selector, root)? else {
        return Ok(None);
    };
    let ExprKind::Array {
        array: target,
        index,
        ..
    } = cx.ir[array].kind
    else {
        unreachable!("An enum-map selector must be an array access");
    };
    let mut mapping = EnumMapping::with_capacity(switch(&cx.ir, stat).cases.len());
    match &cx.ir[target].kind {
        ExprKind::Field(field) => {
            if let Some(owner) = &field.classname
                && let WrapperMethod::Ready { root, method } =
                    cx.wrapper_method(owner, "<clinit>", "()V")
            {
                read_field_map(cx, target, root, method, &mut mapping);
            }
        }
        ExprKind::Invocation(invocation) => {
            let source = invocation
                .classname
                .as_deref()
                .map_or(WrapperMethod::NoClassNode, |owner| {
                    cx.wrapper_method(owner, &invocation.name, "()[I")
                });
            match source {
                WrapperMethod::Unpublished => return Ok(Some(false)),
                WrapperMethod::Ready { method, .. } => read_method_map(cx, method, &mut mapping)?,
                WrapperMethod::NoClassNode | WrapperMethod::Missing | WrapperMethod::NoRoot => {}
            }
        }
        _ => unreachable!("An enum-map access has no field or accessor"),
    }

    let Some((labels, nullable)) = mapped_labels(cx, counters, stat, root, &mapping) else {
        return Ok(Some(false));
    };
    for (case, values) in switch_mut(&mut cx.ir, stat).cases.iter_mut().zip(labels) {
        case.values = values;
    }

    let ExprKind::Invocation(ordinal) = &cx.ir[index].kind else {
        return Err(invalid("Enum-map index is not an ordinal invocation"));
    };
    let receiver = ordinal
        .instance
        .ok_or_else(|| invalid("Ordinal invocation has no receiver"))?;
    let new_selector = Expr::copy(cx, counters, receiver);
    Expr::replace(&mut cx.ir, head, selector, new_selector);
    let offsets = cx.ir[selector].bytecode.clone();
    Expr::add_offsets(&mut cx.ir, new_selector, offsets.as_ref());

    if Expr::variable(&cx.ir, selector).is_some() {
        remove_unused_selector(cx, root, selector);
    }
    if nullable {
        inline_nullable_selector(cx, stat, root, head, new_selector);
    }
    Ok(Some(true))
}

fn simplify_ordinal(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    root: StatId,
    head: ExprId,
    selector: ExprId,
) -> io::Result<bool> {
    let mut labels = JHashMap::new();
    for case in &switch(&cx.ir, stat).cases {
        for &label in case.values.iter().flatten() {
            if !matches!(&cx.ir[label].kind, ExprKind::Constant { var_type, .. }
                if var_type.type_family == TypeFamily::Integer)
            {
                return Ok(false);
            }
            // The map retains the first actual expression for equal constants.
            labels.insert(LabelKey::new(&cx.ir, label), ());
        }
    }

    let ExprKind::Invocation(invoke) = &cx.ir[selector].kind else {
        return Ok(false);
    };
    if invoke.name != "ordinal" {
        return Ok(false);
    }
    let owner = invoke.classname.clone();
    let receiver = invoke.instance;
    let Some(class) = owner
        .as_deref()
        .and_then(|owner| cx.classes().get_class(owner))
    else {
        cx.ir[root].add_comment(
            "$VF: Unable to simplify switch-on-enum, as the enum class was not able to be found.",
            true,
        );
        return Ok(false);
    };
    if class.access_flags & ACC_ENUM == 0 {
        return Ok(false);
    }
    let enum_fields: Vec<_> = class
        .fields
        .iter()
        .filter(|field| field.access_flags & ACC_ENUM != 0)
        .collect();
    let owner = owner.expect("Resolved enum class has no name");
    let descriptor = FieldDescriptor::parse_descriptor(&format!("L{owner};"));

    let keys = JHashSet::from_collection(labels.keys().cloned(), labels.len());
    for key in keys.iter() {
        let label = key.expr;
        let occurrences: Vec<_> = switch(&cx.ir, stat)
            .cases
            .iter()
            .enumerate()
            .flat_map(|(case, slot)| {
                slot.values
                    .iter()
                    .enumerate()
                    .filter_map(move |(i, &value)| (value == Some(label)).then_some((case, i)))
            })
            .collect();
        for (case, index) in occurrences {
            let ordinal = integer_label(&cx.ir, label)
                .ok_or_else(|| invalid("Enum ordinal label is not an integer"))?;
            let field = usize::try_from(ordinal)
                .ok()
                .and_then(|ordinal| enum_fields.get(ordinal))
                .ok_or_else(|| invalid("Enum ordinal is outside its declared constants"))?;
            let expr = Expr::new(
                &mut cx.ir,
                counters,
                ExprKind::Field(Box::new(Field {
                    name: field.name.clone(),
                    classname: Some(owner.clone()),
                    instance: None,
                    descriptor: descriptor.clone(),
                    force_qualified: false,
                    was_condy: false,
                })),
                None,
            );
            switch_mut(&mut cx.ir, stat).cases[case].values[index] = Some(expr);
        }
    }

    if cx.ir[stat].phantom {
        let defaults: Vec<_> = switch(&cx.ir, stat)
            .cases
            .iter()
            .filter(|case| case.values.as_slice() == [None])
            .map(|case| case.statement)
            .filter(|&case| is_statement_match_throw(&cx.ir, case))
            .collect();
        for case in defaults {
            let empty = Statement::new_empty_basic_block(&mut cx.ir, counters);
            case.replace_with(&mut cx.ir, empty);
        }
    }

    let receiver = receiver.ok_or_else(|| invalid("Ordinal invocation has no receiver"))?;
    Expr::replace(&mut cx.ir, head, selector, receiver);
    Ok(true)
}

fn enum_array(cx: &Cx, selector: ExprId, root: StatId) -> io::Result<Option<ExprId>> {
    let ir = &cx.ir;
    let mut candidate = selector;
    if let ExprKind::Function {
        op: FunctionType::Ternary,
        operands,
        ..
    } = &ir[selector].kind
        && let &[condition, yes, no] = operands.as_slice()
        && let ExprKind::Function {
            op: FunctionType::Ne,
            operands,
            ..
        } = &ir[condition].kind
        && Expr::variable(ir, operands[0]).is_some()
        && Expr::expr_type(cx, operands[1]) == VarType::VARTYPE_NULL
        && matches!(&ir[no].kind, ExprKind::Constant {
            value: ConstantValue::Integer(-1), var_type, ..
        } if *var_type == VarType::VARTYPE_INT)
    {
        candidate = yes;
    }

    if Expr::variable(ir, selector).is_some() {
        if Expr::expr_type(cx, selector).to_string() != "I" {
            return Ok(None);
        }
        match assignments_of(cx, root, selector).as_slice() {
            [] => {}
            &[assignment] => candidate = ir[assignment].as_assignment().unwrap().1,
            _ => return Ok(None),
        }
    }

    Ok(is_enum_array(cx, candidate)?.then_some(candidate))
}

fn is_enum_array(cx: &Cx, expr: ExprId) -> io::Result<bool> {
    let ir = &cx.ir;
    let ExprKind::Array { array, index, .. } = ir[expr].kind else {
        return Ok(false);
    };
    match &ir[array].kind {
        ExprKind::Field(field) => {
            let node = field
                .classname
                .as_deref()
                .and_then(|owner| cx.class_nodes.id(owner));
            let descriptor = field.descriptor.descriptor_string.as_str();
            let Some(node) = node.filter(|_| descriptor == "[I") else {
                let ordinal = matches!(&ir[index].kind, ExprKind::Invocation(invoke) if invoke.name == "ordinal");
                return Ok(field.name.starts_with("$SwitchMap") || ordinal && field.is_static());
            };
            let class = cx
                .class_nodes
                .wrapper_owner(node)
                .filter(|&owner| cx.class_nodes[owner].wrapper.is_some())
                .map_or(&cx.class_nodes[node].class, |owner| {
                    &cx.class_nodes[owner].class
                });
            let declaration = class
                .get_field(&field.name, descriptor)
                .ok_or_else(|| invalid("Enum switch-map field declaration is absent"))?;
            Ok(
                declaration.access_flags & SWITCH_MAP_FLAGS == SWITCH_MAP_FLAGS
                    && class.access_flags & ACC_SYNTHETIC != 0,
            )
        }
        ExprKind::Invocation(invoke) => Ok(invoke.name.starts_with("$SWITCH_TABLE$")),
        _ => Ok(false),
    }
}

type EnumMapping = JHashMap<LabelKey, Option<ExprId>>;

fn read_field_map(
    cx: &mut Cx,
    field: ExprId,
    method_root: StatId,
    method: MethodSlot,
    mapping: &mut EnumMapping,
) {
    let assignments = assignments_of(cx, method_root, field);
    let field_assignment = match assignments.as_slice() {
        [assignment] => Some(*assignment),
        _ => None,
    };
    let mut encountered = false;
    for list in cx.wrapper_expr_lists(method) {
        for &expression in &cx.ir[list] {
            let Some((left, right)) = cx.ir[expression].as_assignment() else {
                continue;
            };
            if let ExprKind::Array { array, index, .. } = cx.ir[left].kind {
                let targets_field = Expr::equals(cx, array, field)
                    || !encountered
                        && Expr::variable(&cx.ir, array).is_some()
                        && field_assignment.is_some_and(|assignment| {
                            let (_, source) = cx.ir[assignment].as_assignment().unwrap();
                            Expr::equals(cx, source, array)
                        });
                if targets_field && let ExprKind::Invocation(invoke) = &cx.ir[index].kind {
                    mapping.insert(LabelKey::new(&cx.ir, right), invoke.instance);
                }
            } else if field_assignment
                .is_some_and(|assignment| Expr::equals(cx, expression, assignment))
            {
                encountered = true;
            }
        }
    }
}

fn read_method_map(cx: &mut Cx, method: MethodSlot, mapping: &mut EnumMapping) -> io::Result<()> {
    for list in cx.wrapper_expr_lists(method) {
        for &expression in &cx.ir[list] {
            if let Some((left, right)) = cx.ir[expression].as_assignment()
                && let ExprKind::Array { index, .. } = cx.ir[left].kind
            {
                let ExprKind::Invocation(invoke) = &cx.ir[index].kind else {
                    return Err(invalid(
                        "Enum-map method assignment has a non-invocation index",
                    ));
                };
                mapping.insert(LabelKey::new(&cx.ir, right), invoke.instance);
            }
        }
    }
    Ok(())
}

fn mapped_labels(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    root: StatId,
    mapping: &EnumMapping,
) -> Option<(Vec<Vec<Option<ExprId>>>, bool)> {
    let mut nullable = false;
    let mut mapped = Vec::with_capacity(switch(&cx.ir, stat).cases.len());
    for index in 0..switch(&cx.ir, stat).cases.len() {
        let labels = switch(&cx.ir, stat).cases[index].values.clone();
        let mut replacements = Vec::with_capacity(labels.len());
        for label in labels {
            let replacement = if let Some(label) = label {
                let value = mapping
                    .get(&LabelKey::new(&cx.ir, label))
                    .copied()
                    .flatten();
                let real = if let Some(value) = value {
                    Expr::copy(cx, counters, value)
                } else if let Some(ordinal) = integer_label(&cx.ir, label) {
                    if ordinal == -1 {
                        nullable = true;
                        Expr::new(
                            &mut cx.ir,
                            counters,
                            Expr::constant(VarType::VARTYPE_NULL, ConstantValue::Null, false),
                            None,
                        )
                    } else if let Some(key) = mapping.keys().find(|key| {
                        integer_label(&cx.ir, key.expr).is_some_and(|value| value > ordinal)
                    }) {
                        Expr::copy(cx, counters, key.expr)
                    } else {
                        report_unmapped(cx, root, label);
                        return None;
                    }
                } else {
                    report_unmapped(cx, root, label);
                    return None;
                };
                Some(real)
            } else {
                None
            };
            replacements.push(replacement);
        }
        mapped.push(replacements);
    }
    Some((mapped, nullable))
}

fn report_unmapped(cx: &mut Cx, root: StatId, label: ExprId) {
    cx.ir[root].add_comment("$VF: Unable to simplify switch on enum", true);
    let method = root.method(&cx.ir);
    log::error!(
        "Unable to simplify switch on enum: {:?} not found in method {} {}",
        cx.ir[label].kind,
        method.class_qualified_name,
        method.name
    );
}

fn remove_unused_selector(cx: &mut Cx, root: StatId, selector: ExprId) {
    let references = find_exprs(cx, root, false, |cx, expr| {
        Expr::is_var_referenced(&cx.ir, selector, expr, &[])
    });
    let &[(stat, expr)] = references.as_slice() else {
        return;
    };
    if let Some((left, _)) = cx.ir[expr].as_assignment()
        && Expr::equals(cx, left, selector)
    {
        let list = cx.ir[stat].exprents.unwrap();
        if let Some(index) = cx.ir[list]
            .iter()
            .position(|&other| Expr::equals(cx, expr, other))
        {
            cx.ir[list].remove(index);
        }
    }
}

fn inline_nullable_selector(
    cx: &mut Cx,
    stat: StatId,
    root: StatId,
    head: ExprId,
    selector: ExprId,
) {
    let ir = &cx.ir;
    let Some(used_var) = Expr::variable(ir, selector) else {
        return;
    };
    let Some(list) = ir[stat.get_basic_head(ir)].exprents else {
        return;
    };
    let Some((left, right)) = ir[list].last().and_then(|&expr| ir[expr].as_assignment()) else {
        return;
    };
    if Expr::variable(ir, left).is_some_and(|var| var.pair() == used_var.pair())
        && !Expr::is_var_referenced_in_stat(ir, left, root, &[selector])
    {
        cx.ir[list].pop();
        Expr::replace(&mut cx.ir, head, selector, right);
    }
}

fn assignments_of(cx: &Cx, root: StatId, target: ExprId) -> Vec<ExprId> {
    find_exprs(cx, root, true, |cx, expr| {
        cx.ir[expr]
            .as_assignment()
            .is_some_and(|(left, _)| Expr::equals(cx, left, target))
    })
    .into_iter()
    .map(|(_, expr)| expr)
    .collect()
}

/// SwitchHelper.findExprents visits body expressions by statement BFS.
fn find_exprs(
    cx: &Cx,
    root: StatId,
    only_one_stat: bool,
    matches: impl Fn(&Cx, ExprId) -> bool,
) -> Vec<(StatId, ExprId)> {
    let mut result = Vec::new();
    let mut pending = VecDeque::from([root]);
    while let Some(stat) = pending.pop_front() {
        pending.extend(cx.ir[stat].stats.iter().copied());
        if let Some(list) = cx.ir[stat].exprents {
            result.extend(
                cx.ir[list]
                    .iter()
                    .copied()
                    .filter(|&expr| matches(cx, expr))
                    .map(|expr| (stat, expr)),
            );
            if only_one_stat && !result.is_empty() {
                break;
            }
        }
    }
    result
}

fn integer_label(ir: &Ir, expr: ExprId) -> Option<i32> {
    match &ir[expr].kind {
        ExprKind::Constant {
            var_type,
            value: ConstantValue::Integer(value),
            ..
        } if var_type.type_family == TypeFamily::Integer => Some(*value),
        _ => None,
    }
}

/// ConstExprent has a value hash. Other Exprents use Object.hashCode,
/// so the arena identity models their key when the JVM hash is unavailable.
#[derive(Clone)]
struct LabelKey {
    expr: ExprId,
    class_name: &'static str,
    constant: Option<(VarType, ConstantValue)>,
}

impl LabelKey {
    fn new(ir: &Ir, expr: ExprId) -> Self {
        let constant = match &ir[expr].kind {
            ExprKind::Constant {
                var_type, value, ..
            } => Some((var_type.clone(), value.clone())),
            _ => None,
        };
        // These Exprent subclasses all share the same Java package.
        let class_name = match &ir[expr].kind {
            ExprKind::Array { .. } => "ArrayExprent",
            ExprKind::Assert { .. } => "AssertExprent",
            ExprKind::Assignment { .. } => "AssignmentExprent",
            ExprKind::Constant { .. } => "ConstExprent",
            ExprKind::Exit { .. } => "ExitExprent",
            ExprKind::Field(_) => "FieldExprent",
            ExprKind::Function { .. } => "FunctionExprent",
            ExprKind::If { .. } => "IfExprent",
            ExprKind::Invocation(_) => "InvocationExprent",
            ExprKind::Monitor { .. } => "MonitorExprent",
            ExprKind::New { .. } => "NewExprent",
            ExprKind::Pattern(_) => "PatternExprent",
            ExprKind::Switch { .. } => "SwitchExprent",
            ExprKind::SwitchHead { .. } => "SwitchHeadExprent",
            ExprKind::Variable(_) => "VarExprent",
            ExprKind::Yield { .. } => "YieldExprent",
        };
        Self {
            expr,
            class_name,
            constant,
        }
    }
}

impl PartialEq for LabelKey {
    fn eq(&self, other: &Self) -> bool {
        match (&self.constant, &other.constant) {
            (Some(left), Some(right)) => left == right,
            (None, None) => self.expr == other.expr,
            _ => false,
        }
    }
}

impl Eq for LabelKey {}

impl Hash for LabelKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.java_hash().hash(state);
    }
}

impl JavaHash for LabelKey {
    fn java_hash(&self) -> i32 {
        let Some((ty, value)) = &self.constant else {
            return self.expr.index() as i32;
        };
        let value = match value {
            ConstantValue::Null => 0,
            ConstantValue::Integer(value) => *value,
            ConstantValue::Long(value) => value.java_hash(),
            ConstantValue::Float(value) => {
                if value.is_nan() {
                    0x7fc0_0000
                } else {
                    value.to_bits() as i32
                }
            }
            ConstantValue::Double(value) => {
                let bits = if value.is_nan() {
                    0x7ff8_0000_0000_0000
                } else {
                    value.to_bits() as i64
                };
                bits.java_hash()
            }
            ConstantValue::String(value) => value.java_hash(),
        };
        ty.java_hash().wrapping_mul(31).wrapping_add(value)
    }

    fn java_class_name(&self) -> Option<&'static str> {
        Some(self.class_name)
    }

    fn java_identity(&self) -> Option<u64> {
        Some(self.expr.index() as u64)
    }
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
