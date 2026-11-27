//! Recover assert statements from the compiler's assertion field and throw.

use std::io;

use arcstr::ArcStr;

use crate::code::code_constants::{ACC_INTERFACE, CLINIT_NAME};
use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::exps::{ConstantValue, ExitType, Expr, ExprKind, Field, FunctionType};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{IfStatement, STATEDGE_ALL, Statement, StatementKind};
use crate::engine::class_nodes::ClassKind;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::{StructClass, StructMember, struct_field::StructField};
use crate::types::CodeType;

pub(crate) fn build(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
) -> io::Result<bool> {
    let cx = &mut *cx.enter_method(counters);
    if !cx.options.decompile_assert {
        return Ok(false);
    }
    let Some((holder, field)) = assertion_field(cx, class) else {
        return Ok(false);
    };
    let field = AssertionField {
        owner: holder.qualified_name.clone(),
        name: field.name.clone(),
        descriptor: field.descriptor.clone(),
    };

    let mut changed = false;
    if root.method(&cx.ir).name == CLINIT_NAME {
        changed |= clean_static_initializer(&mut cx.ir, counters, root, &field)?;
    }
    changed |= replace_assertions(cx, counters, root, &field)?;
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

pub(super) fn assertion_field<'a>(
    cx: &'a Cx,
    class: &'a StructClass,
) -> Option<(&'a StructClass, &'a StructField)> {
    let classes = &cx.class_nodes;
    if class.has_modifier(ACC_INTERFACE)
        && let Some(current) = classes.id(&class.qualified_name)
    {
        let mut root = current;
        while classes[root].kind != ClassKind::Root {
            root = classes[root]
                .parent
                .expect("Nested class has no enclosing root");
        }
        let order = classes.wrapper_order(root);
        let initialized = order
            .iter()
            .position(|&node| node == current)
            .map_or(&[][..], |index| &order[..index]);

        for &nested in &classes[root].nested {
            let Some(wrapper) = classes.wrapper_owner(nested) else {
                continue;
            };
            let published = classes[wrapper].wrapper.is_some();
            if !published && (cx.current_method.is_some() || !initialized.contains(&wrapper)) {
                continue;
            }
            let holder = classes[wrapper].class.as_ref();
            if holder.is_synthetic()
                && let Some(field) = class_assertion_field(cx, holder)
            {
                return Some((holder, field));
            }
        }
    }
    class_assertion_field(cx, class).map(|field| (class, field))
}

fn class_assertion_field<'a>(cx: &Cx, class: &'a StructClass) -> Option<&'a StructField> {
    cx.method_properties(class, "<clinit> ()V")?
        .assert_field
        .as_deref()
}

struct AssertionField {
    owner: ArcStr,
    name: ArcStr,
    descriptor: ArcStr,
}

impl AssertionField {
    fn matches(&self, reference: &Field) -> bool {
        reference.classname.as_ref() == Some(&self.owner)
            && reference.name == self.name
            && reference.descriptor.descriptor_string == self.descriptor
    }
}

fn clean_static_initializer(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    stat: StatId,
    field: &AssertionField,
) -> io::Result<bool> {
    let mut changed = false;
    let children = ir[stat].stats.to_vec();
    for child in children {
        changed |= clean_static_initializer(ir, counters, child, field)?;
    }
    let StatementKind::If(branch) = ir[stat].kind else {
        return Ok(changed);
    };
    if branch.if_stat.is_none()
        && let Some([left, right]) =
            function_operands(ir, if_condition(ir, branch), FunctionType::Ne)
        && let ExprKind::Field(reference) = &ir[*left].kind
        && field.matches(reference)
        && is_zero_constant(ir, *right)?
    {
        let empty = Statement::new_empty_basic_block(ir, counters);
        stat.replace_with(ir, empty);
        changed = true;
    }
    Ok(changed)
}

fn replace_assertions(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    field: &AssertionField,
) -> io::Result<bool> {
    let mut changed = false;
    // A nested assertion can replace an ancestor. Visit the original children
    // for this descent, then take a fresh snapshot after each replacement.
    let children = cx.ir[stat].stats.to_vec();
    for child in children {
        changed |= replace_assertions(cx, counters, child, field)?;
    }

    'replace: loop {
        let children = cx.ir[stat].stats.to_vec();
        for child in children {
            if let StatementKind::If(branch) = cx.ir[child].kind
                && cx.ir[child].parent.is_some()
                && replace_assertion(cx, counters, stat, child, branch, field)?
            {
                changed = true;
                continue 'replace;
            }
        }
        return Ok(changed);
    }
}

fn replace_assertion(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    mut parent: StatId,
    stat: StatId,
    branch: IfStatement,
    field: &AssertionField,
) -> io::Result<bool> {
    let ir = &cx.ir;
    let then_branch = branch.if_stat.or_else(|| {
        let edge = &ir[branch.if_edge.unwrap()];
        (edge.edge_type == EdgeType::Break).then_some(edge.destination)
    });
    let (throw_in_if, throw_stat, constructor) = if let Some(then_branch) = then_branch
        && let Some(constructor) = assertion_error(ir, then_branch)
    {
        (true, then_branch, constructor)
    } else if let Some(else_branch) = branch.else_stat
        && let Some(constructor) = assertion_error(ir, else_branch)
    {
        (false, else_branch, constructor)
    } else {
        return Ok(false);
    };

    let condition = if_condition(ir, branch);
    let condition = Expr::copy(cx, counters, condition);
    let Some(assertion) = extract_assertion(cx, stat, condition, field, throw_in_if)? else {
        return Ok(false);
    };
    let ir = &mut cx.ir;
    let condition = assertion.condition.map(|condition| {
        if assertion.replacement == Replacement::Assignment {
            condition
        } else {
            let offsets = ir[constructor].bytecode.clone();
            Expr::function(
                ir,
                counters,
                FunctionType::BoolNot,
                vec![condition],
                offsets,
            )
        }
    });
    let ExprKind::Invocation(call) = &ir[constructor].kind else {
        unreachable!("AssertionError constructor must be an invocation");
    };
    let message = call.parameters.first().copied();
    let expression = Expr::new(ir, counters, ExprKind::Assert { condition, message }, None);

    let block = Statement::new_empty_basic_block(ir, counters);
    let expressions = ir[block].exprents.unwrap();
    ir[expressions].push(expression);

    let first = ir[stat].first.unwrap();
    let head = ir[first].exprents.is_some_and(|list| !ir[list].is_empty());
    let replacement =
        if branch.has_else || (assertion.replacement != Replacement::Assignment && head) {
            for edge in [branch.if_edge, branch.else_edge].into_iter().flatten() {
                first.remove_successor(ir, edge);
            }

            let other = if throw_in_if {
                branch.else_stat
            } else {
                branch.if_stat
            };
            let mut children = Vec::new();
            if head {
                children.push(first);
            }
            children.push(block);
            if branch.has_else {
                children.push(other.expect("If-else assertion has no surviving branch"));
            }
            let sequence = Statement::new_sequence(ir, counters, &children);
            sequence.set_all_parent(ir);
            for pair in children.windows(2) {
                let edge = StatEdge::new(ir, EdgeType::Regular, pair[0], pair[1], None);
                pair[0].add_successor(ir, edge);
            }

            if (branch.has_else || !throw_in_if)
                && let Some(edge) = other
                    .expect("Assertion has no surviving branch")
                    .get_successor_edges(ir, STATEDGE_ALL)
                    .first()
                    .copied()
                && ir[edge].closure == Some(stat)
            {
                sequence.add_labeled_edge(ir, edge);
            }
            sequence
        } else {
            block
        };

    for edge in throw_stat.get_successor_edges(ir, STATEDGE_ALL) {
        edge.remove(ir);
    }
    for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
        if ir[edge].edge_type == EdgeType::Break {
            edge.change_source(ir, block);
        }
    }

    let definitions = ir[stat].var_definitions.clone();
    ir[replacement].var_definitions.extend(definitions);

    if assertion.replacement == Replacement::Assignment {
        for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
            edge.remove(ir);
        }
        ir[stat].parent = None;
        parent.replace_with(ir, replacement);
    } else {
        parent.replace_statement(ir, stat, replacement);
    }

    if assertion.replacement == Replacement::Parent {
        let outer = ir[parent].parent.unwrap();
        let head = outer.get_basic_head(ir);
        if !ir[ir[head].exprents.unwrap()].is_empty() {
            parent = Statement::new_sequence(ir, counters, &[head, parent]);
            ir[parent].parent = Some(outer);
        }
        outer.replace_with(ir, parent);
    }

    Ok(true)
}

fn assertion_error(ir: &Ir, stat: StatId) -> Option<ExprId> {
    let [only] = ir[ir[stat].exprents?][..] else {
        return None;
    };
    let ExprKind::Exit {
        kind: ExitType::Throw,
        value: Some(value),
        ..
    } = ir[only].kind
    else {
        return None;
    };
    let ExprKind::New {
        new_type,
        constructor,
        ..
    } = &ir[value].kind
    else {
        return None;
    };
    (new_type.ty == CodeType::Object
        && new_type.array_dim == 0
        && new_type.name() == "java/lang/AssertionError")
        .then_some(*constructor)
        .flatten()
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Replacement {
    Statement,
    Parent,
    Assignment,
}

struct Assertion {
    condition: Option<ExprId>,
    replacement: Replacement,
}

fn extract_assertion(
    cx: &mut Cx,
    stat: StatId,
    mut expr: ExprId,
    field: &AssertionField,
    throw_in_if: bool,
) -> io::Result<Option<Assertion>> {
    if !matches!(cx.ir[expr].kind, ExprKind::Function { .. }) {
        return Ok(None);
    }
    if throw_in_if {
        expr = unwrap_double_negation(&cx.ir, expr);
    } else if let Some([inner]) = function_operands(&cx.ir, expr, FunctionType::BoolNot) {
        expr = *inner;
    }
    let ExprKind::Function { op, operands, .. } = &cx.ir[expr].kind else {
        return Err(invalid_data("Assertion condition is not a function"));
    };

    if *op == FunctionType::BoolAnd {
        let operands = [operands[0], operands[1]];
        for (index, operand) in operands.into_iter().enumerate() {
            if is_assertion_field(&cx.ir, operand, field)? {
                return Ok(Some(Assertion {
                    condition: Some(operands[1 - index]),
                    replacement: Replacement::Statement,
                }));
            }
        }
        for (index, operand) in operands.into_iter().enumerate() {
            if let Some(assertion) = extract_assertion(cx, stat, operand, field, throw_in_if)? {
                let condition = assertion.condition.ok_or_else(|| {
                    invalid_data("Assertion field removal left an empty boolean operand")
                })?;
                let ExprKind::Function { operands, .. } = &mut cx.ir[expr].kind else {
                    unreachable!()
                };
                operands[index] = condition;
                return Ok(Some(Assertion {
                    condition: Some(expr),
                    replacement: Replacement::Statement,
                }));
            }
        }
    } else if is_assertion_field(&cx.ir, expr, field)? {
        return Ok(Some(Assertion {
            condition: None,
            replacement: Replacement::Statement,
        }));
    } else if *op == FunctionType::Eq
        && let Some(parent) = parent_skipping_sequences(&cx.ir, stat)
        && let StatementKind::If(parent_branch) = cx.ir[parent].kind
    {
        let ir = &cx.ir;
        let head = stat.get_basic_head(ir);
        match ir[ir[head].exprents.unwrap()].as_slice() {
            [] if is_assertion_field(ir, if_condition(ir, parent_branch), field)? => {
                return Ok(Some(Assertion {
                    condition: Some(expr),
                    replacement: Replacement::Parent,
                }));
            }
            [assignment]
                if let ExprKind::Assignment { right, .. } = ir[*assignment].kind
                    && Expr::equals(cx, operands[0], right)
                    && is_zero_constant(ir, operands[1])? =>
            {
                return Ok(Some(Assertion {
                    condition: Some(*assignment),
                    replacement: Replacement::Assignment,
                }));
            }
            _ => {}
        }
    }
    Ok(None)
}

fn parent_skipping_sequences(ir: &Ir, mut stat: StatId) -> Option<StatId> {
    loop {
        stat = ir[stat].parent?;
        if !matches!(ir[stat].kind, StatementKind::Sequence) {
            return Some(stat);
        }
    }
}

fn is_assertion_field(ir: &Ir, expr: ExprId, field: &AssertionField) -> io::Result<bool> {
    let expr = unwrap_double_negation(ir, expr);
    if let Some([left, right]) = function_operands(ir, expr, FunctionType::Eq)
        && let ExprKind::Field(reference) = &ir[*left].kind
        && is_zero_constant(ir, *right)?
    {
        return Ok(field.matches(reference));
    }
    Ok(false)
}

fn unwrap_double_negation(ir: &Ir, expr: ExprId) -> ExprId {
    if let Some([first]) = function_operands(ir, expr, FunctionType::BoolNot)
        && let Some([inner]) = function_operands(ir, *first, FunctionType::BoolNot)
        && matches!(ir[*inner].kind, ExprKind::Function { .. })
    {
        *inner
    } else {
        expr
    }
}

fn if_condition(ir: &Ir, branch: IfStatement) -> ExprId {
    let head = ir[branch.head_exprents.unwrap()][0];
    let ExprKind::If { condition } = ir[head].kind else {
        unreachable!("Expected an if expression");
    };
    condition
}

fn function_operands(ir: &Ir, expr: ExprId, op: FunctionType) -> Option<&[ExprId]> {
    match &ir[expr].kind {
        ExprKind::Function {
            op: actual,
            operands,
            ..
        } if *actual == op => Some(operands),
        _ => None,
    }
}

fn is_zero_constant(ir: &Ir, expr: ExprId) -> io::Result<bool> {
    if let ExprKind::Constant { value, .. } = &ir[expr].kind {
        return match value {
            ConstantValue::Integer(value) => Ok(*value == 0),
            ConstantValue::Null => Ok(false),
            _ => Err(invalid_data(
                "Assertion comparison requires an integer constant",
            )),
        };
    }
    Ok(false)
}

fn invalid_data(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
