//! Place local class declarations before their first use in the enclosing method.

use rustc_hash::FxHashSet;

use crate::decompiler::exps::{Expr, ExprKind, Invocation, Variable};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::{LoopType, StatementKind};
use crate::engine::counter_container::VAR_COUNTER;
use crate::structs::consts::{ConstantValue, PooledConstant};
use crate::types::{CodeType, VarType};

use super::super::{Cx, class_nodes::ClassNodeId, class_wrapper::MethodSlot};

pub(super) fn set_local_class_definition(cx: &mut Cx, method: MethodSlot, node: ClassNodeId) {
    let wrapper = method.get(cx);
    let Ok(Some(body)) = &wrapper.body else {
        let wrapper = method.get_mut(cx);
        wrapper.add_comment(
            "$VF: Couldn't set local class definition as local class statement was null",
        );
        wrapper.add_error_comment = true;
        return;
    };
    let root = body.root;
    let owner = wrapper.variables;
    let class_type = VarType::from_signature_cl(&cx.class_nodes[node].class.qualified_name, true);

    let mut references = FxHashSet::default();
    let scope = definition_statement(cx, root, &class_type, &mut references).unwrap_or_else(|| {
        cx.ir[root]
            .first
            .expect("Method root has no first statement")
    });
    let first = scope.find_first_block(&cx.ir, |stat| references.contains(&stat));
    let body = first.and_then(|stat| cx.ir[stat].exprents);
    let target = first.unwrap_or(scope);
    let expressions = body.map_or(cx.ir[target].var_definitions.as_slice(), |list| {
        &cx.ir[list]
    });
    let position = expressions
        .iter()
        .position(|&expr| search_for_class(cx, expr, &class_type))
        .unwrap_or(expressions.len());

    let Ok(Some(method_body)) = &mut method.get_mut(cx).body else {
        unreachable!("Method body was already checked");
    };
    let index = method_body.counters.get_counter_and_increment(VAR_COUNTER);
    let mut variable = Variable::in_method(index, class_type, owner);
    variable.definition = true;
    variable.class_definition = true;
    let declaration = Expr::new_ambient(cx, ExprKind::Variable(variable), None);
    if let Some(list) = body {
        cx.ir[list].insert(position, declaration);
    } else {
        cx.ir[target].var_definitions.insert(position, declaration);
    }
}

fn definition_statement(
    cx: &Cx,
    stat: StatId,
    class_type: &VarType,
    references: &mut FxHashSet<StatId>,
) -> Option<StatId> {
    let ir = &cx.ir;
    let mut scope = None;
    let mut headers = Vec::new();
    let expressions = if let Some(list) = ir[stat].exprents {
        ir[list].as_slice()
    } else {
        for &child in &ir[stat].stats {
            if let Some(nested) = definition_statement(cx, child, class_type, references) {
                if scope.is_some() {
                    scope = Some(stat);
                    break;
                }
                scope = Some(nested);
            }

            if let StatementKind::Do(header) = ir[child].kind {
                for list in [header.init, header.condition].into_iter().flatten() {
                    headers.extend(&ir[list]);
                }
            }
        }
        if scope != Some(stat) {
            append_headers(ir, stat, &mut headers);
        }
        headers.as_slice()
    };
    if scope != Some(stat)
        && expressions
            .iter()
            .any(|&expr| search_for_class(cx, expr, class_type))
    {
        scope = Some(stat);
    }
    if scope.is_some() {
        references.insert(stat);
    }
    scope
}

fn append_headers(ir: &Ir, stat: StatId, out: &mut Vec<ExprId>) {
    // This search skips the null entries in Java's loop header lists.
    let StatementKind::Do(header) = ir[stat].kind else {
        out.extend(stat.stat_exprents(ir));
        return;
    };
    let expressions = match header.ty {
        LoopType::Infinite => return,
        LoopType::While | LoopType::DoWhile => [header.condition(ir), None, None],
        LoopType::For => [header.init(ir), header.condition(ir), header.increment(ir)],
        LoopType::ForEach => [header.init(ir), header.increment(ir), None],
    };
    out.extend(expressions.into_iter().flatten());
}

fn search_for_class(cx: &Cx, expr: ExprId, class_type: &VarType) -> bool {
    let ir = &cx.ir;
    let name = class_type.name();
    Expr::all_exprents(ir, expr, true, true)
        .into_iter()
        .any(|expr| match &ir[expr].kind {
            ExprKind::Constant {
                var_type, value, ..
            } => {
                (var_type == &VarType::VARTYPE_CLASS
                    && matches!(value, ConstantValue::String(value) if value.utf16().eq(name.encode_utf16())))
                    || var_type == class_type
            }
            ExprKind::Field(field) => field.classname.as_deref() == Some(name),
            ExprKind::Invocation(invocation) => invocation_contains_class(invocation, name),
            ExprKind::New {
                new_type,
                constructor,
                lambda,
                ..
            } => {
                // The Java search conservatively treats lambda bodies as uses.
                *lambda
                    || new_type.ty == CodeType::Object && new_type.value.as_deref() == Some(name)
                    || constructor.is_some_and(|constructor| {
                        let ExprKind::Invocation(invocation) = &ir[constructor].kind else {
                            unreachable!("NewExprent constructor must be an invocation");
                        };
                        invocation_contains_class(invocation, name)
                    })
            }
            ExprKind::Variable(var) => {
                var.definition && type_contains_class(&var.inferred_expr_type(cx), class_type)
            }
            _ => false,
        })
}

fn invocation_contains_class(invocation: &Invocation, name: &str) -> bool {
    invocation.classname.as_deref() == Some(name)
        || invocation.bootstrap_arguments.iter().flat_map(|args| args.iter()).flatten().any(|arg| {
            matches!(arg, PooledConstant::Link(link) if link.classname.as_deref() == Some(name))
        })
}

fn type_contains_class(ty: &VarType, class_type: &VarType) -> bool {
    ty == class_type
        || ty.array_dim > 0 && ty.value == class_type.value
        || ty
            .arguments()
            .iter()
            .flatten()
            .any(|arg| type_contains_class(arg, class_type))
}
