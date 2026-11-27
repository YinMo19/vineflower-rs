//! Locate declarations after the first variable-merge pass.

use std::collections::VecDeque;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::exps::{Expr, ExprKind, Variable};
use crate::decompiler::flow::flatten::build_direct_graph;
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::stats::{LoopType, StatementKind};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::method_timeout::checkpoint;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::attr::LocalVariable;
use crate::types::MethodDescriptor;
use crate::util::jhash::{JHashMap, JHashSet};

pub(super) struct ImplicitDefinitions(FxHashSet<i32>);

/// Reserve the implicit parameters and receiver before merging variables.
pub(super) fn initialize(
    cx: &mut Cx,
    root: StatId,
    owner: VarProcessorId,
    descriptor: &MethodDescriptor,
) -> ImplicitDefinitions {
    let method = Arc::clone(root.method(&cx.ir));
    let has_receiver = method.access_flags & ACC_STATIC == 0;
    let parameter_names = method
        .attributes
        .method_parameters
        .as_ref()
        .filter(|_| cx.options.use_method_parameters)
        .map_or(&[][..], |attribute| attribute.entries.as_slice());

    let mut implicit = FxHashSet::default();
    let processor = &mut cx.ir[owner];
    processor.names = JHashMap::new();
    for (position, (slot, _)) in descriptor.parameter_slots(!has_receiver).enumerate() {
        implicit.insert(slot);
        let name = match parameter_names.get(position) {
            Some(entry) => processor.name_collector.free_name(entry.name.as_deref()),
            None => Some(processor.name_collector.free_index(slot)),
        };
        processor.names.insert(VarVersionPair::new(slot, 0), name);
    }

    if has_receiver {
        implicit.insert(0);
        let receiver = VarVersionPair::new(0, 0);
        processor
            .this_vars
            .insert(receiver, method.class_qualified_name.clone());
        processor
            .names
            .insert(receiver, Some(arcstr::literal!("this")));
        processor.name_collector.add_name("this");
    }
    ImplicitDefinitions(implicit)
}

/// Mark implicit definitions, then place each remaining variable's declaration.
pub(super) fn place(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
    mut implicit: ImplicitDefinitions,
) {
    let ir = &mut cx.ir;
    mark_implicit_definitions(ir, root, owner, &mut implicit);

    let mut scopes = DeclarationScopes::default();
    scopes.init_statement(ir, root);
    // The upstream constructor builds the graph even with validation disabled.
    build_direct_graph(ir, root);

    for (&index, &stat) in scopes.definitions.iter() {
        checkpoint();
        if implicit.0.contains(&index) {
            continue;
        }

        let pair = VarVersionPair::new(index, 0);
        let processor = &mut ir[owner];
        let name = processor.name_collector.free_index(index);
        processor.names.insert(pair, Some(name));

        let Some(scope) = place_in_loop_header(ir, stat, index) else {
            continue;
        };
        let first_block = scope.find_first_block(ir, |stat| {
            scopes.statement_vars[&ir[stat].id].contains(&index)
        });
        let body = first_block.and_then(|first| ir[first].exprents);
        let first = first_block.unwrap_or(scope);
        let expressions = body.map_or(&ir[first].var_definitions, |list| &ir[list]);
        let mut insertion = expressions.len();
        let mut assignment = None;
        for (position, &expr) in expressions.iter().enumerate() {
            assignment = assigned_variable(ir, expr, index);
            if assignment.is_some()
                || Expr::children(ir, expr).any(|child| Expr::contains_var_index(ir, child, index))
            {
                insertion = position;
                break;
            }
        }
        if let Some(assignment) = assignment {
            mark_definition(ir, assignment);
            continue;
        }

        let ty = ir[owner].versions.lower.get(&pair).cloned();
        let mut variable = Variable::in_method(index, ty, owner);
        variable.definition = true;
        let declaration = Expr::new(ir, counters, ExprKind::Variable(variable), None);
        if let Some(lvt) = find_statement_lvt(ir, scope, index).cloned() {
            Expr::set_local_variable(ir, declaration, lvt);
        }

        match body {
            Some(list) => ir[list].insert(insertion, declaration),
            None => ir[first].var_definitions.insert(insertion, declaration),
        }
    }
}

fn mark_implicit_definitions(
    ir: &mut Ir,
    root: StatId,
    owner: VarProcessorId,
    implicit: &mut ImplicitDefinitions,
) {
    let mut pending = VecDeque::from([root]);
    while let Some(stat) = pending.pop_front() {
        for expr in stat.implicitly_defined_vars(ir) {
            let pair = Expr::variable(ir, expr)
                .expect("Expected an implicitly defined variable")
                .pair();
            implicit.0.insert(pair.var);
            let processor = &mut ir[owner];
            let name = processor.name_collector.free_index(pair.var);
            processor.names.insert(pair, Some(name));
            mark_definition(ir, expr);
        }
        pending.extend(ir[stat].stats.iter().copied());
    }
}

#[derive(Default)]
struct DeclarationScopes {
    definitions: JHashMap<i32, StatId>,
    statement_vars: FxHashMap<i32, JHashSet<i32>>,
}

impl DeclarationScopes {
    fn init_statement(&mut self, ir: &Ir, stat: StatId) -> &JHashSet<i32> {
        checkpoint();
        let mut counts = JHashMap::new();
        if let Some(list) = ir[stat].exprents {
            count_expression_vars(ir, ir[list].iter().copied(), &mut counts);
        } else {
            let mut headers = Vec::new();
            for &child in &ir[stat].stats {
                for &index in self.init_statement(ir, child).iter() {
                    let count = counts.get(&index).copied().unwrap_or(0);
                    counts.insert(index, count + 1);
                }

                match ir[child].kind {
                    StatementKind::Do(header)
                        if matches!(header.ty, LoopType::While | LoopType::DoWhile) =>
                    {
                        headers.push(header.condition(ir).expect("Missing loop condition"));
                    }
                    StatementKind::CatchAll {
                        is_finally: true,
                        monitor: Some(monitor),
                        ..
                    } => headers.push(monitor),
                    _ => {}
                }
            }
            headers.extend(stat.stat_exprents(ir));
            count_expression_vars(ir, headers, &mut counts);
        }

        // A reference in two children or in this header requires this scope.
        for (&index, &count) in counts.iter() {
            if count > 1 {
                self.definitions.insert(index, stat);
            }
        }
        let variables = JHashSet::from_collection(counts.keys().copied(), counts.len());
        let id = ir[stat].id;
        self.statement_vars.insert(id, variables);
        &self.statement_vars[&id]
    }
}

fn count_expression_vars(
    ir: &Ir,
    expressions: impl IntoIterator<Item = ExprId>,
    counts: &mut JHashMap<i32, usize>,
) {
    let mut descendants = Vec::new();
    for expr in expressions {
        Expr::append_exprents(ir, expr, true, &mut descendants);
        descendants.push(expr);
        for expr in descendants.drain(..) {
            if let Some(variable) = Expr::variable(ir, expr) {
                counts.insert(variable.index, 2);
            }
        }
    }
}

/// Return the statement where a declaration should be placed if the loop
/// header did not define it.
fn place_in_loop_header(ir: &mut Ir, stat: StatId, index: i32) -> Option<StatId> {
    let StatementKind::Do(header) = ir[stat].kind else {
        return Some(stat);
    };
    match header.ty {
        LoopType::For => {
            let init = header.init(ir);
            if let Some(variable) = init.and_then(|init| assigned_variable(ir, init, index)) {
                mark_definition(ir, variable);
                return None;
            }
            let condition = header.condition(ir).expect("Missing loop condition");
            let increment = header.increment(ir).expect("Missing loop increment");
            if [condition, increment]
                .into_iter()
                .any(|expr| Expr::contains_var_index(ir, expr, index))
            {
                return Some(ir[stat].parent.expect("Missing loop parent"));
            }
        }
        LoopType::ForEach => {
            if let Some(init) = header.init(ir)
                && Expr::variable(ir, init).is_some_and(|var| var.index == index)
            {
                mark_definition(ir, init);
                return None;
            }
        }
        _ => {}
    }
    Some(stat)
}

fn assigned_variable(ir: &Ir, expr: ExprId, index: i32) -> Option<ExprId> {
    let (left, _) = ir[expr].as_assignment()?;
    Expr::variable(ir, left)
        .is_some_and(|variable| variable.index == index)
        .then_some(left)
}

fn mark_definition(ir: &mut Ir, expr: ExprId) {
    let ExprKind::Variable(variable) = &mut ir[expr].kind else {
        unreachable!("Expected a variable definition");
    };
    variable.definition = true;
}

fn find_statement_lvt(ir: &Ir, stat: StatId, index: i32) -> Option<&Arc<LocalVariable>> {
    if let Some(list) = ir[stat].exprents {
        return ir[list]
            .iter()
            .find_map(|&expr| find_expr_lvt(ir, expr, index));
    }
    ir[stat]
        .stats
        .iter()
        .find_map(|&child| find_statement_lvt(ir, child, index))
        .or_else(|| {
            stat.stat_exprents(ir)
                .into_iter()
                .find_map(|expr| find_expr_lvt(ir, expr, index))
        })
}

fn find_expr_lvt(ir: &Ir, expr: ExprId, index: i32) -> Option<&Arc<LocalVariable>> {
    Expr::children(ir, expr)
        .find_map(|child| find_expr_lvt(ir, child, index))
        .or_else(|| {
            Expr::variable(ir, expr)
                .filter(|variable| variable.index == index)
                .and_then(|variable| variable.lvt.as_ref())
        })
}
