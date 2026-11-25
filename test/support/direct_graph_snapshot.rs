// SPDX-License-Identifier: Apache-2.0

use itertools::Itertools;
use vineflower_rs::decompiler::flow::flatten::build_direct_graph;
use vineflower_rs::decompiler::flow::{DirectEdgeType, DirectGraph, DirectId};
use vineflower_rs::decompiler::ir::{ExprId, ExprKind, Ir, StatId};
use vineflower_rs::structs::consts::ConstantValue;

pub fn snapshot(ir: &mut Ir, root: StatId) -> String {
    let graph = build_direct_graph(ir, root);
    // Java hashes extra nodes using their type's enum identity. Compare extra
    // node membership separately, then preserve the reachable reverse postorder.
    let extras = graph
        .extra_nodes
        .iter()
        .copied()
        .sorted_by_key(|&id| &graph[id].id);
    let branches = graph
        .neg_if_branch
        .iter()
        .map(|(&src, &dst)| (&graph[src].id, &graph[dst].id))
        .sorted()
        .map(|(src, dst)| format!("{src}>{dst}"))
        .join(",");
    let nodes = extras
        .clone()
        .chain(graph.order.iter().copied().skip(graph.extra_nodes.len()))
        .map(|id| node(ir, &graph, id))
        .join(";");
    format!(
        "{}|{}|{branches}|{nodes}",
        graph[graph.first].id,
        extras.map(|id| &graph[id].id).join(","),
    )
}

fn node(ir: &Ir, graph: &DirectGraph, id: DirectId) -> String {
    let node = &graph[id];
    let edges = |ids: &[DirectId]| ids.iter().map(|&id| &graph[id].id).join(",");
    format!(
        "{}/{}/{}/{}/{}/{}/{}/{}/{}/{}",
        node.id,
        ir[node.stat].id,
        node.block
            .map_or_else(|| "-".into(), |block| ir[block].id.to_string()),
        node.try_finally
            .map_or("-", |scope| graph[scope].id.as_str()),
        node.block
            .is_some_and(|block| ir[block].exprents == Some(node.exprents)),
        ir[node.exprents]
            .iter()
            .map(|&expr| exprent(ir, expr))
            .join(","),
        edges(node.successors(DirectEdgeType::Regular)),
        edges(node.predecessors(DirectEdgeType::Regular)),
        edges(node.successors(DirectEdgeType::Exception)),
        edges(node.predecessors(DirectEdgeType::Exception)),
    )
}

fn exprent(ir: &Ir, expr: ExprId) -> String {
    let expr = &ir[expr];
    let (kind, ty) = match &expr.kind {
        ExprKind::Constant {
            value: ConstantValue::Integer(value),
            bool_permitted,
            var_type,
            ..
        } => (format!("const={value}:{bool_permitted}"), var_type),
        ExprKind::Variable(variable) => (format!("var={}", variable.index), &variable.var_type),
        _ => unreachable!("Direct graph snapshot runs before expression lifting"),
    };
    format!(
        "{}:{}:{}:{}:{kind}",
        expr.id,
        ty.ty.ordinal(),
        ty.array_dim,
        ty.value.as_deref().unwrap_or("null"),
    )
}
