// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use itertools::Itertools;
use vineflower_rs::decompiler::flow::flatten::build_direct_graph;
use vineflower_rs::decompiler::flow::{DirectEdgeType, DirectGraph, DirectId};
use vineflower_rs::decompiler::ir::{ExprId, ExprKind, Ir, StatId};
use vineflower_rs::decompiler::stats::StatementKind;
use vineflower_rs::structs::consts::ConstantValue;

pub fn snapshot(ir: &mut Ir, root: StatId) -> String {
    describe(ir, root, false)
}

pub fn enhanced(ir: &mut Ir, root: StatId) -> String {
    format!("graph={}", describe(ir, root, true))
}

fn describe(ir: &mut Ir, root: StatId, enhanced: bool) -> String {
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
    let mut lists = HashMap::new();
    let nodes = extras
        .clone()
        .chain(graph.order.iter().copied().skip(graph.extra_nodes.len()))
        .map(|id| {
            let entry = &graph[id];
            let list = enhanced.then(|| *lists.entry(entry.exprents).or_insert(entry.id.as_str()));
            node(ir, &graph, id, list)
        })
        .join(";");
    let mut snapshot = format!(
        "{}|{}|{branches}|{nodes}",
        graph[graph.first].id,
        extras.map(|id| &graph[id].id).join(","),
    );
    if enhanced {
        let destinations = super::structure_statements(ir, root)
            .filter(|&stat| matches!(ir[stat].kind, StatementKind::Do(_)))
            .map(|stat| {
                let id = |node: Option<DirectId>| node.map_or("-", |node| graph[node].id.as_str());
                format!(
                    "{}:{}/{}",
                    ir[stat].id,
                    id(graph.direct_node(stat)),
                    id(graph.continue_node(stat))
                )
            })
            .join(",");
        snapshot.push_str(&format!(";destinations={destinations}"));
    }
    snapshot
}

fn node(ir: &Ir, graph: &DirectGraph, id: DirectId, list: Option<&str>) -> String {
    let node = &graph[id];
    let edges = |ids: &[DirectId]| ids.iter().map(|&id| &graph[id].id).join(",");
    let mut expressions = ir[node.exprents].iter().map(|&expr| match list {
        Some(_) => ir[expr].id.to_string(),
        None => exprent(ir, expr),
    });
    let mut snapshot = format!(
        "{}/{}/{}/{}/{}/{}/{}/{}/{}/{}",
        node.id,
        ir[node.stat].id,
        node.block
            .map_or_else(|| "-".into(), |block| ir[block].id.to_string()),
        node.try_finally
            .map_or("-", |scope| graph[scope].id.as_str()),
        node.block
            .is_some_and(|block| ir[block].exprents == Some(node.exprents)),
        expressions.join(","),
        edges(node.successors(DirectEdgeType::Regular)),
        edges(node.predecessors(DirectEdgeType::Regular)),
        edges(node.successors(DirectEdgeType::Exception)),
        edges(node.predecessors(DirectEdgeType::Exception)),
    );
    if let Some(list) = list {
        let mut aliases = Vec::new();
        if ir[node.stat].exprents == Some(node.exprents) {
            aliases.push("body");
        }
        if let StatementKind::Do(loop_) = ir[node.stat].kind {
            for (slot, header) in [
                ("init", loop_.init),
                ("condition", loop_.condition),
                ("increment", loop_.increment),
            ] {
                if header == Some(node.exprents) {
                    aliases.push(slot);
                }
            }
        }
        if let StatementKind::Catch { resources, .. } = ir[node.stat].kind
            && resources == Some(node.exprents)
        {
            aliases.push("resources");
        }
        snapshot.push_str(&format!("/{list}/{}", aliases.join(",")));
    }
    snapshot
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
        ExprKind::Variable(variable) => (
            format!("var={}", variable.index),
            variable.var_type.as_ref().unwrap(),
        ),
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
