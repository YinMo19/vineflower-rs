// SPDX-License-Identifier: Apache-2.0

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectEdgeType;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectGraph;
import org.jetbrains.java.decompiler.modules.decompiler.flow.DirectNode;
import org.jetbrains.java.decompiler.modules.decompiler.flow.FlattenStatementsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.struct.gen.VarType;

class DirectGraphSnapshot {
  static String snapshot(RootStatement root) {
    DirectGraph graph = FlattenStatementsHelper.build(root);
    List<DirectNode> extras = new ArrayList<>(graph.extraNodes);
    extras.sort(Comparator.comparing(node -> node.id));
    List<DirectNode> order = new ArrayList<>(extras);
    order.addAll(graph.nodes.subList(extras.size(), graph.nodes.size()));

    String extraIds = extras.stream().map(node -> node.id).collect(Collectors.joining(","));
    String branches = graph.mapNegIfBranch.entrySet().stream().sorted(Map.Entry.comparingByKey())
      .map(branch -> branch.getKey() + ">" + branch.getValue()).collect(Collectors.joining(","));
    String nodes = order.stream().map(DirectGraphSnapshot::node).collect(Collectors.joining(";"));
    return graph.first.id + "|" + extraIds + "|" + branches + "|" + nodes;
  }

  private static String node(DirectNode node) {
    List<String> fields = new ArrayList<>(10);
    fields.add(node.id);
    fields.add(Integer.toString(node.statement.id));
    fields.add(node.block == null ? "-" : Integer.toString(node.block.id));
    fields.add(node.tryFinally == null ? "-" : node.tryFinally.id);
    fields.add(Boolean.toString(node.block != null && node.block.getExprents() == node.exprents));
    fields.add(node.exprents.stream().map(DirectGraphSnapshot::exprent).collect(Collectors.joining(",")));
    for (DirectEdgeType kind : DirectEdgeType.TYPES) {
      fields.add(node.getSuccessors(kind).stream().map(edge -> edge.getDestination().id).collect(Collectors.joining(",")));
      fields.add(node.getPredecessors(kind).stream().map(edge -> edge.getSource().id).collect(Collectors.joining(",")));
    }
    return String.join("/", fields);
  }

  private static String exprent(Exprent expr) {
    VarType type = expr.getExprType();
    String prefix = expr.id + ":" + type.type.ordinal() + ":" + type.arrayDim + ":" + type.value + ":";
    if (expr instanceof ConstExprent constant) {
      return prefix + "const=" + constant.getValue() + ":" + constant.isBoolPermitted();
    }
    if (expr instanceof VarExprent var) {
      return prefix + "var=" + var.getIndex();
    }
    throw new IllegalStateException("Unexpected expression in the direct graph: " + expr.type);
  }
}
