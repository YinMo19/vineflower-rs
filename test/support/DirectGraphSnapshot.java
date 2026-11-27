import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
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
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.struct.gen.VarType;

class DirectGraphSnapshot {
  static String snapshot(RootStatement root) {
    return snapshot(FlattenStatementsHelper.build(root), null);
  }

  static String enhanced(RootStatement root) {
    var flattener = new FlattenStatementsHelper();
    DirectGraph graph = flattener.buildDirectGraph(root);
    var starts = destinations(flattener, "mapRegularDestinationNodes");
    var continues = destinations(flattener, "mapContinueDestinationNodes");
    String loops = StructureReference.statements(root).stream().filter(DoStatement.class::isInstance)
      .map(loop -> loop.id + ":" + nodeId((DirectNode) starts.get(loop))
        + "/" + nodeId((DirectNode) continues.get(loop))).collect(Collectors.joining(","));
    return "graph=" + snapshot(graph, new IdentityHashMap<>()) + ";destinations=" + loops;
  }

  private static Map<?, ?> destinations(FlattenStatementsHelper helper, String name) {
    try {
      var field = FlattenStatementsHelper.class.getDeclaredField(name);
      field.setAccessible(true);
      return (Map<?, ?>) field.get(helper);
    } catch (ReflectiveOperationException error) {
      throw new AssertionError(error);
    }
  }

  private static String nodeId(DirectNode node) {
    return node == null ? "-" : node.id;
  }

  private static String snapshot(DirectGraph graph, Map<List<Exprent>, String> lists) {
    List<DirectNode> extras = new ArrayList<>(graph.extraNodes);
    extras.sort(Comparator.comparing(node -> node.id));
    List<DirectNode> order = new ArrayList<>(extras);
    order.addAll(graph.nodes.subList(extras.size(), graph.nodes.size()));

    String extraIds = extras.stream().map(node -> node.id).collect(Collectors.joining(","));
    String branches = graph.mapNegIfBranch.entrySet().stream().sorted(Map.Entry.comparingByKey())
      .map(branch -> branch.getKey() + ">" + branch.getValue()).collect(Collectors.joining(","));
    String nodes = order.stream().map(node -> node(node, lists)).collect(Collectors.joining(";"));
    return graph.first.id + "|" + extraIds + "|" + branches + "|" + nodes;
  }

  private static String node(DirectNode node, Map<List<Exprent>, String> lists) {
    List<String> fields = new ArrayList<>(12);
    fields.add(node.id);
    fields.add(Integer.toString(node.statement.id));
    fields.add(node.block == null ? "-" : Integer.toString(node.block.id));
    fields.add(nodeId(node.tryFinally));
    fields.add(Boolean.toString(node.block != null && node.block.getExprents() == node.exprents));
    fields.add(node.exprents.stream().map(expr -> lists == null ? exprent(expr)
      : expr == null ? "~" : Integer.toString(expr.id)).collect(Collectors.joining(",")));
    for (DirectEdgeType kind : DirectEdgeType.TYPES) {
      fields.add(node.getSuccessors(kind).stream().map(edge -> edge.getDestination().id).collect(Collectors.joining(",")));
      fields.add(node.getPredecessors(kind).stream().map(edge -> edge.getSource().id).collect(Collectors.joining(",")));
    }
    if (lists != null) {
      fields.add(lists.computeIfAbsent(node.exprents, ignored -> node.id));
      List<String> aliases = new ArrayList<>();
      if (node.exprents == node.statement.getExprents()) {
        aliases.add("body");
      }
      if (node.statement instanceof DoStatement loop) {
        if (node.exprents == loop.getInitExprentList()) {
          aliases.add("init");
        }
        if (node.exprents == loop.getConditionExprentList()) {
          aliases.add("condition");
        }
        if (node.exprents == loop.getIncExprentList()) {
          aliases.add("increment");
        }
      }
      if (node.statement instanceof CatchStatement caught && node.exprents == caught.getResources()) {
        aliases.add("resources");
      }
      fields.add(String.join(",", aliases));
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
