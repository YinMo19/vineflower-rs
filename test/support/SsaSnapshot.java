import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.modules.decompiler.StackVarsProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SFormsConstructor;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SSAConstructorSparseEx;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SSAUConstructorSparseEx;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SimpleSSAReassign;
import org.jetbrains.java.decompiler.modules.decompiler.stats.BasicBlockStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionNode;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.util.collections.SFormsFastMapDirect;

class SsaSnapshot {
  private static final Comparator<VarVersionPair> VERSIONS =
    Comparator.comparingInt((VarVersionPair pair) -> pair.var).thenComparingInt(pair -> pair.version);
  private static final Field READ_COUNTS = readCountsField();

  static String run(RootStatement root, StructMethod method, CounterContainer counters) {
    SSAConstructorSparseEx ssa = new SSAConstructorSparseEx();
    String split;
    try {
      ssa.splitVariables(root, method);
      split = "split=" + counters(counters) + ";" + variables(root)
        + entries("phi", ssa.getPhi(), SsaSnapshot::versions)
        + entries("rev", ssa.getSimpleReversePhiLookup(), Object::toString)
        + entries("read", readCounts(ssa), Object::toString);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return "split-" + StructureReference.failureSnapshot(failure);
    }

    String reassigned;
    try {
      Map<Instruction, Integer> rewrites = SimpleSSAReassign.reassignSSAForm(ssa, root);
      reassigned = "reassigned=" + counters(counters) + ";" + variables(root) + rewrites(root, rewrites);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return split + "\treassign-" + StructureReference.failureSnapshot(failure);
    }

    String reset;
    try {
      StackVarsProcessor.setVersionsToNull(root);
      reset = "reset=" + counters(counters) + ";" + variables(root);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return split + "\t" + reassigned + "\treset-" + StructureReference.failureSnapshot(failure);
    }
    return split + "\t" + reassigned + "\t" + reset + "\t" + runSsau(root, method, counters);
  }

  private static String runSsau(RootStatement root, StructMethod method, CounterContainer counters) {
    SSAUConstructorSparseEx ssau = new SSAUConstructorSparseEx();
    String split;
    try {
      ssau.splitVariables(root, method);
      split = "ssau=" + counters(counters) + ";" + variables(root)
        + graph(ssau)
        + entries("assign", ssau.getVarAssignmentMap(), SsaSnapshot::pair)
        + entries("range", ssau.getMapVersionFirstRange(), Object::toString)
        + ssau.getMapFieldVars().entrySet().stream().sorted(Map.Entry.comparingByKey())
           .map(entry -> "field" + entry.getKey() + "=" + entry.getValue() + ";").collect(Collectors.joining())
        + entries("read", readCounts(ssau), Object::toString);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return "ssau-" + StructureReference.failureSnapshot(failure);
    }
    try {
      StackVarsProcessor.setVersionsToNull(root);
      return split + "\tssau-reset=" + counters(counters) + ";" + variables(root);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return split + "\tssau-reset-" + StructureReference.failureSnapshot(failure);
    }
  }

  private static String graph(SSAUConstructorSparseEx ssau) {
    StringBuilder graph = new StringBuilder();
    for (VarVersionNode node : ssau.getSsuVersions().nodes) {
      graph.append("node").append(pair(node.asPair())).append('=')
        .append(node.state == null ? "~" : node.state.name()).append('|')
        .append(edges(node.predecessors)).append('|').append(edges(node.successors)).append('|')
        .append(link(node.phantomNode)).append('|').append(link(node.phantomParentNode)).append('|')
        .append(live(node.live)).append(';');
    }
    return graph.toString();
  }

  private static String edges(Set<VarVersionNode> edges) {
    return edges.stream().map(VarVersionNode::asPair).sorted(VERSIONS).map(SsaSnapshot::pair)
      .collect(Collectors.joining(","));
  }

  private static String link(VarVersionNode node) {
    return node == null ? "~" : pair(node.asPair());
  }

  private static String pair(VarVersionPair pair) {
    return pair.var + ":" + pair.version;
  }

  private static String live(SFormsFastMapDirect live) {
    return live == null ? "~" : live.entryList().stream()
      .map(entry -> entry.getKey() + ":" + versions(entry.getValue())).collect(Collectors.joining("/"));
  }

  private static String counters(CounterContainer counters) {
    return counters.getCounter(CounterContainer.STATEMENT_COUNTER) + ","
      + counters.getCounter(CounterContainer.EXPRESSION_COUNTER) + ","
      + counters.getCounter(CounterContainer.VAR_COUNTER);
  }

  private static String variables(RootStatement root) {
    Map<Integer, VarExprent> vars = new TreeMap<>();
    for (Statement stat : statements(root)) {
      addVariables(vars, stat.getExprents());
      addVariables(vars, stat.getStatExprents());
      addVariables(vars, stat.getVarDefinitions());
      if (stat instanceof CatchAllStatement caught) {
        addVariables(vars, caught.getVars());
        if (caught.getMonitor() != null) {
          addVariables(vars, List.of(caught.getMonitor()));
        }
      } else if (stat instanceof SwitchStatement branch) {
        for (List<Exprent> cases : branch.getCaseValues()) {
          addVariables(vars, cases);
        }
      }
    }
    return vars.values().stream().map(var -> "v" + var.id + "=" + var.getIndex() + ":" + var.getVersion() + ";")
      .collect(Collectors.joining());
  }

  private static void addVariables(Map<Integer, VarExprent> vars, List<? extends Exprent> expressions) {
    if (expressions == null) {
      return;
    }
    for (Exprent expression : expressions) {
      if (expression == null) {
        continue;
      }
      for (Exprent child : expression.getAllExprents(true, true)) {
        if (child instanceof VarExprent var) {
          VarExprent previous = vars.putIfAbsent(var.id, var);
          if (previous != null && previous != var) {
            throw new AssertionError("duplicate variable expression ID " + var.id);
          }
        }
      }
    }
  }

  private static String rewrites(RootStatement root, Map<Instruction, Integer> rewrites) {
    // Multiple block positions can refer to one Instruction.
    Set<Instruction> located = Collections.newSetFromMap(new IdentityHashMap<>());
    StringJoiner positions = new StringJoiner(";", "", ";").setEmptyValue("");
    List<Statement> statements = statements(root);
    statements.sort(Comparator.comparingInt(stat -> stat.id));
    for (Statement stat : statements) {
      if (stat instanceof BasicBlockStatement block) {
        var seq = block.getBlock().getSeq();
        for (int offset = 0; offset < seq.length(); offset++) {
          Instruction instruction = seq.getInstr(offset);
          Integer index = rewrites.get(instruction);
          if (index != null) {
            located.add(instruction);
            positions.add("i" + stat.id + ":" + offset + "=" + index);
          }
        }
      }
    }
    if (located.size() != rewrites.size()) {
      throw new AssertionError("rewrite points to an instruction outside the statement tree");
    }
    return positions.toString();
  }

  private static List<Statement> statements(RootStatement root) {
    ArrayDeque<Statement> pending = new ArrayDeque<>();
    pending.add(root);
    pending.add(root.getDummyExit());
    List<Statement> statements = new ArrayList<>();
    while (!pending.isEmpty()) {
      Statement stat = pending.removeFirst();
      statements.add(stat);
      pending.addAll(stat.getStats());
    }
    return statements;
  }

  private static <V> String entries(String prefix, Map<VarVersionPair, V> map, Function<V, String> value) {
    return map.entrySet().stream().sorted(Map.Entry.comparingByKey(VERSIONS))
      .map(entry -> prefix + entry.getKey().var + ":" + entry.getKey().version + "=" + value.apply(entry.getValue()) + ";")
      .collect(Collectors.joining());
  }

  private static String versions(Iterable<Integer> versions) {
    List<Integer> sorted = new ArrayList<>();
    versions.forEach(sorted::add);
    sorted.sort(Integer::compare);
    return sorted.stream().map(Object::toString).collect(Collectors.joining(","));
  }

  private static Field readCountsField() {
    try {
      Field field = SFormsConstructor.class.getDeclaredField("readCount");
      field.setAccessible(true);
      return field;
    } catch (ReflectiveOperationException failure) {
      throw new AssertionError(failure);
    }
  }

  @SuppressWarnings("unchecked")
  private static Map<VarVersionPair, Integer> readCounts(SFormsConstructor ssa) {
    try {
      return (Map<VarVersionPair, Integer>) READ_COUNTS.get(ssa);
    } catch (IllegalAccessException failure) {
      throw new AssertionError(failure);
    }
  }
}
