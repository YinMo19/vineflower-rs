// SPDX-License-Identifier: Apache-2.0

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.code.cfg.ControlFlowGraph;
import org.jetbrains.java.decompiler.code.cfg.ExceptionRangeCFG;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.DomHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.DoStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.IfStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SynchronizedStatement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

class StructureReference {
  private static final Field SUBROUTINES = subroutinesField();

  private record Options(boolean forceJsr, boolean useLvtNames, boolean complexCondy, boolean decompileFinally) { }

  public static void main(String[] args) throws IOException {
    new Fernflower(null, Map.of(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0"), IFernflowerLogger.NO_OP);
    try (var input = new DataInputStream(new BufferedInputStream(Files.newInputStream(Path.of(args[0]))))) {
      int phase = input.readUnsignedByte();
      StackSnapshot.Check stackCheck = switch (phase) {
        case 3 -> StackSnapshot.Check.STACK;
        case 4 -> StackSnapshot.Check.INCREMENTS;
        case 5 -> StackSnapshot.Check.PRE_MAIN;
        case 6 -> StackSnapshot.Check.LOOP_ELIMINATION;
        case 7 -> StackSnapshot.Check.LOOP_ENHANCEMENT;
        case 8 -> StackSnapshot.Check.LOOP_MERGE;
        case 9 -> StackSnapshot.Check.MAIN_LOOP_LABELS;
        case 10 -> StackSnapshot.Check.SECONDARY_FUNCTIONS;
        case 11 -> StackSnapshot.Check.PATTERN_MATCHING_ENTRY;
        case 12 -> StackSnapshot.Check.IF_PATTERNS;
        case 13 -> StackSnapshot.Check.SWITCH_ENTRY;
        case 14 -> StackSnapshot.Check.SWITCH_PASSES;
        case 15 -> StackSnapshot.Check.TRY_ENTRY;
        case 16 -> StackSnapshot.Check.TRY_RESOURCES;
        case 17 -> StackSnapshot.Check.INLINE_BLOCKS;
        case 18 -> StackSnapshot.Check.LATE_LOOP_PASSES;
        case 19 -> StackSnapshot.Check.EXIT_ENTRY;
        case 20 -> StackSnapshot.Check.EXIT_CONDENSATION;
        case 21 -> StackSnapshot.Check.MAIN_LOOP_END;
        case 22 -> StackSnapshot.Check.POST_SWITCHES;
        case 23 -> StackSnapshot.Check.AFTER_MAIN;
        case 24 -> StackSnapshot.Check.VARIABLE_DEFINITIONS;
        case 25 -> StackSnapshot.Check.METHOD_END;
        default -> null;
      };
      StackSnapshot.Context stackContext = stackCheck == null ? null
        : new StackSnapshot.Context(readStackGroups(input), stackCheck);
      Path previousPath = null;
      Options previousOptions = null;
      StructClass currentClass = null;
      for (int index = input.readInt(); index >= 0; index = input.readInt()) {
        Path classPath = Path.of(readText(input));
        String name = readText(input);
        String descriptor = readText(input);
        Options options = new Options(input.readBoolean(), input.readBoolean(), input.readBoolean(), input.readBoolean());
        if (stackContext != null) {
          int group = input.readInt();
          boolean simplify = input.readBoolean();
          boolean ternary = input.readBoolean();
          boolean booleanAsInt = input.readBoolean();
          boolean assertions = input.readBoolean();
          boolean ternaryConstants = stackCheck == StackSnapshot.Check.SECONDARY_FUNCTIONS && input.readBoolean();
          String classname = readText(input);
          var stackOptions = new StackSnapshot.Options(group, simplify, ternary, options.useLvtNames(),
            booleanAsInt, assertions, ternaryConstants);
          String snapshot = stackContext.run(input, stackOptions, classname, name, descriptor);
          System.out.println(index + "\t" + snapshot);
          continue;
        }
        if (!classPath.equals(previousPath) || !options.equals(previousOptions)) {
          DecompilerContext.setProperty(IFernflowerPreferences.FORCE_JSR_INLINE, flag(options.forceJsr()));
          DecompilerContext.setProperty(IFernflowerPreferences.USE_DEBUG_VAR_NAMES, flag(options.useLvtNames()));
          DecompilerContext.setProperty(IFernflowerPreferences.DECOMPILE_COMPLEX_CONDYS, flag(options.complexCondy()));
          DecompilerContext.setProperty(IFernflowerPreferences.FINALLY_DEINLINE, flag(options.decompileFinally()));
          currentClass = StructClass.create(new DataInputFullStream(Files.readAllBytes(classPath)), true);
          DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS, currentClass);
          DecompilerContext.startClass(new ImportCollector(new ClassNode(ClassNode.Type.ROOT, currentClass)));
          previousPath = classPath;
          previousOptions = options;
        }

        StructMethod method = Objects.requireNonNull(currentClass.getMethod(name, descriptor));
        MethodDescriptor methodDescriptor = MethodDescriptor.parseDescriptor(method, null);
        VarProcessor varProcessor = new VarProcessor(method, methodDescriptor);
        DecompilerContext.startMethod(varProcessor);
        method.expandData(currentClass);
        try {
          CounterContainer counters = DecompilerContext.getCounterContainer();
          counters.setCounter(CounterContainer.VAR_COUNTER, method.getLocalVariables());
          ControlFlowGraph graph = readGraph(input, method);
          String snapshot;
          try {
            RootStatement root = DomHelper.parseGraph(graph, method, 0);
            snapshot = switch (phase) {
              case 0 -> snapshot(root, counters) + "\t" + directSnapshot(root) + "\t"
                + lift(root, currentClass, method, methodDescriptor, varProcessor, counters, false);
              case 1 -> lift(root, currentClass, method, methodDescriptor, varProcessor, counters, true);
              case 2 -> FinallySnapshot.run(graph, root, currentClass, method, methodDescriptor,
                varProcessor, counters, tree -> snapshot(tree, counters));
              default -> throw new IllegalArgumentException("unknown parity phase " + phase);
            };
          } catch (RuntimeException | AssertionError | StackOverflowError failure) {
            if (failure.getClass() == RuntimeException.class && "parsing failure!".equals(failure.getMessage())) {
              snapshot = "rejected=parsing failure!";
            } else {
              snapshot = "structure-" + failureSnapshot(failure);
            }
          }
          System.out.println(index + "\t" + snapshot);
        } finally {
          method.releaseResources();
        }
      }
    }
  }

  private static List<List<String>> readStackGroups(DataInputStream input) throws IOException {
    int count = input.readInt();
    var groups = new ArrayList<List<String>>(count);
    for (int i = 0; i < count; i++) {
      groups.add(readTexts(input));
    }
    return groups;
  }

  private static String lift(RootStatement root, StructClass cl, StructMethod method, MethodDescriptor descriptor,
                             VarProcessor vars, CounterContainer counters, boolean checkSsa) {
    try {
      new ExprProcessor(descriptor, vars).processStatement(root, cl);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return "lift-" + failureSnapshot(failure);
    }
    return checkSsa ? SsaSnapshot.run(root, method, counters) : ExpressionSnapshot.snapshot(root, counters);
  }

  private static String flag(boolean value) {
    return value ? "1" : "0";
  }

  private static String directSnapshot(RootStatement root) {
    try {
      return "graph=" + DirectGraphSnapshot.snapshot(root);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return failureSnapshot(failure);
    }
  }

  static String failureSnapshot(Throwable failure) {
    return "error=" + failure.toString().replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
  }

  private record PendingBlock(BasicBlock block, int[] successors, int[] handlers, int[] predecessors, int[] throwers) { }

  // Reuse the real method and decoded bytecode as context. Both implementations
  // receive the same prepared graph, including synthetic handler blocks and IDs.
  static ControlFlowGraph readGraph(DataInputStream input, StructMethod method) throws IOException {
    FullInstructionSequence sequence = method.getInstructionSequence();
    ControlFlowGraph graph = new ControlFlowGraph(sequence);
    graph.getBlocks().clear();
    graph.getExceptions().clear();
    graph.getFinallyExits().clear();
    BasicBlock exit = graph.getLast();
    exit.getPreds().clear();

    int firstId = input.readInt();
    int exitId = input.readInt();
    if (exit.id != exitId) {
      throw new IllegalStateException("mismatched dummy CFG exit: " + exit.id + " vs " + exitId);
    }
    graph.last_id = input.readInt();
    int[] exitPredecessors = readInts(input);
    int[] exitThrowers = readInts(input);
    graph.addErrorComment = input.readBoolean();
    List<String> comments = readTexts(input);
    if (!comments.isEmpty()) {
      graph.commentLines = new LinkedHashSet<>(comments);
    }

    Map<Integer, BasicBlock> blocks = new HashMap<>();
    List<Instruction> instructions = new ArrayList<>();
    blocks.put(exitId, exit);
    int blockCount = input.readInt();
    List<PendingBlock> pending = new ArrayList<>(blockCount);
    for (int i = 0; i < blockCount; i++) {
      BasicBlock block = new BasicBlock(input.readInt());
      if (blocks.put(block.id, block) != null) {
        throw new IllegalStateException("duplicate CFG block ID " + block.id);
      }
      graph.getBlocks().addWithKey(block, block.id);
      for (int offset : readInts(input)) {
        block.getInstrOldOffsets().add(offset);
      }
      pending.add(new PendingBlock(block, readInts(input), readInts(input), readInts(input), readInts(input)));
      int length = input.readInt();
      for (int j = 0; j < length; j++) {
        int identity = input.readInt();
        if (identity == instructions.size()) {
          int original = input.readInt();
          Instruction instruction;
          if (original >= 0) {
            instruction = sequence.getInstr(original);
          } else {
            int opcode = input.readInt();
            boolean wide = input.readBoolean();
            int group = input.readInt();
            int offset = input.readInt();
            int size = input.readInt();
            int[] operands = readInts(input);
            instruction = Instruction.create(
              opcode, wide, group, method.getBytecodeVersion(), operands, offset, size);
            instruction.initInstruction(sequence);
          }
          instructions.add(instruction);
        }
        block.getSeq().addInstruction(instructions.get(identity));
      }
    }

    graph.setFirst(blocks.get(firstId));
    for (PendingBlock entry : pending) {
      addBlocks(entry.block().getSuccs(), entry.successors(), blocks);
      addBlocks(entry.block().getSuccExceptions(), entry.handlers(), blocks);
      addBlocks(entry.block().getPreds(), entry.predecessors(), blocks);
      addBlocks(entry.block().getPredExceptions(), entry.throwers(), blocks);
    }
    exit.getPredExceptions().clear();
    addBlocks(exit.getPreds(), exitPredecessors, blocks);
    addBlocks(exit.getPredExceptions(), exitThrowers, blocks);

    int rangeCount = input.readInt();
    for (int i = 0; i < rangeCount; i++) {
      BasicBlock handler = blocks.get(input.readInt());
      List<BasicBlock> protectedBlocks = new ArrayList<>();
      addBlocks(protectedBlocks, readInts(input), blocks);
      List<String> types = input.readBoolean() ? readTexts(input) : null;
      graph.getExceptions().add(new ExceptionRangeCFG(protectedBlocks, handler, types));
    }
    for (int finallyExit : readInts(input)) {
      graph.getFinallyExits().add(blocks.get(finallyExit));
    }
    Map<BasicBlock, BasicBlock> subroutines = subroutines(graph);
    subroutines.clear();
    int count = input.readInt();
    for (int i = 0; i < count; i++) {
      subroutines.put(Objects.requireNonNull(blocks.get(input.readInt())),
        Objects.requireNonNull(blocks.get(input.readInt())));
    }
    return graph;
  }

  private static void addBlocks(List<BasicBlock> dest, int[] ids, Map<Integer, BasicBlock> blocks) {
    for (int id : ids) {
      dest.add(Objects.requireNonNull(blocks.get(id)));
    }
  }

  private static Field subroutinesField() {
    try {
      Field field = ControlFlowGraph.class.getDeclaredField("subroutines");
      field.setAccessible(true);
      return field;
    } catch (ReflectiveOperationException failure) {
      throw new AssertionError(failure);
    }
  }

  @SuppressWarnings("unchecked")
  static Map<BasicBlock, BasicBlock> subroutines(ControlFlowGraph graph) {
    try {
      return (Map<BasicBlock, BasicBlock>) SUBROUTINES.get(graph);
    } catch (IllegalAccessException failure) {
      throw new AssertionError(failure);
    }
  }

  private static int[] readInts(DataInputStream input) throws IOException {
    int[] values = new int[input.readInt()];
    for (int i = 0; i < values.length; i++) {
      values[i] = input.readInt();
    }
    return values;
  }

  private static List<String> readTexts(DataInputStream input) throws IOException {
    int length = input.readInt();
    List<String> texts = new ArrayList<>(length);
    for (int i = 0; i < length; i++) {
      texts.add(readText(input));
    }
    return texts;
  }

  private static String readText(DataInputStream input) throws IOException {
    byte[] bytes = new byte[input.readInt()];
    input.readFully(bytes);
    return new String(bytes, StandardCharsets.UTF_8);
  }

  private static String snapshot(RootStatement root, CounterContainer counters) {
    return snapshot(root, counters, false, false);
  }

  static String snapshot(RootStatement root, CounterContainer counters, boolean loopStage, boolean switchStage) {
    List<String> fields = new ArrayList<>();
    fields.add("counters=" + counters.getCounter(CounterContainer.STATEMENT_COUNTER)
      + "," + counters.getCounter(CounterContainer.EXPRESSION_COUNTER)
      + "," + counters.getCounter(CounterContainer.VAR_COUNTER));
    fields.add("error=" + root.addErrorComment);
    fields.add("comments=" + (root.commentLines == null ? "" : String.join("|", root.commentLines)));

    for (Statement statement : statements(root)) {
      fields.add("stat=" + statement.id + ":" + statement.type.name());
      fields.add("tree=" + statementId(statement.getParent()) + "/" + statementId(statement.getFirst())
        + "/" + statementId(statement.getPost()) + "/"
        + statement.getStats().stream().map(StructureReference::statementId).collect(Collectors.joining(",")));
      fields.add("flags=" + statement.getLastBasicType().name() + "/" + statement.isMonitorEnter()
        + "/" + statement.containsMonitorExitOrAthrow() + "/" + statement.containsMonitorExit() + "/" + statement.isCopied());
      if (switchStage) {
        fields.add("phantom=" + statement.isPhantom());
      }
      fields.add("out=" + edges(statement.getAllSuccessorEdges()));
      if (loopStage) {
        fields.add("in=" + edges(statement.getAllPredecessorEdges()));
      }
      fields.add("labels=" + statement.getLabelEdges().stream().map(StructureReference::edgeId)
        .sorted().collect(Collectors.joining("|")));

      if (statement instanceof IfStatement branch) {
        fields.add("if=" + (branch.iftype == IfStatement.IFTYPE_IFELSE) + "/" + branch.isNegated()
          + "/" + statementId(branch.getIfstat()) + "/" + statementId(branch.getElsestat())
          + "/" + edgeId(branch.getIfEdge()) + "/" + edgeId(branch.getElseEdge()));
      } else if (statement instanceof SwitchStatement branch) {
        List<String> cases = new ArrayList<>();
        for (int i = 0; i < branch.getCaseStatements().size(); i++) {
          var edges = branch.getCaseEdges().get(i).stream().map(edge -> switchEdge(edge, switchStage))
            .collect(Collectors.joining("|"));
          var values = branch.getCaseValues().get(i).stream()
            .map(expr -> switchStage ? expr == null ? "-" : Integer.toString(expr.id) : expression(expr))
            .collect(Collectors.joining("|"));
          cases.add(statementId(branch.getCaseStatements().get(i)) + ":" + edges + ":" + values);
        }
        fields.add("switch=" + switchEdge(branch.getDefaultEdge(), switchStage) + "/" + String.join("/", cases));
      } else if (statement instanceof CatchStatement caught) {
        fields.add("catch=" + caught.getExctStrings().stream().map(types -> String.join(",", types))
          .collect(Collectors.joining("|")) + "/" + expressions(caught.getVars()));
      } else if (statement instanceof CatchAllStatement caught) {
        fields.add("catch-all=" + statementId(caught.getHandler()) + "/" + caught.isFinally()
          + "/" + expression(caught.getMonitor()) + "/" + expressions(caught.getVars()));
      } else if (statement instanceof SynchronizedStatement sync) {
        fields.add("monitor=" + statementId(sync.getBody()));
      } else if (loopStage && statement instanceof DoStatement loop) {
        fields.add("loop=" + loop.getLooptype());
      }
    }
    return String.join(";", fields);
  }

  private static String switchEdge(StatEdge edge, boolean includeAlias) {
    String description = edgeId(edge);
    if (includeAlias && edge != null) {
      int index = edge.getSource().getAllSuccessorEdges().indexOf(edge);
      return description + "@" + (index == -1 ? "-" : Integer.toString(index));
    }
    return description;
  }

  static List<Statement> statements(RootStatement root) {
    List<Statement> result = new ArrayList<>();
    Deque<Statement> pending = new ArrayDeque<>();
    pending.add(root);
    pending.add(root.getDummyExit());
    while (!pending.isEmpty()) {
      Statement statement = pending.removeFirst();
      result.add(statement);
      for (int i = statement.getStats().size() - 1; i >= 0; i--) {
        pending.addFirst(statement.getStats().get(i));
      }
    }
    return result;
  }

  static Map<StatEdge, String> edgeStates(RootStatement root) {
    Map<StatEdge, String> states = new IdentityHashMap<>();
    for (Statement statement : statements(root)) {
      for (StatEdge edge : statement.getAllSuccessorEdges()) {
        states.put(edge, edgeId(edge));
      }
    }
    return states;
  }

  private static String statementId(Statement statement) {
    return statement == null ? "-" : Integer.toString(statement.id);
  }

  private static String edges(List<StatEdge> edges) {
    return edges.stream().map(StructureReference::edgeId).collect(Collectors.joining("|"));
  }

  static String edgeId(StatEdge edge) {
    if (edge == null) {
      return "-";
    }
    return edge.getType() + "," + edge.getSource().id + "," + edge.getDestination().id
      + "," + statementId(edge.closure) + "," + edge.labeled + "," + edge.explicit
      + "," + edge.canInline + "," + edge.phantomContinue
      + "," + (edge.getExceptions() == null ? "*" : String.join(",", edge.getExceptions()));
  }

  private static String expressions(List<? extends Exprent> expressions) {
    return expressions.stream().map(StructureReference::expression).collect(Collectors.joining("|"));
  }

  private static String expression(Exprent expression) {
    if (expression == null) {
      return "-";
    }
    if (expression instanceof VarExprent variable) {
      return variable.id + "=" + variable.getIndex() + ":" + Objects.toString(variable.getExprType().value, "*");
    }
    ConstExprent constant = (ConstExprent) expression;
    return constant.id + "=" + constant.getIntValue();
  }
}
