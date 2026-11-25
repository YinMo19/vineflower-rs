// SPDX-License-Identifier: Apache-2.0

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
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
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.DomHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchAllStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.CatchStatement;
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
  private record Options(boolean forceJsr, boolean useLvtNames, boolean complexCondy) { }

  public static void main(String[] args) throws IOException {
    new Fernflower(null, Map.of(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0"), IFernflowerLogger.NO_OP);
    try (var input = new DataInputStream(new BufferedInputStream(Files.newInputStream(Path.of(args[0]))))) {
      Path previousPath = null;
      Options previousOptions = null;
      StructClass currentClass = null;
      for (int index = input.readInt(); index >= 0; index = input.readInt()) {
        Path classPath = Path.of(readText(input));
        String name = readText(input);
        String descriptor = readText(input);
        Options options = new Options(input.readBoolean(), input.readBoolean(), input.readBoolean());
        if (!classPath.equals(previousPath) || !options.equals(previousOptions)) {
          DecompilerContext.setProperty(IFernflowerPreferences.FORCE_JSR_INLINE, flag(options.forceJsr()));
          DecompilerContext.setProperty(IFernflowerPreferences.USE_DEBUG_VAR_NAMES, flag(options.useLvtNames()));
          DecompilerContext.setProperty(IFernflowerPreferences.DECOMPILE_COMPLEX_CONDYS, flag(options.complexCondy()));
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
            snapshot = snapshot(root, counters) + "\t" + directSnapshot(root)
              + "\t" + ExpressionSnapshot.lift(root, currentClass, methodDescriptor, varProcessor, counters);
          } catch (RuntimeException | AssertionError | StackOverflowError failure) {
            if (failure.getClass() == RuntimeException.class && "parsing failure!".equals(failure.getMessage())) {
              snapshot = "rejected=parsing failure!";
            } else {
              snapshot = failureSnapshot(failure);
            }
          }
          System.out.println(index + "\t" + snapshot);
        } finally {
          method.releaseResources();
        }
      }
    }
  }

  private static String flag(boolean value) {
    return value ? "1" : "0";
  }

  private static String directSnapshot(RootStatement root) {
    try {
      return DirectGraphSnapshot.snapshot(root);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return failureSnapshot(failure);
    }
  }

  private static String failureSnapshot(Throwable failure) {
    return "error=" + failure.toString().replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
  }

  private record PendingBlock(BasicBlock block, int[] successors, int[] handlers) { }

  // Reuse the real method and decoded bytecode as context. Both implementations
  // receive the same prepared graph, including synthetic handler blocks and IDs.
  private static ControlFlowGraph readGraph(DataInputStream input, StructMethod method) throws IOException {
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
    graph.addErrorComment = input.readBoolean();
    List<String> comments = readTexts(input);
    if (!comments.isEmpty()) {
      graph.commentLines = new LinkedHashSet<>(comments);
    }

    Map<Integer, BasicBlock> blocks = new HashMap<>();
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
      pending.add(new PendingBlock(block, readInts(input), readInts(input)));
      int length = input.readInt();
      for (int j = 0; j < length; j++) {
        int opcode = input.readInt();
        boolean wide = input.readBoolean();
        int group = input.readInt();
        int offset = input.readInt();
        int size = input.readInt();
        int[] operands = readInts(input);
        Instruction instruction = Instruction.create(
          opcode, wide, group, method.getBytecodeVersion(), operands, offset, size);
        instruction.initInstruction(sequence);
        block.getSeq().addInstruction(instruction);
      }
    }

    graph.setFirst(blocks.get(firstId));
    for (PendingBlock entry : pending) {
      for (int successor : entry.successors()) {
        entry.block().addSuccessor(blocks.get(successor));
      }
      for (int handler : entry.handlers()) {
        entry.block().addSuccessorException(blocks.get(handler));
      }
    }

    int rangeCount = input.readInt();
    for (int i = 0; i < rangeCount; i++) {
      BasicBlock handler = blocks.get(input.readInt());
      List<BasicBlock> protectedBlocks = Arrays.stream(readInts(input)).mapToObj(blocks::get).toList();
      List<String> types = input.readBoolean() ? readTexts(input) : null;
      graph.getExceptions().add(new ExceptionRangeCFG(protectedBlocks, handler, types));
    }
    for (int finallyExit : readInts(input)) {
      graph.getFinallyExits().add(blocks.get(finallyExit));
    }
    return graph;
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
    List<String> fields = new ArrayList<>();
    fields.add("counters=" + counters.getCounter(CounterContainer.STATEMENT_COUNTER)
      + "," + counters.getCounter(CounterContainer.EXPRESSION_COUNTER)
      + "," + counters.getCounter(CounterContainer.VAR_COUNTER));
    fields.add("error=" + root.addErrorComment);
    fields.add("comments=" + (root.commentLines == null ? "" : String.join("|", root.commentLines)));

    Deque<Statement> pending = new ArrayDeque<>();
    pending.add(root);
    pending.add(root.getDummyExit());
    while (!pending.isEmpty()) {
      Statement statement = pending.removeFirst();
      fields.add("stat=" + statement.id + ":" + statement.type.name());
      fields.add("tree=" + statementId(statement.getParent()) + "/" + statementId(statement.getFirst())
        + "/" + statementId(statement.getPost()) + "/"
        + statement.getStats().stream().map(StructureReference::statementId).collect(Collectors.joining(",")));
      fields.add("flags=" + statement.getLastBasicType().name() + "/" + statement.isMonitorEnter()
        + "/" + statement.containsMonitorExitOrAthrow() + "/" + statement.containsMonitorExit() + "/" + statement.isCopied());
      fields.add("out=" + edges(statement.getAllSuccessorEdges()));
      fields.add("labels=" + statement.getLabelEdges().stream().map(StructureReference::edgeId)
        .sorted().collect(Collectors.joining("|")));

      if (statement instanceof IfStatement branch) {
        fields.add("if=" + (branch.iftype == IfStatement.IFTYPE_IFELSE) + "/" + branch.isNegated()
          + "/" + statementId(branch.getIfstat()) + "/" + statementId(branch.getElsestat())
          + "/" + edgeId(branch.getIfEdge()) + "/" + edgeId(branch.getElseEdge()));
      } else if (statement instanceof SwitchStatement branch) {
        List<String> cases = new ArrayList<>();
        for (int i = 0; i < branch.getCaseStatements().size(); i++) {
          cases.add(statementId(branch.getCaseStatements().get(i)) + ":" + edges(branch.getCaseEdges().get(i))
            + ":" + expressions(branch.getCaseValues().get(i)));
        }
        fields.add("switch=" + edgeId(branch.getDefaultEdge()) + "/" + String.join("/", cases));
      } else if (statement instanceof CatchStatement caught) {
        fields.add("catch=" + caught.getExctStrings().stream().map(types -> String.join(",", types))
          .collect(Collectors.joining("|")) + "/" + expressions(caught.getVars()));
      } else if (statement instanceof CatchAllStatement caught) {
        fields.add("catch-all=" + statementId(caught.getHandler()) + "/" + caught.isFinally()
          + "/" + expression(caught.getMonitor()) + "/" + expressions(caught.getVars()));
      } else if (statement instanceof SynchronizedStatement sync) {
        fields.add("monitor=" + statementId(sync.getBody()));
      }

      for (int i = statement.getStats().size() - 1; i >= 0; i--) {
        pending.addFirst(statement.getStats().get(i));
      }
    }
    return String.join(";", fields);
  }

  private static String statementId(Statement statement) {
    return statement == null ? "-" : Integer.toString(statement.id);
  }

  private static String edges(List<StatEdge> edges) {
    return edges.stream().map(StructureReference::edgeId).collect(Collectors.joining("|"));
  }

  private static String edgeId(StatEdge edge) {
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
