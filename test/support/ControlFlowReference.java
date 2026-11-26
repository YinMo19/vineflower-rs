// SPDX-License-Identifier: Apache-2.0

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;
import java.util.stream.IntStream;

import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.code.cfg.ControlFlowGraph;
import org.jetbrains.java.decompiler.code.cfg.ExceptionRangeCFG;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.code.DeadCodeHelper;
import org.jetbrains.java.decompiler.modules.code.ExceptionDeobfuscator;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.DomHelper;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.FastExtendedPostdominanceHelper;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.StrongConnectivityHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.GeneralStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

class ControlFlowReference {
  private static final Field SUBROUTINES = subroutinesField();
  private static final Method GRAPH_TO_STATEMENT = graphToStatementMethod();
  private record HandlerOrderBoundary(int lastBlockId, int orderedRangeCount) { }

  public static void main(String[] args) throws IOException {
    new Fernflower(null, Map.of(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0"), IFernflowerLogger.NO_OP);
    List<String> paths = Files.readAllLines(Path.of(args[0]));
    for (int index = 0; index < paths.size(); index++) {
      byte[] bytes = Files.readAllBytes(Path.of(paths.get(index)));
      for (boolean forceJsr : new boolean[] {false, true}) {
        DecompilerContext.setProperty(IFernflowerPreferences.FORCE_JSR_INLINE, forceJsr ? "1" : "0");
        inspect(index + "\t" + (forceJsr ? "force-jsr" : "default") + "\t", bytes, forceJsr);
      }
    }
  }

  private static void inspect(String key, byte[] bytes, boolean forceJsr) {
    StructClass cl;
    try {
      cl = StructClass.create(new DataInputFullStream(bytes), true);
      emit(key + "<class>", "load", cl.qualifiedName);
    } catch (Exception | AssertionError | StackOverflowError failure) {
      emitFailure(key + "<class>", "load", failure);
      return;
    }
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS, cl);
    for (StructMethod method : cl.getMethods()) {
      if (!method.containsCode()) {
        continue;
      }
      String methodKey = key + method.getName() + method.getDescriptor();
      String stage = "construct";
      try {
        DecompilerContext.startMethod(null);
        method.expandData(cl);
        ControlFlowGraph graph = new ControlFlowGraph(method.getInstructionSequence());
        DecompilerContext.getCounterContainer().setCounter(CounterContainer.VAR_COUNTER, method.getLocalVariables());
        emit(methodKey, stage, snapshot(graph, true));

        stage = "common";
        DeadCodeHelper.removeDeadBlocks(graph);
        if (method.getBytecodeVersion().hasJsr() || forceJsr) {
          graph.inlineJsr(cl, method);
        }
        DeadCodeHelper.connectDummyExitBlock(graph);
        DeadCodeHelper.removeGotos(graph);
        emit(methodKey, stage, snapshot(graph, false));

        stage = "java";
        HandlerOrderBoundary boundary = prepareJavaGraph(graph, method);
        emit(methodKey, stage, "handler-order-boundary=" + boundary.lastBlockId() + "," + boundary.orderedRangeCount()
          + ";" + snapshot(graph, false));

        stage = "postdominance";
        RootStatement root = (RootStatement) GRAPH_TO_STATEMENT.invoke(null, graph, method);
        emit(methodKey, stage, postdominanceSnapshot(root.getFirst()));
      } catch (Exception | AssertionError | StackOverflowError failure) {
        emitFailure(methodKey, stage, failure);
      } finally {
        method.releaseResources();
      }
    }
  }

  private static HandlerOrderBoundary prepareJavaGraph(ControlFlowGraph graph, StructMethod method) {
    ExceptionDeobfuscator.removeCircularRanges(graph);
    ExceptionDeobfuscator.restorePopRanges(graph);
    if (DecompilerContext.getOption(IFernflowerPreferences.REMOVE_EMPTY_RANGES)) {
      ExceptionDeobfuscator.removeEmptyRanges(graph);
    }
    if (DecompilerContext.getOption(IFernflowerPreferences.ENSURE_SYNCHRONIZED_MONITOR)) {
      DeadCodeHelper.extendSynchronizedRangeToMonitorexit(graph);
    }
    if (DecompilerContext.getOption(IFernflowerPreferences.INCORPORATE_RETURNS)) {
      DeadCodeHelper.incorporateValueReturns(graph);
    }
    ExceptionDeobfuscator.insertEmptyExceptionHandlerBlocks(graph);
    DeadCodeHelper.mergeBasicBlocks(graph);
    int orderedRangeCount = graph.getExceptions().size();
    if (ExceptionDeobfuscator.hasObfuscatedExceptions(graph)) {
      List<List<BasicBlock>> protectedBeforeSplit = graph.getExceptions().stream()
        .map(range -> List.copyOf(range.getProtectedRange())).toList();
      if (!ExceptionDeobfuscator.handleMultipleEntryExceptionRanges(graph)) {
        graph.addComment("$VF: Could not handle exception ranges with multiple entries");
        graph.addErrorComment = true;
      }
      while (orderedRangeCount > 0 && !protectedBeforeSplit.get(orderedRangeCount - 1)
        .equals(graph.getExceptions().get(orderedRangeCount - 1).getProtectedRange())) {
        orderedRangeCount--;
      }
      int handlerIdBoundary = graph.last_id;
      ExceptionDeobfuscator.insertDummyExceptionHandlerBlocks(graph, method.getBytecodeVersion());
      return new HandlerOrderBoundary(handlerIdBoundary, orderedRangeCount);
    }
    return new HandlerOrderBoundary(graph.last_id, orderedRangeCount);
  }

  static String snapshot(ControlFlowGraph graph, boolean constructed) throws IllegalAccessException {
    StringBuilder out = new StringBuilder();
    out.append("first=").append(graph.getFirst().id).append(";last=").append(graph.getLast().id);
    out.append(";last-id=").append(graph.last_id);
    for (BasicBlock block : graph.getBlocks()) {
      out.append(";block=").append(block.id);
      String instructions = StreamSupport.stream(block.getSeq().spliterator(), false)
        .map(instruction -> {
          String operands = IntStream.range(0, instruction.operandsCount()).map(instruction::operand)
            .mapToObj(Integer::toString).collect(Collectors.joining(" "));
          return instruction.opcode + "@" + instruction.startOffset + "+" + instruction.length
            + "/" + instruction.group + "/" + instruction.wide + "[" + operands + "]";
        })
        .collect(Collectors.joining(","));
      out.append(";instructions=").append(instructions);
      out.append(";offsets=").append(block.getInstrOldOffsets().stream().map(Object::toString).collect(Collectors.joining(",")));
      out.append(";edges=").append(ids(block.getSuccs()));
      out.append(";exception-edges=").append(ids(block.getSuccExceptions()));
    }
    List<BasicBlock> exitPredecessors = graph.getLast().getPreds();
    out.append(";exit-predecessors=").append(constructed ? ids(exitPredecessors) : sortedIds(exitPredecessors));
    for (ExceptionRangeCFG range : graph.getExceptions()) {
      String types = range.getExceptionTypes() == null ? "*" : String.join(",", range.getExceptionTypes());
      out.append(";range=").append(range.getHandler().id).append(':').append(types);
      out.append(':').append(constructed ? ids(range.getProtectedRange()) : sortedIds(range.getProtectedRange()));
    }
    out.append(";finally-exits=").append(sortedIds(graph.getFinallyExits()));
    out.append(";rpo=").append(ids(graph.getReversePostOrder()));
    out.append(";error-comment=").append(graph.addErrorComment);
    out.append(";comments=").append(graph.commentLines == null ? "" : String.join(",", graph.commentLines));
    if (constructed) {
      Map<?, ?> subroutines = (Map<?, ?>) SUBROUTINES.get(graph);
      out.append(";subroutines=").append(subroutines.entrySet().stream()
        .map(entry -> ((BasicBlock) entry.getKey()).id + ":" + ((BasicBlock) entry.getValue()).id)
        .sorted().collect(Collectors.joining(",")));
    }
    return out.toString();
  }

  private static Field subroutinesField() {
    try {
      Field field = ControlFlowGraph.class.getDeclaredField("subroutines");
      field.setAccessible(true);
      return field;
    } catch (ReflectiveOperationException failure) {
      throw new ExceptionInInitializerError(failure);
    }
  }

  private static Method graphToStatementMethod() {
    try {
      Method method = DomHelper.class.getDeclaredMethod("graphToStatement", ControlFlowGraph.class, StructMethod.class);
      method.setAccessible(true);
      return method;
    } catch (ReflectiveOperationException failure) {
      throw new ExceptionInInitializerError(failure);
    }
  }

  private static String postdominanceSnapshot(Statement statement) {
    if (!(statement instanceof GeneralStatement general)) {
      return "basic=" + statement.id;
    }
    StrongConnectivityHelper connectivity = new StrongConnectivityHelper(general);
    var postdominators = DomHelper.calcPostDominators(general);
    var extended = new FastExtendedPostdominanceHelper().getExtendedPostdominators(general);
    return "rpo=" + statementIds(general.getReversePostOrderList())
      + ";post-rpo=" + statementIds(general.getPostReversePostOrderList())
      + ";components=" + connectivity.getComponents().stream()
        .map(ControlFlowReference::statementIds).collect(Collectors.joining("/"))
      + ";post=" + IntStream.range(0, postdominators.size())
        .mapToObj(index -> postdominators.getKey(index) + ":" + joinIds(postdominators.get(index)))
        .collect(Collectors.joining("/"))
      + ";extended=" + extended.entrySet().stream()
        .map(entry -> entry.getKey() + ":" + joinIds(entry.getValue())).collect(Collectors.joining("/"));
  }

  private static String statementIds(List<Statement> statements) {
    return statements.stream().map(statement -> Integer.toString(statement.id)).collect(Collectors.joining(","));
  }

  private static String joinIds(Iterable<Integer> ids) {
    return StreamSupport.stream(ids.spliterator(), false).map(Object::toString).collect(Collectors.joining(","));
  }

  private static String ids(List<BasicBlock> blocks) {
    return blocks.stream().map(block -> Integer.toString(block.id)).collect(Collectors.joining(","));
  }

  private static String sortedIds(Iterable<BasicBlock> blocks) {
    return StreamSupport.stream(blocks.spliterator(), false)
      .map(block -> block.id).sorted().map(Object::toString).collect(Collectors.joining(","));
  }

  private static void emit(String key, String stage, String snapshot) {
    System.out.println(key + "\t" + stage + "\t" + snapshot);
  }

  private static void emitFailure(String key, String stage, Throwable failure) {
    emit(key, stage, "error=" + failure.toString().replace('\t', ' ').replace('\n', ' ').replace('\r', ' '));
  }
}
