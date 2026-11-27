import java.util.Arrays;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.StringJoiner;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.jetbrains.java.decompiler.code.FullInstructionSequence;
import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.code.JumpInstruction;
import org.jetbrains.java.decompiler.code.SwitchInstruction;
import org.jetbrains.java.decompiler.code.cfg.BasicBlock;
import org.jetbrains.java.decompiler.code.cfg.ControlFlowGraph;
import org.jetbrains.java.decompiler.code.cfg.ExceptionRangeCFG;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.modules.decompiler.ClearStructHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.FinallyProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.SequenceHelper;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.DomHelper;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;

class FinallySnapshot {
  static String run(ControlFlowGraph graph, RootStatement root, StructClass cl, StructMethod method,
                    MethodDescriptor descriptor, VarProcessor vars, CounterContainer counters,
                    Function<RootStatement, String> structure) {
    String before = "input=" + graph(graph, method.getInstructionSequence());
    String recovered;
    try {
      FinallyProcessor processor = new FinallyProcessor(method, descriptor, vars);
      int iteration = 0;
      while (processor.iterateGraph(cl, method, root, graph)) {
        RootStatement previous = root;
        try {
          root = DomHelper.parseGraph(graph, method, ++iteration);
        } catch (RuntimeException failure) {
          if (failure.getClass() == RuntimeException.class && "parsing failure!".equals(failure.getMessage())) {
            return before + "\trecovery-rejected=reparse:parsing failure!";
          }
          throw failure;
        }
        root.addComments(previous);
      }
      String semaphores = vars.getSyntheticSemaphores().stream().sorted()
        .map(Object::toString).collect(Collectors.joining(","));
      recovered = before + "\trecovered=" + semaphores + ";" + graph(graph, method.getInstructionSequence())
        + "\t" + structure.apply(root);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      if (isOffsetRemovalFailure(failure)) {
        return before + "\trecovery-rejected=instruction offsets:" + failure.getMessage();
      }
      return before + "\trecovery-" + StructureReference.failureSnapshot(failure);
    }

    try {
      DomHelper.buildSynchronized(root);
      DomHelper.removeSynchronizedHandler(root);
      root.buildContentFlags();
      SequenceHelper.condenseSequences(root);
      ClearStructHelper.clearStatements(root);
      new ExprProcessor(descriptor, vars).processStatement(root, cl);
      SequenceHelper.condenseSequences(root);
      return recovered + "\t" + structure.apply(root) + ";content="
        + root.hasTryCatch() + "," + root.hasLoops() + "," + root.hasSwitch()
        + "\t" + ExpressionSnapshot.snapshot(root, counters);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return recovered + "\tpost-finally-" + StructureReference.failureSnapshot(failure);
    }
  }

  private static boolean isOffsetRemovalFailure(Throwable failure) {
    if (failure.getClass() != IndexOutOfBoundsException.class) {
      return false;
    }
    StackTraceElement[] frames = failure.getStackTrace();
    for (int i = 1; i < frames.length; i++) {
      // A direct ArrayList.remove here is the old offset list. Instruction
      // removal would have InstructionSequence/VBStyleCollection on the stack.
      if (frames[i].getClassName().equals(FinallyProcessor.class.getName())
          && frames[i].getMethodName().equals("removeExceptionInstructionsEx")) {
        return frames[i - 1].getClassName().equals("java.util.ArrayList")
          && frames[i - 1].getMethodName().equals("remove");
      }
    }
    return false;
  }

  private static String graph(ControlFlowGraph graph, FullInstructionSequence method) {
    Map<Instruction, Integer> originals = new IdentityHashMap<>();
    for (int i = 0; i < method.length(); i++) {
      originals.put(method.getInstr(i), i);
    }
    Map<Instruction, Integer> aliases = new IdentityHashMap<>();
    StringJoiner fields = new StringJoiner(";");
    fields.add("entry=" + graph.getFirst().id + "/" + graph.getLast().id + "/" + graph.last_id);
    fields.add("comments=" + graph.addErrorComment + "|"
      + (graph.commentLines == null ? "" : String.join("|", graph.commentLines)));
    for (BasicBlock block : graph.getBlocks()) {
      fields.add("block=" + block.id);
      fields.add("edges=" + ids(block.getSuccs()) + "/" + ids(block.getSuccExceptions()));
      fields.add("preds=" + ids(block.getPreds()) + "/" + ids(block.getPredExceptions()));
      fields.add("offsets=" + block.getInstrOldOffsets().stream().map(Object::toString).collect(Collectors.joining(",")));
      for (int i = 0; i < block.size(); i++) {
        Instruction instruction = block.getInstruction(i);
        int identity = aliases.computeIfAbsent(instruction, key -> aliases.size());
        fields.add("insn=" + identity + "|" + originals.getOrDefault(instruction, -1) + "|" + instruction(instruction));
      }
    }
    fields.add("exit-preds=" + ids(graph.getLast().getPreds()) + "/" + ids(graph.getLast().getPredExceptions()));
    for (ExceptionRangeCFG range : graph.getExceptions()) {
      List<String> types = range.getExceptionTypes();
      fields.add("range=" + range.getHandler().id + "|" + (types == null ? "*" : String.join(",", types))
        + "|" + ids(range.getProtectedRange()));
    }
    fields.add("finally-exits=" + graph.getFinallyExits().stream().map(block -> block.id).sorted()
      .map(Object::toString).collect(Collectors.joining(",")));
    fields.add("subroutines=" + StructureReference.subroutines(graph).entrySet().stream()
      .map(entry -> entry.getKey().id + ":" + entry.getValue().id).sorted().collect(Collectors.joining(",")));
    return fields.toString();
  }

  private static String instruction(Instruction instruction) {
    String operands = IntStream.range(0, instruction.operandsCount()).map(instruction::operand)
      .mapToObj(Integer::toString).collect(Collectors.joining(","));
    String target = "";
    if (instruction instanceof JumpInstruction jump) {
      target = "j" + jump.destination;
    } else if (instruction instanceof SwitchInstruction branch) {
      target = "s" + branch.getDefaultDestination() + "/" + ints(branch.getDestinations()) + "/" + ints(branch.getValues());
    }
    return instruction.opcode + "," + instruction.group + "," + instruction.wide + ","
      + instruction.startOffset + "," + instruction.length + "[" + operands + "]" + target;
  }

  private static String ints(int[] values) {
    return values == null ? "" : Arrays.stream(values).mapToObj(Integer::toString).collect(Collectors.joining(","));
  }

  private static String ids(Collection<BasicBlock> blocks) {
    return blocks.stream().map(block -> Integer.toString(block.id)).collect(Collectors.joining(","));
  }
}
