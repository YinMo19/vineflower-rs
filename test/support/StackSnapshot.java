// SPDX-License-Identifier: Apache-2.0

import java.io.DataInputStream;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.StringJoiner;
import java.util.stream.Collectors;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.code.MethodProperties;
import org.jetbrains.java.decompiler.code.cfg.ControlFlowGraph;
import org.jetbrains.java.decompiler.main.ClassesProcessor;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.ClassWrapper;
import org.jetbrains.java.decompiler.main.rels.LambdaProcessor;
import org.jetbrains.java.decompiler.modules.code.MethodPropertiesProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.AssertProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.ClearStructHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ConcatenationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.EliminateLoopsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.FinallyProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.IfHelper;
import org.jetbrains.java.decompiler.modules.decompiler.IfPatternMatchProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.IntersectionCastProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.LabelHelper;
import org.jetbrains.java.decompiler.modules.decompiler.LoopExtractHelper;
import org.jetbrains.java.decompiler.modules.decompiler.MergeHelper;
import org.jetbrains.java.decompiler.modules.decompiler.PPandMMHelper;
import org.jetbrains.java.decompiler.modules.decompiler.SecondaryFunctionsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.SequenceHelper;
import org.jetbrains.java.decompiler.modules.decompiler.SimplifyExprentsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.StackVarsProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.SwitchExpressionHelper;
import org.jetbrains.java.decompiler.modules.decompiler.SwitchPatternMatchProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.decompose.DomHelper;
import org.jetbrains.java.decompiler.modules.decompiler.sforms.SSAConstructorSparseEx;
import org.jetbrains.java.decompiler.modules.decompiler.stats.RootStatement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.util.InterpreterUtil;

class StackSnapshot {
  enum Check {
    STACK, INCREMENTS, PRE_MAIN, LOOP_ELIMINATION, LOOP_ENHANCEMENT, LOOP_MERGE, MAIN_LOOP_LABELS,
    SECONDARY_FUNCTIONS, PATTERN_MATCHING_ENTRY, IF_PATTERNS, SWITCH_ENTRY, SWITCH_PASSES, TRY_ENTRY;

    boolean usesLoopHeaders() {
      return this == LOOP_ENHANCEMENT || this == LOOP_MERGE || identifiesLabels();
    }

    boolean identifiesLabels() {
      return this == MAIN_LOOP_LABELS || this == SECONDARY_FUNCTIONS || settlesPatternEntry();
    }

    boolean settlesPatternEntry() {
      return this == PATTERN_MATCHING_ENTRY || matchesIfPatterns();
    }

    boolean matchesIfPatterns() {
      return this == IF_PATTERNS || this == SWITCH_ENTRY || recoversSwitches();
    }

    boolean recoversSwitches() {
      return this == SWITCH_PASSES || this == TRY_ENTRY;
    }

    ExpressionSnapshot.Detail expressionDetail() {
      return switch (this) {
        case SWITCH_PASSES, TRY_ENTRY -> ExpressionSnapshot.Detail.SWITCHES;
        case PATTERN_MATCHING_ENTRY, IF_PATTERNS, SWITCH_ENTRY -> ExpressionSnapshot.Detail.INTERSECTION_CASTS;
        case SECONDARY_FUNCTIONS -> ExpressionSnapshot.Detail.SECONDARY_FUNCTIONS;
        default -> usesLoopHeaders() ? ExpressionSnapshot.Detail.LOOP_HEADERS : ExpressionSnapshot.Detail.BASE;
      };
    }
  }

  record Options(int group, boolean simplify, boolean ternary, boolean lvt, boolean booleanAsInt,
                 boolean assertions, boolean ternaryConstants) {}
  private record RootScope(ImportCollector imports, List<ClassNode> wrapperOrder, String error) {}

  static class Context {
    private final List<List<String>> groups;
    private final Check check;
    private final Map<ClassNode, RootScope> roots = new IdentityHashMap<>();
    private final Map<ClassNode, ClassWrapper> wrappers = new IdentityHashMap<>();
    private final List<ClassNode> published = new ArrayList<>();
    private Options options;
    private Fernflower engine;
    private ClassNode current;

    Context(List<List<String>> groups, Check check) {
      this.groups = groups;
      this.check = check;
    }

    private void select(Options next) {
      if (next.equals(options)) {
        return;
      }
      if (engine != null) {
        engine.clearContext();
      }
      options = next;
      roots.clear();
      wrappers.clear();
      published.clear();
      current = null;
      engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, check.usesLoopHeaders() ? "1" : "0",
        IFernflowerPreferences.SIMPLIFY_STACK_SECOND_PASS, next.simplify() ? "1" : "0",
        IFernflowerPreferences.TERNARY_CONDITIONS, next.ternary() ? "1" : "0",
        IFernflowerPreferences.USE_DEBUG_VAR_NAMES, next.lvt() ? "1" : "0",
        IFernflowerPreferences.BOOLEAN_TRUE_ONE, next.booleanAsInt() ? "1" : "0",
        IFernflowerPreferences.DECOMPILE_ASSERTIONS, next.assertions() ? "1" : "0",
        IFernflowerPreferences.TERNARY_CONSTANT_SIMPLIFICATION, next.ternaryConstants() ? "1" : "0"
      ), IFernflowerLogger.NO_OP);
      for (String path : groups.get(next.group())) {
        engine.addSource(Path.of(path).toFile());
      }
      DecompilerContext.getClassProcessor().loadClasses(null);
    }

    private RootScope prepareRoot(ClassNode root) {
      var imports = new ImportCollector(root);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, null);
      DecompilerContext.startClass(imports);
      var cl = root.classStruct;
      var order = new ArrayList<ClassNode>();
      try {
        if (!(cl.isSynthetic() && "package-info".equals(root.simpleName)) &&
            !(cl.hasModifier(CodeConstants.ACC_MODULE) && cl.hasAttribute(StructGeneralAttribute.ATTRIBUTE_MODULE))) {
          new LambdaProcessor().processClass(root);
          ADD_NAMES.invoke(null, root, imports);
          appendWrapperOrder(root, order);
        }
        return new RootScope(imports, order, null);
      } catch (IllegalStateException error) {
        return new RootScope(imports, List.of(), error.getMessage());
      } catch (ReflectiveOperationException | IOException error) {
        throw new IllegalStateException("Cannot prepare root " + cl.qualifiedName, error);
      }
    }

    private ClassWrapper selectWrapper(ClassNode node, RootScope scope) {
      if (node != current) {
        for (var old : published) {
          setWrapper(old, null);
        }
        published.clear();
        for (var earlier : scope.wrapperOrder()) {
          if (earlier == node) {
            break;
          }
          setWrapper(earlier, wrappers.computeIfAbsent(earlier, StackSnapshot::wrapper));
          published.add(earlier);
        }
        current = node;
      }
      // ClassesProcessor only publishes this slot after wrapper.init returns.
      return wrappers.computeIfAbsent(node, StackSnapshot::wrapper);
    }

    String run(DataInputStream input, Options options, String classname,
               String name, String descriptor) throws IOException {
      select(options);
      var node = Objects.requireNonNull(DecompilerContext.getClassProcessor().getMapRootClasses().get(classname));
      var owner = node;
      while (owner.parent != null) {
        owner = owner.parent;
      }
      var scope = roots.computeIfAbsent(owner, this::prepareRoot);
      var cl = node.classStruct;
      var method = Objects.requireNonNull(cl.getMethod(name, descriptor));

      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS, cl);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_WRAPPER, selectWrapper(node, scope));

      method.expandData(cl);
      try {
        if (!check.usesLoopHeaders()) {
          input.mark(Integer.MAX_VALUE);
        }
        var firstGraph = StructureReference.readGraph(input, method);
        ControlFlowGraph settledGraph = null;
        if (!check.usesLoopHeaders()) {
          input.reset();
          settledGraph = StructureReference.readGraph(input, method);
        }
        if (scope.error() != null) {
          return "class-rejected=" + scope.error();
        }
        var hidden = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_WRAPPER).getHiddenMembers();
        var initialHidden = Set.copyOf(hidden);
        String first = stage(firstGraph, scope.imports(), cl, method, initialHidden, true, check);
        hidden.clear();
        hidden.addAll(initialHidden);
        if (settledGraph == null || "rejected=parsing failure!".equals(first)) {
          return first;
        }
        return first + "\t" + stage(settledGraph, scope.imports(), cl, method, initialHidden, false, check);
      } finally {
        method.releaseResources();
      }
    }
  }

  private static final Method ADD_NAMES = processorMethod("addClassNameToImport", ClassNode.class, ImportCollector.class);
  private static final Method EARLY_WRAPPER = processorMethod("shouldInitEarly", ClassNode.class);
  private static final Field NODE_WRAPPER = wrapperField();

  private static Method processorMethod(String name, Class<?>... args) {
    try {
      Method method = ClassesProcessor.class.getDeclaredMethod(name, args);
      method.setAccessible(true);
      return method;
    } catch (ReflectiveOperationException error) {
      throw new AssertionError(error);
    }
  }

  private static Field wrapperField() {
    try {
      Field field = ClassNode.class.getDeclaredField("wrapper");
      field.setAccessible(true);
      return field;
    } catch (ReflectiveOperationException error) {
      throw new AssertionError(error);
    }
  }

  private static void setWrapper(ClassNode node, ClassWrapper wrapper) {
    try {
      NODE_WRAPPER.set(node, wrapper);
    } catch (IllegalAccessException error) {
      throw new AssertionError(error);
    }
  }

  private static void appendWrapperOrder(ClassNode node, List<ClassNode> order) throws ReflectiveOperationException {
    if (node.type == ClassNode.Type.LAMBDA) {
      return;
    }
    var later = new ArrayList<ClassNode>();
    for (var child : node.nested) {
      if ((Boolean) EARLY_WRAPPER.invoke(null, child)) {
        appendWrapperOrder(child, order);
      } else {
        later.add(child);
      }
    }
    order.add(node);
    for (var child : later) {
      appendWrapperOrder(child, order);
    }
  }

  private static ClassWrapper wrapper(ClassNode node) {
    var wrapper = new ClassWrapper(node);
    for (var method : node.classStruct.getMethods()) {
      var properties = new MethodProperties(method);
      MethodPropertiesProcessor.parse(method, node.classStruct, properties);
      wrapper.getMethodProperties().put(InterpreterUtil.makeUniqueKey(method.getName(), method.getDescriptor()), properties);
    }
    return wrapper;
  }

  private static String stage(ControlFlowGraph graph, ImportCollector imports, StructClass cl, StructMethod method,
                              Set<String> initialHidden, boolean first, Check check) {
    DecompilerContext.startClass(new ImportCollector(imports));
    var descriptor = MethodDescriptor.parseDescriptor(method, null);
    var vars = new VarProcessor(method, descriptor);
    DecompilerContext.startMethod(vars);
    var counters = DecompilerContext.getCounterContainer();
    counters.setCounter(CounterContainer.VAR_COUNTER, method.getLocalVariables());
    String operation = "structure";
    try {
      var root = DomHelper.parseGraph(graph, method, 0);
      operation = "finally";
      var finallyProcessor = new FinallyProcessor(method, descriptor, vars);
      int iteration = 0;
      while (finallyProcessor.iterateGraph(cl, method, root, graph)) {
        var oldRoot = root;
        root = DomHelper.parseGraph(graph, method, ++iteration);
        root.addComments(oldRoot);
      }
      DomHelper.buildSynchronized(root);
      DomHelper.removeSynchronizedHandler(root);
      root.buildContentFlags();
      SequenceHelper.condenseSequences(root);
      ClearStructHelper.clearStatements(root);
      operation = "lift";
      new ExprProcessor(descriptor, vars).processStatement(root, cl);
      SequenceHelper.condenseSequences(root);

      operation = "simplify-stack";
      if (check != Check.STACK) {
        boolean firstNumbering = check == Check.INCREMENTS && first;
        boolean repeat;
        do {
          operation = "simplify-stack";
          StackVarsProcessor.simplifyStackVars(root, method, cl);
          operation = "set-var-versions";
          vars.setVarVersions(root);
          repeat = false;
          if (!firstNumbering) {
            operation = "find-increments";
            repeat = new PPandMMHelper(vars).findPPandMM(root);
          }
        } while (repeat);
        if (!firstNumbering) {
          operation = "inline-increments";
          PPandMMHelper.inlinePPIandMMIIf(root);
        }
        if (check == Check.PRE_MAIN || check == Check.LOOP_ELIMINATION || check.usesLoopHeaders()) {
          operation = "simplify-concat";
          if (cl.getVersion().hasIndyStringConcat()) {
            ConcatenationHelper.simplifyStringConcat(root);
          }
          if (!first || check != Check.PRE_MAIN) {
            operation = "build-assertions";
            AssertProcessor.buildAssertions(root);
          }
        }
      } else if (first) {
        var ssa = new SSAConstructorSparseEx();
        ssa.splitVariables(root, method);
        var reordered = new HashSet<Integer>();
        while (SimplifyExprentsHelper.simplifyStackVarsStatement(root, reordered, ssa, cl, true)) {}
      } else {
        StackVarsProcessor.simplifyStackVars(root, method, cl);
      }
      if (check.usesLoopHeaders()) {
        String details = "";
        while (true) {
          operation = "clean-up-edges";
          LabelHelper.cleanUpEdges(root);
          if (check == Check.LOOP_ENHANCEMENT) {
            operation = "eliminate-loops";
            if (root.hasLoops()) {
              while (EliminateLoopsHelper.eliminateLoops(root, cl)) {}
            }
            operation = "enhance-loops";
            details = ";enhanced=" + (root.hasLoops() && MergeHelper.enhanceLoops(root));
          } else if (root.hasLoops()) {
            operation = "merge-loops";
            while (true) {
              if (EliminateLoopsHelper.eliminateLoops(root, cl)) {
                continue;
              }
              MergeHelper.enhanceLoops(root);
              if (LoopExtractHelper.extractLoops(root)) {
                continue;
              }
              if (!IfHelper.mergeAllIfs(root)) {
                break;
              }
            }
          }
          if (check.identifiesLabels()) {
            operation = "simplify-stack";
            StackVarsProcessor.simplifyStackVars(root, method, cl);
            operation = "set-var-versions";
            vars.setVarVersions(root);
            operation = "identify-labels";
            LabelHelper.identifyLabels(root);
          }
          if (check == Check.SECONDARY_FUNCTIONS || check.settlesPatternEntry()) {
            operation = "identify-secondary";
            boolean changed = SecondaryFunctionsHelper.identifySecondaryFunctions(root, vars);
            if (check == Check.SECONDARY_FUNCTIONS) {
              details = ";secondary=" + changed;
            } else {
              if (changed) {
                continue;
              }
              operation = "intersection-casts";
              if (IntersectionCastProcessor.makeIntersectionCasts(root)) {
                continue;
              }
            }
          }
          if (check.matchesIfPatterns()) {
            operation = "match-if-patterns";
            String before = counterSnapshot(counters);
            boolean changed = DecompilerContext.getOption(IFernflowerPreferences.PATTERN_MATCHING)
              && cl.getVersion().hasIfPatternMatching() && IfPatternMatchProcessor.matchInstanceof(root);
            if (check == Check.IF_PATTERNS) {
              details = ";pattern-counters-before=" + before + ";if-patterns=" + changed;
            } else if (changed) {
              continue;
            }
          }
          if (check.recoversSwitches()) {
            boolean patterns = false;
            boolean expressions = false;
            String afterPatterns = null;
            if (root.hasSwitch()) {
              operation = "process-switch-patterns";
              patterns = SwitchPatternMatchProcessor.hasPatternMatch(root)
                && SwitchPatternMatchProcessor.processPatternMatching(root);
              afterPatterns = counterSnapshot(counters);
              operation = "process-switch-expressions";
              expressions = SwitchExpressionHelper.hasSwitchExpressions(root)
                && SwitchExpressionHelper.processSwitchExpressions(root);
            }
            if (check == Check.SWITCH_PASSES) {
              details = ";switch-patterns=" + patterns + ";switch-pattern-counters="
                + (afterPatterns == null ? counterSnapshot(counters) : afterPatterns)
                + ";switch-expressions=" + expressions;
            } else if (patterns || expressions) {
              continue;
            }
          }
          break;
        }
        operation = "snapshot";
        return snapshot(root, counters, vars, initialHidden, check, details)
          + "\t" + DirectGraphSnapshot.enhanced(root);
      } else if (check == Check.LOOP_ELIMINATION) {
        operation = "snapshot";
        var originalEdges = first ? StructureReference.edgeStates(root) : Map.of();
        operation = "clean-up-edges";
        LabelHelper.cleanUpEdges(root);
        operation = "snapshot";
        if (first) {
          var cleanedEdges = StructureReference.edgeStates(root);
          long removed = originalEdges.keySet().stream().filter(edge -> !cleanedEdges.containsKey(edge)).count();
          long rewritten = originalEdges.entrySet().stream().filter(entry -> cleanedEdges.containsKey(entry.getKey())
            && !entry.getValue().equals(cleanedEdges.get(entry.getKey()))).count();
          return snapshot(root, counters, vars, initialHidden, check,
            ";cleanup-removed=" + removed + ";cleanup-rewritten=" + rewritten);
        }

        List<String> states = new ArrayList<>();
        states.add(snapshot(root, counters, vars, initialHidden, check, ""));
        var iterations = new StringJoiner(",");
        if (root.hasLoops()) {
          boolean repeat;
          do {
            operation = "eliminate-loops";
            repeat = EliminateLoopsHelper.eliminateLoops(root, cl);
            iterations.add(Boolean.toString(repeat));
            operation = "snapshot";
            states.add(snapshot(root, counters, vars, initialHidden, check, ""));
          } while (repeat);
        }
        return "iterations=" + iterations + "\t" + String.join("\t", states);
      }

      operation = "snapshot";
      String snapshot = snapshot(root, counters, vars, initialHidden, check, "");
      if (check == Check.INCREMENTS && first) {
        operation = "find-increments";
        snapshot += ";repeat=" + new PPandMMHelper(vars).findPPandMM(root);
      } else if (check == Check.PRE_MAIN && first) {
        operation = "build-assertions";
        snapshot += ";assert-changed=" + AssertProcessor.buildAssertions(root);
      }
      return snapshot;
    } catch (RuntimeException | AssertionError | StackOverflowError error) {
      if (error.getClass() == RuntimeException.class && "parsing failure!".equals(error.getMessage())) {
        return "rejected=parsing failure!";
      }
      String failure = switch (check) {
        case STACK -> "stack-";
        case INCREMENTS -> "increments-" + operation + "-";
        case PRE_MAIN -> "pre-main-" + operation + "-";
        case LOOP_ELIMINATION -> "loop-elimination-" + operation + "-";
        case LOOP_ENHANCEMENT -> "loop-enhancement-" + operation + "-";
        case LOOP_MERGE -> "loop-merge-" + operation + "-";
        case MAIN_LOOP_LABELS -> "main-loop-labels-" + operation + "-";
        case SECONDARY_FUNCTIONS -> "secondary-functions-" + operation + "-";
        case PATTERN_MATCHING_ENTRY -> "pattern-matching-entry-" + operation + "-";
        case IF_PATTERNS -> "if-patterns-" + operation + "-";
        case SWITCH_ENTRY -> "switch-entry-" + operation + "-";
        case SWITCH_PASSES -> "switch-passes-" + operation + "-";
        case TRY_ENTRY -> "try-entry-" + operation + "-";
      };
      return failure + StructureReference.failureSnapshot(error);
    }
  }

  private static String snapshot(RootStatement root, CounterContainer counters, VarProcessor vars,
                                 Set<String> initialHidden, Check check, String details) {
    var hidden = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_WRAPPER).getHiddenMembers();
    String allMembers = hidden.stream().sorted().map(ExpressionSnapshot::text).collect(Collectors.joining(","));
    String added = hidden.stream().filter(member -> !initialHidden.contains(member)).sorted()
      .map(ExpressionSnapshot::text).collect(Collectors.joining(","));
    boolean loopStage = check == Check.LOOP_ELIMINATION || check.usesLoopHeaders();
    String content = check == Check.PRE_MAIN || loopStage
      ? ";content=" + root.hasTryCatch() + "," + root.hasLoops() + "," + root.hasSwitch() : "";
    String snapshot = StructureReference.snapshot(root, counters, loopStage, check.recoversSwitches())
      + content + ";hidden=" + allMembers + ";hidden-added=" + added + details
      + "\t" + ExpressionSnapshot.snapshot(root, counters, check.expressionDetail());
    return check == Check.STACK ? snapshot : snapshot + "\t" + VariableSnapshot.snapshot(vars);
  }

  private static String counterSnapshot(CounterContainer counters) {
    return counters.getCounter(CounterContainer.STATEMENT_COUNTER)
      + "," + counters.getCounter(CounterContainer.EXPRESSION_COUNTER)
      + "," + counters.getCounter(CounterContainer.VAR_COUNTER);
  }
}
