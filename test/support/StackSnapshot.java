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
import java.util.function.BiFunction;
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
import org.jetbrains.java.decompiler.modules.decompiler.ClearStructHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.FinallyProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.PPandMMHelper;
import org.jetbrains.java.decompiler.modules.decompiler.SequenceHelper;
import org.jetbrains.java.decompiler.modules.decompiler.SimplifyExprentsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.StackVarsProcessor;
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
  record Options(int group, boolean simplify, boolean ternary, boolean lvt, boolean booleanAsInt) {}
  private record RootScope(ImportCollector imports, List<ClassNode> wrapperOrder, String error) {}

  static class Context {
    private final List<List<String>> groups;
    private final boolean increments;
    private final Map<ClassNode, RootScope> roots = new IdentityHashMap<>();
    private final Map<ClassNode, ClassWrapper> wrappers = new IdentityHashMap<>();
    private final List<ClassNode> published = new ArrayList<>();
    private Options options;
    private Fernflower engine;
    private ClassNode current;

    Context(List<List<String>> groups, boolean increments) {
      this.groups = groups;
      this.increments = increments;
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
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0",
        IFernflowerPreferences.SIMPLIFY_STACK_SECOND_PASS, next.simplify() ? "1" : "0",
        IFernflowerPreferences.TERNARY_CONDITIONS, next.ternary() ? "1" : "0",
        IFernflowerPreferences.USE_DEBUG_VAR_NAMES, next.lvt() ? "1" : "0",
        IFernflowerPreferences.BOOLEAN_TRUE_ONE, next.booleanAsInt() ? "1" : "0"
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
               String name, String descriptor,
               BiFunction<RootStatement, CounterContainer, String> tree) throws IOException {
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
        input.mark(Integer.MAX_VALUE);
        var firstGraph = StructureReference.readGraph(input, method);
        input.reset();
        var settledGraph = StructureReference.readGraph(input, method);
        if (scope.error() != null) {
          return "class-rejected=" + scope.error();
        }
        var hidden = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_WRAPPER).getHiddenMembers();
        var initialHidden = Set.copyOf(hidden);
        String first = stage(firstGraph, scope.imports(), cl, method, tree, initialHidden, true, increments);
        hidden.clear();
        hidden.addAll(initialHidden);
        if ("rejected=parsing failure!".equals(first)) {
          return first;
        }
        return first + "\t" + stage(settledGraph, scope.imports(), cl, method, tree, initialHidden, false, increments);
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
                              BiFunction<RootStatement, CounterContainer, String> tree, Set<String> initialHidden,
                              boolean first, boolean increments) {
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
      if (increments) {
        boolean repeat;
        do {
          operation = "simplify-stack";
          StackVarsProcessor.simplifyStackVars(root, method, cl);
          operation = "set-var-versions";
          vars.setVarVersions(root);
          repeat = false;
          if (!first) {
            operation = "find-increments";
            repeat = new PPandMMHelper(vars).findPPandMM(root);
          }
        } while (repeat);
        if (!first) {
          operation = "inline-increments";
          PPandMMHelper.inlinePPIandMMIIf(root);
        }
      } else if (first) {
        var ssa = new SSAConstructorSparseEx();
        ssa.splitVariables(root, method);
        var reordered = new HashSet<Integer>();
        while (SimplifyExprentsHelper.simplifyStackVarsStatement(root, reordered, ssa, cl, true)) {}
      } else {
        StackVarsProcessor.simplifyStackVars(root, method, cl);
      }
      var hidden = DecompilerContext.getContextProperty(DecompilerContext.CURRENT_CLASS_WRAPPER).getHiddenMembers();
      String allMembers = hidden.stream().sorted().map(ExpressionSnapshot::text).collect(Collectors.joining(","));
      String added = hidden.stream().filter(member -> !initialHidden.contains(member)).sorted()
        .map(ExpressionSnapshot::text).collect(Collectors.joining(","));
      operation = "snapshot";
      String snapshot = tree.apply(root, counters) + ";hidden=" + allMembers + ";hidden-added=" + added
        + "\t" + ExpressionSnapshot.snapshot(root, counters);
      if (increments) {
        snapshot += "\t" + VariableSnapshot.snapshot(vars);
        if (first) {
          operation = "find-increments";
          snapshot += ";repeat=" + new PPandMMHelper(vars).findPPandMM(root);
        }
      }
      return snapshot;
    } catch (RuntimeException | AssertionError | StackOverflowError error) {
      if (error.getClass() == RuntimeException.class && "parsing failure!".equals(error.getMessage())) {
        return "rejected=parsing failure!";
      }
      return (increments ? "increments-" + operation + "-" : "stack-") + StructureReference.failureSnapshot(error);
    }
  }
}
