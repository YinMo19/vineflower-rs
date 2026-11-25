// SPDX-License-Identifier: Apache-2.0

import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.BitSet;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.StringJoiner;
import java.util.TreeMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.jetbrains.java.decompiler.code.Instruction;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.struct.gen.MethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericMethodDescriptor;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;

class ExpressionSnapshot {
  private static final Field ARRAY_HARD_TYPE = field(ArrayExprent.class, "hardType");
  private static final Field VARIABLE_TYPE = field(VarExprent.class, "varType");
  private static final Field VARIABLE_BOUND = field(VarExprent.class, "boundType");
  private static final Field CONSTANT_CONDY = field(ConstExprent.class, "wasCondy");
  private static final Field FIELD_CONDY = field(FieldExprent.class, "wasCondy");
  private static final Field FIELD_QUALIFIED = field(FieldExprent.class, "forceQualified");
  private static final Field INVOCATION_LAZY_CONDY = field(InvocationExprent.class, "wasLazyCondy");
  private static final Field FUNCTION_IMPLICIT_TYPE = field(FunctionExprent.class, "implicitType");
  private static final Field ASSERT_PARAMETERS = field(AssertExprent.class, "parameters");

  // Record shared nodes once and keep references by the upstream expression ID.
  private final Map<Integer, Exprent> nodes = new TreeMap<>();
  private final boolean enhanced;
  private final boolean secondary;

  private ExpressionSnapshot(boolean enhanced, boolean secondary) {
    this.enhanced = enhanced;
    this.secondary = secondary;
  }

  static String snapshot(RootStatement root, CounterContainer counters) {
    return snapshot(root, counters, false, false);
  }

  static String snapshot(RootStatement root, CounterContainer counters, boolean enhanced, boolean secondary) {
    try {
      return new ExpressionSnapshot(enhanced, secondary).describe(root, counters);
    } catch (RuntimeException | AssertionError | StackOverflowError failure) {
      return "snapshot-error=" + text(failure.toString());
    }
  }

  private String describe(RootStatement root, CounterContainer counters) {
    StringJoiner fields = new StringJoiner(";");
    fields.add("counters=" + counters.getCounter(CounterContainer.STATEMENT_COUNTER)
      + "," + counters.getCounter(CounterContainer.EXPRESSION_COUNTER)
      + "," + counters.getCounter(CounterContainer.VAR_COUNTER));

    Deque<Statement> pending = new ArrayDeque<>();
    pending.add(root);
    pending.add(root.getDummyExit());
    while (!pending.isEmpty()) {
      Statement statement = pending.removeFirst();
      fields.add("body" + statement.id + "=" + expressions(statement.getExprents()));
      if (enhanced) {
        fields.add("definitions" + statement.id + "=" + expressions(statement.getVarDefinitions()));
      }
      if (enhanced && statement instanceof DoStatement loop) {
        fields.add("loop" + statement.id + "=" + expression(loop.getInitExprent()) + ","
          + expression(loop.getConditionExprent()) + "," + expression(loop.getIncExprent()));
        if (loop.getLooptype() == DoStatement.Type.FOR_EACH) {
          String source = loop.getIncExprent().getExprType().arrayDim > 0 ? "array" : "iterator";
          fields.add("foreach" + statement.id + "=" + source);
        }
      } else if (statement instanceof IfStatement branch) {
        fields.add("head" + statement.id + "=" + expressions(branch.getHeadexprentList()));
        fields.add("pattern" + statement.id + "=" + branch.isPatternMatched());
        fields.add("ppmm" + statement.id + "=" + branch.hasPPMM());
      } else if (statement instanceof SwitchStatement branch) {
        fields.add("head" + statement.id + "=" + expressions(branch.getHeadexprentList()));
        boolean linked = branch.getHeadexprent() instanceof SwitchHeadExprent head
          && head.getCaseValues() == branch.getCaseValues();
        fields.add("cases" + statement.id + "=" + cases(branch.getCaseValues()) + "|" + linked);
      } else if (statement instanceof SynchronizedStatement sync) {
        fields.add("head" + statement.id + "=" + expressions(sync.getHeadexprentList()));
      } else if (statement instanceof CatchStatement caught) {
        fields.add("catch" + statement.id + "=" + expressions(caught.getVars()));
      } else if (statement instanceof CatchAllStatement caught) {
        fields.add("catch" + statement.id + "=" + expressions(caught.getVars()) + "|" + expression(caught.getMonitor()));
      }
      for (int i = statement.getStats().size() - 1; i >= 0; i--) {
        pending.addFirst(statement.getStats().get(i));
      }
    }
    for (Exprent e : nodes.values()) {
      fields.add("e" + e.id + "=" + e.type.name() + "|" + type(e.getExprType()) + "|"
        + offsets(e.bytecode) + "|" + operands(e));
    }
    return fields.toString();
  }

  private String expression(Exprent expr) {
    if (expr == null) {
      return "~";
    }
    Exprent previous = nodes.putIfAbsent(expr.id, expr);
    if (previous == null) {
      expressions(expr.getAllExprents());
      if (expr instanceof SwitchHeadExprent head) {
        cases(head.getCaseValues());
      } else if (expr instanceof NewExprent allocation) {
        expression(allocation.getConstructor());
      }
    } else if (previous != expr) {
      throw new AssertionError("duplicate expression ID " + expr.id);
    }
    return Integer.toString(expr.id);
  }

  private String expressions(List<? extends Exprent> exprs) {
    return exprs == null ? "~" : exprs.stream().map(this::expression).collect(Collectors.joining(","));
  }

  private String cases(List<List<Exprent>> cases) {
    return cases.stream().map(this::expressions).collect(Collectors.joining("/", "[", "]"));
  }

  private String operands(Exprent e) {
    if (e instanceof VarExprent var) {
      String fields = parts(var.getIndex(), var.getVersion(), var.isStack(), var.isCatchTempVar(),
        type((VarType) read(VARIABLE_TYPE, var)), lvt(var.getLVT()), instruction(var.getBackingInstr()),
        var.isEffectivelyFinal());
      return enhanced ? fields + "|" + type((VarType) read(VARIABLE_BOUND, var)) : fields;
    }
    if (e instanceof ConstExprent constant) {
      return parts(value(constant.getValue()), constant.isBoolPermitted(), read(CONSTANT_CONDY, constant));
    }
    if (e instanceof AssignmentExprent assign) {
      return parts(expression(assign.getLeft()), expression(assign.getRight()), enumName(assign.getCondType()));
    }
    if (e instanceof ArrayExprent array) {
      return parts(expression(array.getArray()), expression(array.getIndex()), type((VarType) read(ARRAY_HARD_TYPE, array)));
    }
    if (e instanceof FieldExprent field) {
      return parts(text(field.getName()), text(field.getClassname()), field.isStatic(),
        expression(field.getInstance()), text(field.getDescriptor().descriptorString),
        read(FIELD_QUALIFIED, field), read(FIELD_CONDY, field));
    }
    if (e instanceof InvocationExprent invocation) {
      List<PooledConstant> arguments = invocation.getBootstrapArguments();
      String fields = parts(invocation.getInvocationType().name(), invocation.getFunctype().name(),
        text(invocation.getName()), text(invocation.getClassname()), invocation.isStatic(),
        expression(invocation.getInstance()), text(invocation.getStringDescriptor()),
        descriptor(invocation.getDescriptor()), text(invocation.getInvokeDynamicClassSuffix()),
        expressions(invocation.getLstParameters()), constant(invocation.getBootstrapMethod()),
        arguments == null ? "~" : arguments.stream().map(ExpressionSnapshot::constant).collect(Collectors.joining("/")),
        invocation.isSyntheticNullCheck(), read(INVOCATION_LAZY_CONDY, invocation));
      return secondary ? fields + "|" + invocation.shouldForceBoxing() : fields;
    }
    if (e instanceof FunctionExprent function) {
      String fields = parts(function.getFuncType().name(), expressions(function.getLstOperands()),
        type((VarType) read(FUNCTION_IMPLICIT_TYPE, function)));
      return secondary ? fields + "|" + function.doesCast() : fields;
    }
    if (e instanceof NewExprent allocation) {
      return parts(type(allocation.getNewType()), expressions(allocation.getLstDims()),
        expression(allocation.getConstructor()), expressions(allocation.getLstArrayElements()),
        allocation.isAnonymous(), allocation.isLambda(), allocation.isMethodReference(), allocation.isDirectArrayInit());
    }
    if (e instanceof ExitExprent exit) {
      return parts(exit.getExitType().name(), expression(exit.getValue()), type(exit.getRetType()),
        descriptor(exit.getMethodDescriptor()));
    }
    if (e instanceof AssertExprent assertion) {
      List<?> parameters = (List<?>) read(ASSERT_PARAMETERS, assertion);
      return parts(expression((Exprent) parameters.get(0)),
        expression(parameters.size() > 1 ? (Exprent) parameters.get(1) : null));
    }
    if (e instanceof MonitorExprent monitor) {
      return parts(monitor.getMonType().name(), expression(monitor.getValue()), monitor.isRemovable());
    }
    if (e instanceof IfExprent branch) {
      return expression(branch.getCondition());
    }
    if (e instanceof SwitchHeadExprent branch) {
      return parts(expression(branch.getValue()), cases(branch.getCaseValues()));
    }
    throw new AssertionError("unexpected expression kind " + e.type);
  }

  private static String offsets(BitSet offsets) {
    return offsets == null ? "~" : offsets.stream().mapToObj(Integer::toString).collect(Collectors.joining(","));
  }

  static String type(VarType type) {
    if (type == null) {
      return "~";
    }
    String base = type.type.ordinal() + "," + type.arrayDim + "," + text(type.value)
      + "," + type.typeFamily.ordinal() + "," + type.stackSize;
    if (type instanceof GenericType generic) {
      return base + "<" + generic.getWildcard() + "," + type(generic.getParent()) + ","
        + generic.getArguments().stream().map(ExpressionSnapshot::type).collect(Collectors.joining("/")) + ">";
    }
    return base;
  }

  private static String descriptor(MethodDescriptor descriptor) {
    return text(descriptor.toString()) + "@" + type(descriptor.ret) + "@"
      + types(java.util.Arrays.asList(descriptor.params)) + "@" + genericDescriptor(descriptor.genericInfo);
  }

  private static String genericDescriptor(GenericMethodDescriptor generic) {
    if (generic == null) {
      return "~";
    }
    return generic.typeParameters.stream().map(ExpressionSnapshot::text).collect(Collectors.joining("/")) + "@"
      + generic.typeParameterBounds.stream().map(ExpressionSnapshot::types).collect(Collectors.joining("|")) + "@"
      + types(generic.parameterTypes) + "@" + type(generic.returnType) + "@" + types(generic.exceptionTypes);
  }

  private static String types(List<VarType> types) {
    return types.stream().map(ExpressionSnapshot::type).collect(Collectors.joining("/"));
  }

  private static String lvt(LocalVariable local) {
    return local == null ? "~" : local.getVersion().var + "," + local.getVersion().version + ","
      + local.getStart() + "," + local.getEnd() + "," + text(local.getName())
      + "," + text(local.getDescriptor()) + "," + text(local.getSignature());
  }

  private static String instruction(Instruction insn) {
    return insn == null ? "~" : insn.opcode + "," + insn.wide + "," + insn.group
      + "," + insn.startOffset + "," + insn.length + ","
      + IntStream.range(0, insn.operandsCount()).mapToObj(i -> Integer.toString(insn.operand(i))).collect(Collectors.joining(","));
  }

  private static String constant(PooledConstant constant) {
    if (constant == null) {
      return "~";
    }
    if (constant instanceof PrimitiveConstant p) {
      return "p," + p.type + "," + p.index + "," + p.isArray + "," + value(p.value);
    }
    if (constant instanceof LinkConstant l) {
      return "l," + l.type + "," + l.index1 + "," + l.index2 + "," + text(l.classname)
        + "," + text(l.elementname) + "," + text(l.descriptor);
    }
    throw new AssertionError("unexpected constant kind " + constant.type);
  }

  private static String value(Object value) {
    if (value == null) {
      return "~";
    }
    if (value instanceof Integer) {
      return "i" + value;
    }
    if (value instanceof Long) {
      return "j" + value;
    }
    if (value instanceof Float f) {
      return "f" + Integer.toHexString(Float.floatToRawIntBits(f));
    }
    if (value instanceof Double d) {
      return "d" + Long.toHexString(Double.doubleToRawLongBits(d));
    }
    if (value instanceof String s) {
      return "s" + text(s);
    }
    throw new AssertionError("unexpected constant value " + value.getClass());
  }

  // Escape UTF-16 units directly so the protocol preserves even isolated surrogates.
  static String text(String text) {
    if (text == null) {
      return "~";
    }
    StringBuilder escaped = new StringBuilder();
    for (int i = 0; i < text.length(); i++) {
      char c = text.charAt(i);
      if (c < 0x20 || c > 0x7e || "|;,/%~@<>".indexOf(c) >= 0) {
        escaped.append('%').append(Integer.toHexString(c | 0x10000).substring(1));
      } else {
        escaped.append(c);
      }
    }
    return escaped.toString();
  }

  private static String parts(Object... fields) {
    StringJoiner result = new StringJoiner("|");
    for (Object field : fields) {
      result.add(field.toString());
    }
    return result.toString();
  }

  private static String enumName(Enum<?> field) {
    return field == null ? "~" : field.name();
  }

  private static Field field(Class<?> owner, String name) {
    try {
      Field field = owner.getDeclaredField(name);
      field.setAccessible(true);
      return field;
    } catch (ReflectiveOperationException failure) {
      throw new AssertionError(failure);
    }
  }

  private static Object read(Field field, Object owner) {
    try {
      return field.get(owner);
    } catch (IllegalAccessException failure) {
      throw new AssertionError(failure);
    }
  }
}
