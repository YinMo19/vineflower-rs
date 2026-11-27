import java.lang.reflect.Field;
import java.util.Comparator;
import java.util.Map;
import java.util.StringJoiner;
import java.util.function.Function;

import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;

class VariableSnapshot {
  private static final Comparator<VarVersionPair> VERSION_ORDER = Comparator
    .comparingInt((VarVersionPair pair) -> pair.var)
    .thenComparingInt(pair -> pair.version);
  private static final Field VAR_NAMES = ExpressionSnapshot.field(VarProcessor.class, "mapVarNames");
  private static final Field LOCAL_VARIABLES = ExpressionSnapshot.field(VarProcessor.class, "mapVarLVTs");
  private static final Field CLASHING_NAMES = ExpressionSnapshot.field(VarProcessor.class, "clashingNames");

  static String snapshot(VarProcessor vars) {
    return snapshot(vars, false);
  }

  static String snapshot(VarProcessor vars, boolean definitions) {
    var versions = vars.getVarVersions();
    var types = versions.getTypeProcessor();
    var result = new StringJoiner(";");
    result.add("versions=");
    bounds(result, "lower", types.getLowerBounds(), ExpressionSnapshot::type);
    bounds(result, "upper", types.getUpperBounds(), ExpressionSnapshot::type);
    bounds(result, "final", types.getMapFinalVars(), type -> type.name());
    versions.getMapOriginalVarIndices().entrySet().stream().sorted(Map.Entry.comparingByKey())
      .forEach(entry -> result.add("original" + entry.getKey() + "=" + pair(entry.getValue())));
    if (definitions) {
      bounds(result, "name", VariableSnapshot.<String>bindings(VAR_NAMES, vars), ExpressionSnapshot::text);
      bounds(result, "this", vars.getThisVars(), ExpressionSnapshot::text);
      bounds(result, "local", VariableSnapshot.<LocalVariable>bindings(LOCAL_VARIABLES, vars), ExpressionSnapshot::lvt);
      bounds(result, "clash", VariableSnapshot.<String>bindings(CLASHING_NAMES, vars), ExpressionSnapshot::text);
    }
    return result.toString();
  }

  @SuppressWarnings("unchecked")
  private static <T> Map<VarVersionPair, T> bindings(Field field, VarProcessor vars) {
    return (Map<VarVersionPair, T>) ExpressionSnapshot.read(field, vars);
  }

  private static <T> void bounds(StringJoiner result, String name, Map<VarVersionPair, T> bindings,
                                 Function<T, String> value) {
    bindings.entrySet().stream().sorted(Map.Entry.comparingByKey(VERSION_ORDER))
      .forEach(entry -> result.add(name + pair(entry.getKey()) + "=" + value.apply(entry.getValue())));
  }

  private static String pair(VarVersionPair pair) {
    return pair.var + "," + pair.version;
  }
}
