// SPDX-License-Identifier: Apache-2.0

import java.util.Comparator;
import java.util.Map;
import java.util.StringJoiner;
import java.util.function.Function;

import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;

class VariableSnapshot {
  private static final Comparator<VarVersionPair> VERSION_ORDER = Comparator
    .comparingInt((VarVersionPair pair) -> pair.var)
    .thenComparingInt(pair -> pair.version);

  static String snapshot(VarProcessor vars) {
    var versions = vars.getVarVersions();
    var types = versions.getTypeProcessor();
    var result = new StringJoiner(";");
    result.add("versions=");
    bounds(result, "lower", types.getLowerBounds(), ExpressionSnapshot::type);
    bounds(result, "upper", types.getUpperBounds(), ExpressionSnapshot::type);
    bounds(result, "final", types.getMapFinalVars(), type -> type.name());
    versions.getMapOriginalVarIndices().entrySet().stream().sorted(Map.Entry.comparingByKey())
      .forEach(entry -> result.add("original" + entry.getKey() + "=" + pair(entry.getValue())));
    return result.toString();
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
