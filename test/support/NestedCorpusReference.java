// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.rels.NestedClassProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;

class NestedCorpusReference {
  private static final Comparator<VarVersionPair> ORDER = Comparator.comparingInt((VarVersionPair v) -> v.var)
    .thenComparingInt(v -> v.version);

  public static void main(String[] args) throws Exception {
    for (String group : Files.readAllLines(Path.of(args[0]))) {
      var cp = WrapperStages.load(Path.of(group), Map.of("__unit_test_mode__","1","include-runtime","0"));
      var roots = new TreeMap<>(cp.getMapRootClasses());
      for (var root : roots.values()) {
        if (root.type != ClassNode.Type.ROOT || root.nested.isEmpty()
            && !root.classStruct.hasAttribute(org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute.ATTRIBUTE_BOOTSTRAP_METHODS)) continue;
        var rows = new ArrayList<String>();
        System.out.println("root " + group + " " + root.classStruct.qualifiedName);
        try {
          WrapperStages.initialize(cp, root);
        } catch (IllegalStateException e) {
          if (!e.getStackTrace()[0].getClassName().endsWith(".LambdaProcessor")) throw e;
          System.out.println("prepare error " + e.getMessage());
          continue;
        }
        new NestedClassProcessor().processClass(root, root);
        collect(root, rows);
        rows.forEach(System.out::println);
      }
    }
  }

  static void collect(ClassNode node, List<String> rows) {
    rows.add("class " + node.type + " " + node.simpleName + " " + node.enclosingMethod);
    if (node.type != ClassNode.Type.LAMBDA) {
      new TreeSet<>(node.getWrapper().getHiddenMembers()).forEach(key -> rows.add("hide " + key));
      if (node.superInvocation != null) rows.add("super " + node.superInvocation.id);
      new TreeMap<>(node.mapFieldsToVars).forEach((key,v) -> rows.add("field " + key + " " + pair(v)));
      for (var method : node.getWrapper().getMethods()) {
        rows.add("method " + method.methodStruct);
        if (method.root == null) {
          rows.add(method.decompileError == null ? "no code" : "failed");
          continue;
        }
        rows.add("counters " + method.counter.getCounter(CounterContainer.VAR_COUNTER) + " "
          + method.counter.getCounter(CounterContainer.EXPRESSION_COUNTER));
        if (method.synthParameters != null) rows.add("params " + String.join("/", method.synthParameters.stream().map(NestedCorpusReference::pair).toList()));
        var outer = new TreeSet<String>(Comparator.nullsFirst(Comparator.naturalOrder()));
        outer.addAll(method.setOuterVarNames);
        outer.forEach(name -> rows.add("outer " + name));
        var vars = method.varproc;
        if (vars.nestedProcessed) rows.add("lambda bindings");
        for (var version : vars.getUsedVarVersions().stream().sorted(ORDER).toList()) {
          var source = vars.getVarSource(version);
          rows.add("var " + pair(version) + " " + vars.getVarName(version) + " " + vars.getVarFinal(version)
            + " " + vars.getThisVars().get(version) + " " + vars.getInheritedNames().containsKey(version)
            + " " + vars.getExternalVars().contains(version)
            + " " + (source == null ? "-" : source.a + "@" + pair(source.b)) + " " + vars.getVarLVT(version));
        }
        expressions(method.root, vars, rows);
      }
    }
    for (var child : node.nested) collect(child, rows);
  }

  static void expressions(Statement stat, VarProcessor vars, List<String> rows) {
    var roots = new ArrayList<Exprent>(stat.getVarDefinitions());
    roots.addAll(stat.getExprents() == null ? stat.getStatExprents() : stat.getExprents());
    for (var expr : roots) {
      if (expr == null) continue;
      for (var sub : expr.getAllExprents(true, true)) {
        if (sub instanceof VarExprent var && (var.isClassDef() || vars.getExternalVars().contains(var.getVarVersionPair()))) {
          rows.add("use " + stat.id + " " + var.id + " " + pair(var.getVarVersionPair()) + " " + var.isClassDef()
            + " " + var.getVarType() + " " + var.getLVT());
        }
      }
    }
    for (var child : stat.getStats()) expressions(child, vars, rows);
  }

  static String pair(VarVersionPair pair) {
    return pair == null ? "-" : pair.var + "," + pair.version;
  }
}
