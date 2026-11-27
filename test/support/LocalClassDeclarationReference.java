import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.Map;
import java.util.TreeMap;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.main.rels.NestedClassProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;

class LocalClassDeclarationReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("DeclarationHost.java"), """
      import java.util.List;
      import java.util.Collections;

      class DeclarationHost {
        static void missing() { class Missing {} }
        static void effect(int n) {}
        static void use(Object var) {}

        static void shared(boolean condition) {
          class Common {}
          effect(101);
          if (condition) use(new Common());
          else use(Common.class);
          effect(102);
        }

        static void narrow(boolean condition) {
          if (condition) {
            class Narrow {}
            effect(201);
            use(new Narrow());
          }
          effect(202);
        }

        static void unused() {
          class Unused {}
          effect(301);
        }

        static void lambda() {
          class AfterLambda {}
          effect(401);
          Runnable unrelated = () -> effect(402);
          unrelated.run();
          effect(403);
          use(new AfterLambda());
        }

        static void fields() {
          class Owner { static int field = 7; }
          effect(501);
          use(Owner.field);
        }

        static void loop(boolean enabled) {
          class Loop {
            int count;
            boolean more() { return count < 2; }
          }
          effect(601);
          for (Loop value = new Loop(); enabled && value.more(); ++value.count) {
            effect(value.count);
          }
          effect(602);
        }

        static void generic(boolean condition) {
          class Element {}
          effect(701);
          List<? extends Element> list;
          if (condition) {
            list = Collections.emptyList();
            effect(702);
          } else {
            list = Collections.singletonList(null);
            effect(703);
          }
          use(list);
        }

        static void arrays(boolean condition) {
          class Entry {}
          effect(801);
          Entry[] array;
          if (condition) {
            array = null;
            effect(802);
          } else {
            array = new Entry[1];
            effect(803);
          }
          use(array);
        }
      }
      """);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17", "-g", "-parameters",
      "-d", classes.toString(), source.toString()) != 0) throw new AssertionError("javac failed");
    var rootField = MethodWrapper.class.getDeclaredField("root");
    rootField.setAccessible(true);
    for (String debug : new String[]{"0", "1"}) {
      System.out.println("debug=" + debug);
      var cp = WrapperStages.initialize(classes, "DeclarationHost", Map.of(
        "__unit_test_mode__", "1", "include-runtime", "0", "use-lvt-names", debug));
      var root = cp.getMapRootClasses().get("DeclarationHost");
      var wrappers = root.getWrapper().getMethods();
      var missing = wrappers.getWithKey("missing ()V");
      rootField.set(missing, null);
      var localClasses = new TreeMap<String, ClassNode>();
      for (var pair : cp.getMapRootClasses().entrySet()) {
        if (pair.getValue().type == ClassNode.Type.LOCAL) localClasses.put(pair.getKey(), pair.getValue());
      }
      var originalSlots = new TreeMap<String, Integer>();
      for (var pair : localClasses.entrySet()) {
        var wrapper = wrappers.getWithKey(pair.getValue().enclosingMethod);
        originalSlots.put(pair.getKey(), wrapper.counter.getCounter(CounterContainer.VAR_COUNTER));
      }
      new NestedClassProcessor().processClass(root, root);
      for (var pair : localClasses.entrySet()) {
        var child = pair.getValue();
        var wrapper = wrappers.getWithKey(child.enclosingMethod);
        if (wrapper == missing) {
          System.out.println("missing|" + wrapper.addErrorComment + "|" + String.join("/", wrapper.commentLines));
          continue;
        }
        if (wrapper.root == null) throw new AssertionError(wrapper.methodStruct.toString(), wrapper.decompileError);
        int local = originalSlots.get(pair.getKey());
        int newCount = wrapper.counter.getCounter(CounterContainer.VAR_COUNTER);
        var queue = new ArrayDeque<Statement>();
        queue.add(wrapper.root);
        while (!queue.isEmpty()) {
          var stat = queue.remove();
          for (boolean body : new boolean[]{false, true}) {
            var exprs = body ? stat.getExprents() : stat.getVarDefinitions();
            if (exprs == null) continue;
            for (int i = 0; i < exprs.size(); ++i) {
              if (!(exprs.get(i) instanceof VarExprent expr) || !expr.isClassDef() || !child.classStruct.qualifiedName.equals(expr.getVarType().value)) continue;
              if (expr.getIndex() != local || expr.getVersion() != 0) throw new AssertionError("unexpected variable");
              var copy = (VarExprent)expr.copy();
              System.out.printf("%s|%s|%s|%d|%s|%d/%d|%d|%d|%d|%d|%d|%b|%b|%b|%b|%b|%b|%b%n",
                pair.getKey(), wrapper.methodStruct.getName(), stat.type, stat.id, body ? "body" : "defs",
                i, exprs.size(), i == 0 ? -1 : exprs.get(i - 1).id, i + 1 == exprs.size() ? -1 : exprs.get(i + 1).id,
                local, newCount, expr.id, expr.isDefinition(), expr.isClassDef(), expr.getProcessor() == wrapper.varproc,
                expr.getLVT() == null, expr.bytecode == null, copy.isDefinition(), copy.isClassDef());
            }
          }
          queue.addAll(stat.getStats());
        }
      }
    }
  }
}
