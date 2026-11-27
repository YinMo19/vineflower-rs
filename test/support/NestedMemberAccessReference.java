import java.nio.file.Files;
import java.nio.file.Path;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import java.lang.reflect.Field;
import java.util.*;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.rels.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.flow.*;
import org.jetbrains.java.decompiler.modules.decompiler.vars.*;

class NestedMemberAccessReference {
  static Field names;
  static {
    try {
      names = VarProcessor.class.getDeclaredField("mapVarNames");
      names.setAccessible(true);
    } catch (ReflectiveOperationException e) { throw new ExceptionInInitializerError(e); }
  }

  static String expr(Exprent e, IdentityHashMap<Exprent,Integer> aliases) {
    var known = aliases.get(e);
    if (known != null) return "@" + known;
    int index = aliases.size();
    aliases.put(e,index);
    String data = e.type.toString();
    if (e instanceof FieldExprent f) data += ":" + f.getClassname() + "." + f.getName() + f.getDescriptor().descriptorString + ":" + f.isStatic();
    else if (e instanceof InvocationExprent i) data += ":" + i.getClassname() + "." + i.getName() + i.getStringDescriptor() + ":" + i.isStatic();
    else if (e instanceof FunctionExprent f) data += ":" + f.getFuncType();
    else if (e instanceof VarExprent v) data += ":" + v.getIndex() + "," + v.getVersion();
    else if (e instanceof ExitExprent x) data += ":" + x.getExitType();
    else if (e instanceof ConstExprent c) data += ":" + c.getValue();
    var children = new ArrayList<String>();
    for (Exprent child : e.getAllExprents()) children.add(expr(child, aliases));
    return index + "#" + e.id + "#" + data + "#" + e.bytecode + "[" + String.join("|", children) + "]";
  }

  static void dump(ClassesProcessor cp) throws Exception {
    for (var node : new TreeMap<>(cp.getMapRootClasses()).values()) {
      if (node.type == ClassesProcessor.ClassNode.Type.LAMBDA) continue;
      var wrapper = node.getWrapper();
      System.out.println(node.classStruct.qualifiedName + " hidden=" + new TreeSet<>(wrapper.getHiddenMembers()));
      for (var method : wrapper.getMethods()) {
        if (method.decompileError != null) throw new AssertionError(method.toString(), method.decompileError);
        if (method.root == null) continue;
        var vars = new TreeMap<String,String>();
        ((Map<VarVersionPair,String>)names.get(method.varproc)).forEach((pair,name) -> vars.put(pair.var+","+pair.version,name));
        var inherited = new TreeMap<String,String>();
        method.varproc.getInheritedNames().forEach((pair,name) -> inherited.put(pair.var+","+pair.version,name));
        var external = new TreeSet<String>();
        method.varproc.getExternalVars().forEach(pair -> external.add(pair.var+","+pair.version));
        var outer = new TreeSet<String>();
        method.setOuterVarNames.forEach(name -> outer.add(String.valueOf(name)));
        System.out.println(method.methodStruct.getName() + method.methodStruct.getDescriptor()
          + " counters=" + method.counter.getCounter(CounterContainer.EXPRESSION_COUNTER)
          + "," + method.counter.getCounter(CounterContainer.VAR_COUNTER)
          + " vars=" + vars + " outer=" + outer + " inherited=" + inherited + " external=" + external);
        var graph = method.getOrBuildGraph();
        var queue = new ArrayDeque<DirectNode>();
        var seen = Collections.newSetFromMap(new IdentityHashMap<DirectNode,Boolean>());
        var aliases = new IdentityHashMap<Exprent,Integer>();
        queue.add(graph.first);
        while (!queue.isEmpty()) {
          var current = queue.removeFirst();
          if (!seen.add(current)) continue;
          var expressions = new ArrayList<String>();
          for (var e : current.exprents) expressions.add(expr(e, aliases));
          System.out.println(current.id + " " + String.join(";",expressions));
          for (var edge : current.getSuccessors(DirectEdgeType.REGULAR)) queue.add(edge.getDestination());
        }
      }
    }
  }

  public static void main(String[] args) throws Exception {
    Path scratch = Path.of(args[0]);
    Path access = Files.writeString(scratch.resolve("AccessSubject.java"), """
      public class AccessSubject {
        private int instance;
        private static int shared;
        private int call(int v) { return instance + v; }
        private static long wide(long a, double b, int c) { return a + (long)b * c; }

        static int sameOwner(AccessSubject x) { return sourceFacade(x); }
        static int sourceFacade(AccessSubject x) { return x.instance; }
        static int combined(int a, int b) { return a * 10 + b; }
        int rootToNested(AccessSubject value) { return ZBridge.privateForward(value); }

        class Member {
          int ownerAccess() { return AccessSubject.this.instance; }
          void ownerSet(int v) { AccessSubject.this.instance = v; }
          private int memberPrivate() { return AccessSubject.this.instance; }
        }

        static class AConsumer {
          int get(AccessSubject x) { return x.instance + AccessSubject.shared; }
          int set(AccessSubject x, int v) { return (x.instance = v) + (AccessSubject.shared = v); }
          int post(AccessSubject x) { return x.instance++ + AccessSubject.shared--; }
          int pre(AccessSubject x) { return --x.instance + ++AccessSubject.shared; }
          int invoke(AccessSubject x, int v) { return x.call(v); }
          long invokeWide(long a, double b, int c) { return AccessSubject.wide(a, b, c); }
          int member(Member m) { return m.memberPrivate(); }
          int nested(AccessSubject x) { return combined(ZBridge.forward(x), ZBridge.forward(x)); }
          int reordered(AccessSubject x, int a, int b) { return ZBridge.reordered(x, a, b); }
        }

        static class ZBridge {
          static int forward(AccessSubject x) { return x.instance; }
          private static int privateForward(AccessSubject x) { return x.instance; }
          static int reordered(AccessSubject x, int a, int b) { return combined(b, a); }
        }
      }
      """);
    Path alias = Files.writeString(scratch.resolve("AliasSubject.java"), """
      public class AliasSubject {
        static int copyAlias(int captured) {
          class Local {
            private final int value$;
            Local(int explicit) { this.value$ = explicit; }
            static int alias(Local local) { return local.value$; }
          }
          Local instance = new Local(captured);
          return Local.alias(instance) + Local.alias(instance);
        }
      }
      """);
    for (String release : List.of("8", "17")) {
      Path classes = compile(scratch, access, "AccessSubject", release);
      for (String syntheticNotSet : List.of("0", "1")) {
        snapshot(classes, "AccessSubject", release, syntheticNotSet);
      }
    }
    snapshot(compile(scratch, alias, "AliasSubject", "17"), "AliasSubject", "17", "1");
  }

  static Path compile(Path scratch, Path source, String subject, String release) throws Exception {
    Path classes = Files.createDirectory(scratch.resolve(subject + "-" + release));
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "-g", "-parameters",
        "--release", release, "-d", classes.toString(), source.toString()) != 0) {
      throw new AssertionError("javac failed");
    }
    return classes;
  }

  static void snapshot(Path fixture, String subject, String release, String syntheticNotSet) throws Exception {
    System.out.println(subject + " " + release + " " + syntheticNotSet);
    var engine = new Fernflower(null, Map.of("__unit_test_mode__", "1", "include-runtime", "1",
      "synthetic-not-set", syntheticNotSet), IFernflowerLogger.NO_OP);
    engine.addSource(fixture.toFile());
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    var root = processor.getMapRootClasses().get(subject);
    processor.processClass(root.classStruct);
    dump(processor);
  }
}
