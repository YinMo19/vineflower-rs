// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import javax.tools.ToolProvider;
import java.util.*;
import java.lang.reflect.Field;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.extern.*;
import org.jetbrains.java.decompiler.main.rels.*;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.modules.decompiler.stats.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.struct.gen.VarType;
import org.jetbrains.java.decompiler.struct.gen.generics.GenericType;

class GenericChainsReference {
  static Object get(Object obj, Class<?> owner, String name) throws Exception {
    Field field = owner.getDeclaredField(name);
    field.setAccessible(true);
    return field.get(obj);
  }

  static String type(VarType t) {
    if (t == null) return "-";
    int wild = GenericType.WILDCARD_NO;
    String parent = "-";
    List<String> args = new ArrayList<>();
    if (t instanceof GenericType gen) {
      wild = gen.getWildcard();
      parent = type(gen.getParent());
      for (var arg : gen.getArguments()) args.add(type(arg));
    }
    return t.type.name() + "/" + t.arrayDim + "/" + (t.value == null ? "-" : t.value)
        + "/" + wild + "/" + parent + "[" + String.join(",", args) + "]";
  }

  static void expression(Exprent e, Set<Exprent> seen, List<String> rows) throws Exception {
    if (!seen.add(e)) return;
    if (e instanceof InvocationExprent i) {
      StructMethod desc = (StructMethod)get(i, InvocationExprent.class, "desc");
      List<String> args = i.getGenericArgs().stream().map(GenericChainsReference::type).toList();
      List<String> map = new ArrayList<>();
      i.getGenericsMap().forEach((key, value) -> map.add(type(key) + "=" + type(value)));
      Collections.sort(map);
      boolean instance = (boolean)get(i, InvocationExprent.class, "isInvocationInstance");
      VarType remapped = (VarType)get(i, InvocationExprent.class, "remappedInstType");
      Object boxing = get(i, InvocationExprent.class, "boxing");
      boolean keep = (boolean)get(boxing, boxing.getClass(), "keepCast");
      if (desc != null || !args.isEmpty() || !map.isEmpty() || instance
        || i.forceGenericQualfication || remapped != null || keep) {
        String selected = desc == null ? "-" : desc.getClassQualifiedName() + "." + desc.getName() + desc.getDescriptor();
        rows.add("call\t" + i.getClassname() + "." + i.getName() + i.getStringDescriptor() + "\t"
            + selected + "\t" + instance + "\t" + i.forceGenericQualfication + "\t" + keep + "\t"
            + type(remapped) + "\t" + String.join(";", args) + "\t" + String.join(";", map));
      }
    } else if (e instanceof NewExprent n) {
      VarType lambda = (VarType)get(n, NewExprent.class, "inferredLambdaType");
      var args = ((List<VarType>)get(n, NewExprent.class, "genericArgs")).stream().map(GenericChainsReference::type).toList();
      if (lambda != null || !args.isEmpty()) {
        rows.add("new\t" + n.getNewType().value + "\t" + type(lambda) + "\t" + String.join(";", args));
      }
    }
    for (var child : e.getAllExprents()) expression(child, seen, rows);
  }

  static void statement(Statement stat, Set<Exprent> seen, List<String> rows) throws Exception {
    if (stat.getExprents() != null) {
      for (var expr : stat.getExprents()) expression(expr, seen, rows);
    }
    for (var child : stat.getStats()) statement(child, seen, rows);
  }

  public static void main(String[] args) throws Exception {
    Path scratch = Path.of(args[0]);
    Path fixture = Files.createDirectory(scratch.resolve("classes"));
    Path source = Files.writeString(scratch.resolve("ChainSubject.java"), """
      import java.util.Comparator;
      import java.util.function.Function;

      public class ChainSubject {
        static int key(String s) { return s.length(); }
        static int key(int i) { return i; }
        static int unique(String s) { return s.length(); }

        static Comparator<String> directLambda() {
          return Comparator.comparing((String s) -> s.length()).thenComparing(s -> s);
        }
        static Comparator<String> overloadedReference() {
          return Comparator.<String, Integer>comparing(ChainSubject::key).thenComparing(s -> s);
        }
        static Comparator<String> uniqueReference() {
          return Comparator.comparing(ChainSubject::unique).thenComparing(s -> s);
        }
        static Comparator<String> externalOverload() {
          return Comparator.<String, Integer>comparing(Integer::valueOf).thenComparing(s -> s);
        }
        static int unsuitableReturn() {
          return Comparator.comparing((String s) -> s.length()).compare("a", "b");
        }
        static Comparator<String> classGenericOnly() {
          return Comparator.comparing((String s) -> s.length()).reversed();
        }
        public static class Base<X> {
          public <T> Base<X> then(Function<? super X, ? extends T> f) { return this; }
          public Object unsignedStep() { return this; }
          public static <T> Derived begin(Function<T, String> f) { return new Derived(); }
        }
        public static class Derived extends Base<String> {}
        static Object plainIntermediate() {
          return Derived.begin((String s) -> s).unsignedStep();
        }
        public static class GenericOwner<T> {
          private final java.util.List<T> seed;
          GenericOwner(java.util.List<T> seed) { this.seed = seed; }
          public static <T> Base<T> start(java.util.List<T> seed, Function<T, String> f) { return new Base<>(); }
          Base<T> sameFormal() {
            return start(seed, s -> s.toString()).then(s -> s);
          }
        }
        static Base<String> inheritedOwner() {
          return Derived.begin((String s) -> s).then(String::length);
        }
      }
      """);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "-g", "-parameters",
        "--release", "17", "-d", fixture.toString(), source.toString()) != 0) {
      throw new AssertionError("javac failed");
    }
    for (var explicit : List.of("0", "1")) {
      snapshot(fixture, explicit);
    }
  }

  private static void snapshot(Path fixture, String explicit) throws Exception {
    System.out.println("explicit=" + explicit);
    var engine = new Fernflower(null, Map.of(
      IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "1",
      IFernflowerPreferences.EXPLICIT_GENERIC_ARGUMENTS, explicit,
      IFernflowerPreferences.UNIT_TEST_MODE, "1"), IFernflowerLogger.NO_OP);
    engine.addSource(fixture.toFile());
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    var root = processor.getMapRootClasses().get("ChainSubject");
    DecompilerContext.startClass(new ImportCollector(root));
    new LambdaProcessor().processClass(root);
    var init = ClassesProcessor.class.getDeclaredMethod("initWrappers", ClassesProcessor.ClassNode.class, LanguageSpec.class);
    init.setAccessible(true);
    init.invoke(null, root, null);
    for (var node : new TreeMap<>(processor.getMapRootClasses()).values()) {
      if (node.type == ClassesProcessor.ClassNode.Type.LAMBDA) continue;
      for (var method : node.getWrapper().getMethods()) {
        if (method.decompileError != null) throw new Error(method.methodStruct.getName(), method.decompileError);
        if (method.root == null) continue;
        List<String> rows = new ArrayList<>();
        statement(method.root, Collections.newSetFromMap(new IdentityHashMap<>()), rows);
        for (String row : rows) System.out.println(node.classStruct.qualifiedName + "." + method.methodStruct.getName()
          + method.methodStruct.getDescriptor() + "\t" + row);
      }
    }
  }
}
