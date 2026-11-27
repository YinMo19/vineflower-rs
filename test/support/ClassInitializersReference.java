import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.util.TextBuffer;

class ClassInitializersReference {
  private static final Field QUALIFIED;
  static {
    try {
      QUALIFIED = FieldExprent.class.getDeclaredField("forceQualified");
      QUALIFIED.setAccessible(true);
    } catch (ReflectiveOperationException error) {
      throw new ExceptionInInitializerError(error);
    }
  }

  private static String shape(Exprent expression) throws IllegalAccessException {
    List<String> parts = new ArrayList<>();
    for (Exprent expr : expression.getAllExprents(true, true)) {
      if (expr instanceof FieldExprent field) {
        parts.add("field " + field.getClassname() + "." + field.getName()
          + (QUALIFIED.getBoolean(field) ? " qualified" : ""));
      } else if (expr instanceof InvocationExprent invocation) {
        parts.add("call " + invocation.getClassname() + "." + invocation.getName() + invocation.getStringDescriptor());
      } else if (expr instanceof FunctionExprent function) {
        parts.add(function.getFuncType().name());
      } else if (expr instanceof ConstExprent constant) {
        parts.add("constant " + constant.getValue());
      } else if (expr instanceof NewExprent allocation && allocation.isLambda()) {
        parts.add("lambda");
      } else if (expr instanceof AssignmentExprent) {
        parts.add("assignment");
      }
    }
    return String.join("; ", parts);
  }

  private static void dumpBody(Statement stat, String method) throws Exception {
    if (stat.getExprents() != null) {
      for (Exprent expr : stat.getExprents()) {
        System.out.println("body\t" + method + "\t" + shape(expr));
      }
    }
    for (Statement child : stat.getStats()) dumpBody(child, method);
  }

  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var source = Files.writeString(scratch.resolve("InitializerSubject.java"), """
      import java.util.function.IntSupplier;

      class InitializerSubject {
        static int before = InitializerSubject.later;
        static IntSupplier queued = () -> InitializerSubject.later;
        static int later = compute();
        static int duplicate;
        static int unsafe;
        static {
          sideEffect();
          duplicate = 1;
          duplicate = 2;
          unsafe = duplicate + 3;
        }

        final Object object = Boolean.TRUE;
        final boolean unboxed = (Boolean)object;
        int first = later + 1;
        int second = first + 1;
        int argument;

        InitializerSubject() { this(42); }
        InitializerSubject(int value) { argument = value; }
        InitializerSubject(String value) { argument = value.length(); }

        static int compute() { return (int)System.nanoTime(); }
        static void sideEffect() { System.out.println("effect"); }
      }
      """);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    int status = ToolProvider.getSystemJavaCompiler().run(null, null, null,
      "--release", "17", "-g", "-d", classes.toString(), source.toString());
    if (status != 0) throw new AssertionError("javac exit " + status);

    var engine = new Fernflower(null, Map.of("include-runtime", "1", "thread-count", "1"), IFernflowerLogger.NO_OP);
    engine.addSource(classes.toFile());
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    var node = processor.getMapRootClasses().get("InitializerSubject");
    processor.processClass(node.classStruct);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS, node.classStruct);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_WRAPPER, node.getWrapper());

    var prepare = ClassWriter.class.getDeclaredMethod("invokeProcessors", TextBuffer.class, ClassNode.class);
    prepare.setAccessible(true);
    var buffer = new TextBuffer();
    if (!Boolean.TRUE.equals(prepare.invoke(null, buffer, node))) {
      throw new AssertionError(buffer.convertToStringAndAllowDataDiscard());
    }
    buffer.convertToStringAndAllowDataDiscard();

    var wrapper = node.getWrapper();
    for (var pair : List.of(Map.entry("static", wrapper.getStaticFieldInitializers()),
                            Map.entry("dynamic", wrapper.getDynamicFieldInitializers()))) {
      var table = pair.getValue();
      for (int i = 0; i < table.size(); i++) {
        System.out.println(pair.getKey() + "\t" + table.getLstKeys().get(i) + "\t" + shape(table.get(i)));
      }
    }
    for (var method : wrapper.getMethods()) {
      var name = method.methodStruct.getName();
      if (name.equals("<init>") || name.equals("<clinit>") || name.startsWith("lambda$")) {
        if (method.decompileError != null) throw new AssertionError(method.decompileError);
        dumpBody(method.root, name + method.methodStruct.getDescriptor());
      }
    }
  }
}
