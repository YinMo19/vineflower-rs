import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.util.TextBuffer;

class MethodWriterReference {
  private static final List<String> ROOTS = List.of(
    "methodwriter/MethodSubject", "methodwriter/Face", "methodwriter/Base",
    "methodwriter/Defaults", "methodwriter/Value", "methodwriter/Empty", "methodwriter/Failure"
  );

  public static void main(String[] args) throws Exception {
    var classes = compile(Path.of(args[0]));
    for (int width : new int[]{52, 132}) {
      for (String className : ROOTS) {
        var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
          IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "1",
          IFernflowerPreferences.PREFERRED_LINE_LENGTH, Integer.toString(width),
          IFernflowerPreferences.REMOVE_BRIDGE, width == 52 ? "1" : "0",
          IFernflowerPreferences.REMOVE_SYNTHETIC, width == 52 ? "1" : "0",
          IFernflowerPreferences.USE_METHOD_PARAMETERS, width == 52 ? "1" : "0",
          IFernflowerPreferences.DUMP_EXCEPTION_ON_ERROR, "0",
          "variable-renaming", width == 52 ? "" : "jad",
          "rename-parameters", width == 52 ? "0" : "1"
        ), IFernflowerLogger.NO_OP);
        try {
          engine.addSource(classes.toFile());
          var processor = DecompilerContext.getClassProcessor();
          processor.loadClasses(null);
          var node = processor.getMapRootClasses().get(className);
          processor.processClass(node.classStruct);
          if (className.equals("methodwriter/Failure")) {
            node.getWrapper().getMethodWrapper("failed", "()Ljava/lang/String;").decompileError =
              new IllegalStateException("exercise method bytecode dump");
          }
          var buffer = new TextBuffer();
          new ClassWriter().writeClass(node, buffer, 0);
          WriterSnapshot.print(width, "class", className, buffer);
        } finally {
          engine.clearContext();
        }
      }
    }
  }

  private static Path compile(Path scratch) throws Exception {
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("MethodSubject.java"), """
      package methodwriter;

      import java.io.IOException;
      import java.lang.annotation.ElementType;
      import java.lang.annotation.Retention;
      import java.lang.annotation.RetentionPolicy;
      import java.lang.annotation.Target;
      import java.util.List;

      @Target(ElementType.TYPE_USE)
      @Retention(RetentionPolicy.RUNTIME)
      @interface TypeUse { String value(); }

      @Target({ElementType.TYPE_USE, ElementType.PARAMETER, ElementType.METHOD})
      @interface Both { String value(); }

      @interface Defaults {
        String label() default "café";
        byte level() default 3;
        Class<?>[] types() default {String.class, int.class};
        ElementType kind() default ElementType.METHOD;
        Class<? extends Number> numeric() default Long.class;
      }

      interface Face {
        default int increment(final int input) { return step(input); }
        private int step(int input) { return input + 1; }
        static boolean active() { return true; }
        long widen(long input, double weight);
      }

      abstract class Base<T> {
        T convert(T input) { return input; }
        protected abstract void supplies(int input, long wide, Object object);
      }

      public abstract class MethodSubject extends Base<Number> implements Face {
        protected MethodSubject() throws IOException { super(); }
        public MethodSubject(final long wide, String label) { super(); }

        @Deprecated
        @Both("return and method")
        public @TypeUse("result") Number convert(@Both("parameter and type") final Number input) {
          return input;
        }

        public abstract <E extends Exception, V extends Comparable<V>>
          List<@TypeUse("argument") V> checked(@TypeUse("error") E problem, V value) throws E, IOException;

        public abstract @TypeUse("return component") String @TypeUse("return dimension") []
          annotated(@Both("declaration and type") @TypeUse("component") final String
            @TypeUse("array") [] @TypeUse("ellipsis") ... values);

        public native long nativeCall(long wide, double weight, String description) throws IOException;
      }

      record Value(String label, long value) {
        @Deprecated public Value {
          if (label == null) throw new IllegalArgumentException("label");
        }
        public Value(String label) { this(label, 1L); }
        public long twice() { return value + value; }
      }

      record Empty() {}

      class Failure {
        static String failed() {
          try {
            if (System.nanoTime() != 0L) return "café " + System.currentTimeMillis();
            return "alternate";
          } catch (RuntimeException error) {
            return "caught";
          }
        }
      }
      """);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17", "-g", "-parameters",
      "-encoding", "UTF-8", "-d", classes.toString(), source.toString()) != 0) {
      throw new AssertionError("javac failed");
    }
    Files.writeString(classes.resolve("fernflower_abstract_parameter_names.txt"),
      "methodwriter/Base supplies (IJLjava/lang/Object;)V count width item\n");
    return classes;
  }
}
