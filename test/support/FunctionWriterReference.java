// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Map;
import java.util.TreeMap;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.util.TextBuffer;

class FunctionWriterReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("OperatorSubject.java"), """
      import java.io.Serializable;
      import java.util.List;
      @SuppressWarnings("unchecked")
      class OperatorSubject {
        static int mask(int input, int other) { return (input & 255) + (other | 65280); }
        static int assoc(int first, int second, int third) { return first + (second + third); }
        static float floats(float first, float second, float third) { return first + (second + third); }
        static int sub(int first, int second, int third) { return first - (second - third); }
        static int shifts(int first, int second, int third) { return (first << second) >>> third; }
        static int negations(int first, int second) { return -(~(first - second)); }
        static boolean chars(char code) { return code == 65 || code == 9; }
        static short convert(double number) { return (short)(int) number; }
        static byte unboxThenConvert(Integer number) { return (byte) number.intValue(); }
        static double pi(double number) { return number / (Math.PI / 3); }
        static int length(Object[] items) { return items.length; }
        static int lengthOfNull() { return ((Object[])null).length; }
        static int onlyByte(byte value) { return value; }
        static int narrowArg() { return onlyByte((byte)37); }
        static int overloaded(String value) { return 1; }
        static int overloaded(Integer value) { return 2; }
        static int typedNull() { return overloaded((String)null); }
        static float floatNaN() { return Float.NaN; }
        static int maxInt() { return Integer.MAX_VALUE; }
        static long maxLong() { return Long.MAX_VALUE; }
        static int ternary(boolean choice, int first, int second) {
          return choice ? (first > second ? first : second) : first + second;
        }
        static String concat(boolean choice, String first, String second) {
          return "Result: " + (choice ? first : second);
        }
        static boolean pattern(Object value) { return value instanceof String text; }
        static Object explicitCast(Object value) { return (String) value; }
        static Serializable intersection(Object value) { return (Runnable & Serializable) value; }
        static <T> T generic(Object value) { return (T) value; }
        static <T> List<T> genericCast(Object value) { return (List<T>) value; }
        static String nullReturn() { return null; }
      }
      """);
    int status = ToolProvider.getSystemJavaCompiler().run(null, null, null,
      "--release", "17", "-g", "-Xlint:none", "-d", classes.toString(), source.toString());
    if (status != 0) throw new AssertionError("javac exit " + status);

    var mappings = new ArrayList<String>();
    for (int width : new int[] {24, 160}) {
      var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "1",
        IFernflowerPreferences.LITERALS_AS_IS, width == 160 ? "1" : "0",
        IFernflowerPreferences.PREFERRED_LINE_LENGTH, Integer.toString(width)),
        IFernflowerLogger.NO_OP);
      try {
        engine.addSource(classes.toFile());
        var processor = DecompilerContext.getClassProcessor();
        processor.loadClasses(null);
        var node = processor.getMapRootClasses().get("OperatorSubject");
        processor.processClass(node.classStruct);
        DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
        for (var method : node.getWrapper().getMethods()) {
          if (method.methodStruct.getName().equals("<init>")) continue;
          if (method.decompileError != null) throw new AssertionError(method.decompileError);
          DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, method);
          DecompilerContext.resetMethod(method);
          int[] index = {0};
          method.getOrBuildGraph().iterateExprents(expr -> {
            if (expr instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.RETURN) {
              var name = method.methodStruct.getName() + "|" + method.methodStruct.getDescriptor() + "|" + index[0]++;
              var buffer = new TextBuffer().append(expr.toJava(1), "OperatorSubject", name);
              WriterSnapshot.print(width, "expression", name, buffer);
              var tracer = buffer.getTracers().values().iterator().next();
              mappings.add(width + "|" + name + "|" + new TreeMap<>(tracer.getMapping()));
            }
            return 0;
          });
          if (index[0] == 0) throw new AssertionError(method.methodStruct.getName());
        }
      } finally {
        engine.clearContext();
      }
    }
    System.out.println("section=bytecode-mappings");
    mappings.forEach(System.out::println);
  }
}
