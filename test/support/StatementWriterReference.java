// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Map;
import java.util.TreeMap;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.util.TextBuffer;

class StatementWriterReference {
  private static final String SOURCE = """
    import java.io.IOException;
    import java.io.InputStream;
    import java.util.List;

    abstract class FlowSubject {
      static int state;
      abstract int external(int argument);
      native int nativeMethod(Object object);

      static void branches(int choice, int first, int second) {
        if (choice == first) {
          state += first;
          state -= second;
        } else if (choice == second) {
          state -= first;
          state += second;
        } else {
          state = first + second;
        }
      }

      static int counted(int limit) {
        int sum = 0;
        for (int index = 0; index < limit; index++) sum += index;
        return sum;
      }

      static int doWhile(int count) {
        int total = 0;
        do {
          total += count;
        } while (--count > 0);
        return total;
      }

      static void whileLoop(int count, long longNamedLimit) {
        while (count < longNamedLimit && count > 0) {
          state = count * count;
          count = Integer.rotateRight(count, 2);
        }
      }

      static void infinite() {
        for (;;) {
          state = (state ^ 255) + 1;
        }
      }

      static int enhanced(int[] numbers, List<String> text) {
        int sum = 0;
        for (int number : numbers) sum += number;
        for (String word : text) sum += word.length();
        return sum;
      }

      static int labeled(int[][] rows, int threshold) {
        int score = 0;
        outer: for (int[] row : rows) {
          for (int value : row) {
            if (value < 0) continue outer;
            if (value > threshold) break outer;
            score += value;
          }
          score += 7;
        }
        return score;
      }

      static void labeledContinue(int count, int length) {
        outer: for (int first = 0; first < count; first++) {
          state += first;
          for (int second = 0; second < length; second++) {
            state += second;
            if (state == count) continue outer;
            state /= first + 1;
          }
          state ^= first;
        }
      }

      static int declared(boolean choice, int lower, int upper) {
        int first;
        int second;
        if (choice) {
          first = state;
          second = lower;
        } else {
          first = upper;
          second = state;
        }
        return first - second;
      }

      static void caught(int divisor) {
        try {
          state /= divisor;
          state += divisor;
        } catch (ArithmeticException | IllegalArgumentException failure) {
          state = failure.hashCode();
        } catch (IllegalStateException other) {
          state = other.hashCode();
        } finally {
          state *= 3;
        }
      }

      static void monitored(Object lock, int number) {
        synchronized (lock) {
          state += number;
          if (number < 0) state -= number;
        }
        state = number;
      }

      static int resource(InputStream input) throws IOException {
        try (InputStream stream = input) {
          return stream.read();
        }
      }

      static int resources(InputStream left, InputStream right) throws IOException {
        try (InputStream first = left; InputStream second = right) {
          return first.read() + second.read();
        }
      }
    }
    """;

  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("FlowSubject.java"), SOURCE);
    int status = ToolProvider.getSystemJavaCompiler().run(null, null, null,
      "--release", "17", "-g", "-d", classes.toString(), source.toString());
    if (status != 0) throw new AssertionError("javac exit " + status);

    var prepare = ClassWriter.class.getDeclaredMethod("invokeProcessors", TextBuffer.class, ClassNode.class);
    prepare.setAccessible(true);
    var mappings = new ArrayList<String>();
    var states = new ArrayList<String>();
    for (int width : new int[] {26, 37, 160}) {
      var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "1",
        IFernflowerPreferences.FINALLY_DEINLINE, width == 37 ? "0" : "1",
        IFernflowerPreferences.NEW_LINE_SEPARATOR, width == 37 ? "0" : "1",
        IFernflowerPreferences.INDENT_STRING, width == 37 ? "\t" : "   ",
        IFernflowerPreferences.PREFERRED_LINE_LENGTH, Integer.toString(width)),
        IFernflowerLogger.NO_OP);
      try {
        engine.addSource(classes.toFile());
        engine.addSource(scratch.resolve("TestTryReturn.class").toFile());
        var processor = DecompilerContext.getClassProcessor();
        processor.loadClasses(null);
        var node = processor.getMapRootClasses().get("FlowSubject");
        processor.processClass(node.classStruct);
        DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
        var error = new TextBuffer();
        if (!(boolean) prepare.invoke(null, error, node)) {
          throw new AssertionError(error.convertToStringAndAllowDataDiscard());
        }
        for (var method : node.getWrapper().getMethods()) {
          String name = method.methodStruct.getName() + "|" + method.methodStruct.getDescriptor();
          states.add(width + "|FlowSubject|" + name + "|" + methodState(method));
          if (method.root == null || method.decompileError != null) continue;

          DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, method);
          var body = method.root.toJava(2);
          body.addBytecodeMapping(method.root.getDummyExit().bytecode);
          var buffer = new TextBuffer().append(body, "FlowSubject", name);
          WriterSnapshot.print(width, "statement", name, buffer);
          var tracers = buffer.getTracers();
          var offsets = tracers.isEmpty() ? Map.<Integer, Integer>of() : tracers.values().iterator().next().getMapping();
          mappings.add(width + "|" + name + "|" + new TreeMap<>(offsets));
        }

        DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, null);
        var failures = processor.getMapRootClasses().get("pkg/TestTryReturn");
        processor.processClass(failures.classStruct);
        for (var method : failures.getWrapper().getMethods()) {
          if (method.methodStruct.getName().equals("testParsingFailure")) {
            states.add(width + "|pkg/TestTryReturn|testParsingFailure|()V|" + methodState(method));
          }
        }
      } finally {
        engine.clearContext();
      }
    }
    System.out.println("section=bytecode-mappings");
    mappings.forEach(System.out::println);
    System.out.println("section=method-states");
    states.forEach(System.out::println);
  }

  private static String methodState(MethodWrapper method) {
    return method.decompileError != null ? "failed" : method.root == null ? "no-code" : "code";
  }
}
