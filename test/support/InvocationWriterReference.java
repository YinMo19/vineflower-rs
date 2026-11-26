// SPDX-License-Identifier: Apache-2.0

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;

class InvocationWriterReference {
  public static void main(String[] args) throws Exception {
    var classes = compileFixture(Path.of(args[0]));
    for (int width : new int[]{44, 140}) {
      var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, width == 44 ? "0" : "1",
        IFernflowerPreferences.EXPLICIT_GENERIC_ARGUMENTS, width == 44 ? "0" : "1",
        IFernflowerPreferences.PREFERRED_LINE_LENGTH, Integer.toString(width)
      ), IFernflowerLogger.NO_OP);
      try {
        engine.addSource(classes.toFile());
        var processor = DecompilerContext.getClassProcessor();
        processor.loadClasses(null);
        var root = processor.getMapRootClasses().get("CallSubject");
        processor.processClass(root.classStruct);
        DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, root);
        for (var wrapper : root.getWrapper().getMethods()) {
          if (wrapper.decompileError != null) throw new AssertionError(wrapper.decompileError);
          DecompilerContext.resetMethod(wrapper);
          DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, wrapper);
          int[] index = {0};
          wrapper.getOrBuildGraph().iterateExprents(expr -> {
            if (expr instanceof ExitExprent exit) {
              expr = exit.getValue();
            }
            if (expr instanceof InvocationExprent call) {
              var name = wrapper.methodStruct.getName() + wrapper.methodStruct.getDescriptor() + "|" + index[0]++;
              WriterSnapshot.print(width, "invocation", name, call.toJava(1));
            }
            return 0;
          });
        }
      } finally {
        engine.clearContext();
      }
    }
  }

  private static Path compileFixture(Path scratch) throws Exception {
    var text = """
      import java.lang.invoke.*;
      import java.net.http.HttpRequest;

      interface Face { default int base() { return 42; } }

      class Ancestor {
        Ancestor(int count) {}
        int inherited(int count) { return count; }
      }

      class Factories {
        static <T> T provided() { return null; }
      }

      class CallSubject extends Ancestor implements Face {
        CallSubject(int count) { super(count); }
        CallSubject() { this(17); }

        int superclass(int count) { return super.inherited(count); }
        int superinterface() { return Face.super.base(); }
        String boxedReceiver(int value) { return Integer.valueOf(value).toString(); }

        static int choose(int value) { return 0; }
        static int choose(Integer value) { return 1; }
        static int boxing(int value) { return choose(Integer.valueOf(value)); }
        static int unboxing(Integer value) { return choose(value.intValue()); }

        static String inspect(Object value) { return "object"; }
        static String inspect(String value) { return "string"; }
        static String nullArgument() { return inspect((Object)null); }

        static String chain(String text) {
          return text.trim().concat("café long method argument").toUpperCase();
        }
        static String generics() {
          return Factories.<String>provided().trim();
        }

        static String varargs(String format) { return format; }
        static String varargs(String... strings) { return strings[0]; }
        static String unambiguousVarargs() { return varargs("one", "two"); }
        static String ambiguousVarargs() { return varargs(new String[]{"one"}); }
        static String emptyVarargs() { return varargs(); }
        static String bootstrapVarargs() { return String.format("%s", "text"); }
        static HttpRequest.Builder platformVarargs(HttpRequest.Builder builder) {
          return builder.headers("Accept", "text/plain");
        }
        static Object polymorphic(MethodHandle handle) throws Throwable {
          return (String) handle.invokeExact("a", 2);
        }

        static String dynamic(String text, int number) {
          return text + "café" + number;
        }
      }

      class CallSubjectStringConcatFactory {
        public static CallSite joinInvocation(
            MethodHandles.Lookup lookup, String name, MethodType type, String recipe, Object... constants)
            throws StringConcatException {
          return StringConcatFactory.makeConcatWithConstants(lookup, name, type, recipe, constants);
        }
      }
      """;
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("CallSubject.java"), text);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17", "-g", "-parameters",
      "-encoding", "UTF-8", "-d", classes.toString(), source.toString()) != 0) {
      throw new AssertionError("javac failed");
    }

    // Preserve the compiler's real invokedynamic instruction and bootstrap
    // argument but direct the method handle to an ordinary user bootstrap.
    var file = classes.resolve("CallSubject.class");
    var bytes = changePoolString(Files.readAllBytes(file),
      "java/lang/invoke/StringConcatFactory", "CallSubjectStringConcatFactory");
    Files.write(file, changePoolString(bytes, "makeConcatWithConstants", "joinInvocation"));
    return classes;
  }

  private static byte[] changePoolString(byte[] bytes, String original, String replacement) {
    // A variable-length CONSTANT_Utf8 can be edited without changing pool indexes.
    var textPool = new String(bytes, StandardCharsets.ISO_8859_1);
    int start = textPool.indexOf(original);
    if (start < 3 || textPool.indexOf(original, start + original.length()) >= 0 ||
      bytes[start - 3] != 1 || bytes[start - 2] != 0 || bytes[start - 1] != original.length()) {
      throw new AssertionError("Expected the bootstrap CONSTANT_Utf8 " + original);
    }
    var updated = new java.io.ByteArrayOutputStream();
    updated.write(bytes, 0, start - 1);
    updated.write(replacement.length());
    updated.writeBytes(replacement.getBytes(StandardCharsets.US_ASCII));
    updated.write(bytes, start + original.length(), bytes.length - start - original.length());
    return updated.toByteArray();
  }
}
