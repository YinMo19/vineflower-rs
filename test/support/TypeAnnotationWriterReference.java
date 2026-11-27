import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.util.TextBuffer;

class TypeAnnotationWriterReference {
  public static void main(String[] args) throws Exception {
    var classes = compileFixture(Path.of(args[0]));
    var definition = ClassWriter.class.getDeclaredMethod("writeClassDefinition", ClassNode.class, TextBuffer.class, int.class);
    definition.setAccessible(true);
    for (int width : new int[]{42, 120}) {
      var options = Map.<String, Object>of(
        "include-runtime", "0",
        "use-method-parameters", "1",
        "preferred-line-length", Integer.toString(width)
      );
      var engine = new Fernflower(new ConsoleFileSaver(null), options, IFernflowerLogger.NO_OP);
      engine.addSource(classes.toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      var nodes = processor.getMapRootClasses();
      var root = nodes.get("ann/Shapes");
      processor.processClass(root.classStruct);
      var writer = new ClassWriter();
      for (String name : new String[]{"ann/Shapes", "ann/Shapes$R", "ann/Shapes$VR"}) {
        var node = nodes.get(name);
        DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
        var buffer = new TextBuffer();
        definition.invoke(writer, node, buffer, node == root ? 0 : 1);
        WriterSnapshot.print(width, "class", name, buffer);
      }

      var owner = root.classStruct;
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, root);
      for (var field : owner.getFields()) {
        var buffer = new TextBuffer();
        writer.writeField(root.getWrapper(), owner, field, buffer, 1);
        WriterSnapshot.print(width, "field", field.getName(), buffer);
      }
      for (int i = 0; i < owner.getMethods().size(); ++i) {
        var method = owner.getMethods().get(i);
        if (method.getName().equals("<init>")) continue;
        var buffer = new TextBuffer();
        writer.writeMethod(root, method, i, buffer, 1);
        WriterSnapshot.print(width, "method", method.getName(), buffer);
      }
      // Re-entering processClass keeps the parsed attributes of this root.
      processor.processClass(root.classStruct);
      var componentOwner = nodes.get("ann/Shapes$VR");
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, componentOwner);
      var repeated = new TextBuffer();
      definition.invoke(writer, componentOwner, repeated, 1);
      WriterSnapshot.print(width, "repeat", componentOwner.classStruct.qualifiedName, repeated);
      engine.clearContext();
    }
  }

  private static Path compileFixture(Path root) throws Exception {
    var classes = Files.createDirectory(root.resolve("classes"));
    var source = Files.writeString(root.resolve("Shapes.java"), """
      package ann;

      import java.lang.annotation.*;
      import java.util.List;
      import java.util.Map;

      @Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
      @Retention(RetentionPolicy.RUNTIME)
      @interface V { String value(); }

      @Target(ElementType.TYPE_USE)
      @interface I { String value(); }

      @Target({ElementType.TYPE_USE, ElementType.FIELD, ElementType.METHOD, ElementType.PARAMETER, ElementType.RECORD_COMPONENT})
      @Retention(RetentionPolicy.RUNTIME)
      @interface Both { String value(); }

      @Target(ElementType.TYPE_USE)
      @interface Named { String description(); Class<?> expected(); }

      public abstract class Shapes<@V("parameter") T extends @V("class bound") Number & Comparable<T>,
                                   U extends @V("interface bound") Runnable & AutoCloseable,
                                   Z> {
        public class N { public class Q {} }
        public static class S<X> { public class J {} }
        public static class Holder<X> { public class Inner<Y> {} }

        public @V("element") int @I("array0") [] @V("array1") [] primitives;
        public @V("outer") Shapes.N.@I("inner") Q nested;
        public Shapes.@V("static") S<?>.@I("inner") J underStatic;
        public Holder<@V("outer arg") Integer>.Inner<@V("inner arg") Long> genericOwner;
        public @V("raw type") List<@I("wild") ? extends @V("bound") Number @I("bound array") []> wildExtends;
        public Map<@V("unbounded") ?, @I("wild") ? super @V("bound") Long> wildSuper;
        public @Both("duplicate field") @I("type only") String annotatedField;
        public List<@V("equal") String> @V("equal") [] equalTextPaths;
        public abstract @Both("duplicate return") @I("return") T inspect(@Both("duplicate parameter") final @I("primitive") int x,
          @V("array component") String @I("first dimension") [] @V("last dimension") ... values);
        public abstract <@V("method parameter") Y extends @V("method bound") Runnable & AutoCloseable, W> Y bounds(W value);

        public record R(@Both("duplicate record") List<@V("arg") String> @I("array") [] values,
                        @Named(description = "café 🐈 long annotation value", expected = String.class) String label) {}
        public record VR(@V("element") String @I("first dimension") [] @V("last dimension") ... values) {}
      }
      """);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17", "-g", "-parameters",
      "-encoding", "UTF-8", "-d", classes.toString(), source.toString()) != 0) {
      throw new AssertionError("javac failed");
    }
    return classes;
  }
}
