// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import javax.tools.ToolProvider;
import net.fabricmc.fernflower.api.FabricJavadocStyle;
import net.fabricmc.fernflower.api.IFabricJavadocProvider;
import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.struct.*;
import org.jetbrains.java.decompiler.util.TextBuffer;

class ClassDeclarationReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var source = Files.writeString(scratch.resolve("Host.java"), """
      package decl;
      import java.io.Serializable;
      import java.util.ArrayList;
      import java.util.List;
      sealed interface Shape<T> permits Open, Fixed { }
      non-sealed class Open<T> implements Shape<T>, Cloneable { }
      final class Fixed extends Open<Integer> implements Shape<Integer> { }
      @Deprecated public abstract class Host<T extends Number & Serializable> extends ArrayList<T> {
        interface Member {
          class Implicit { }
          @interface Tag { }
        }
        enum Mode { A, B { public String toString() { return ""; } }; }
        public Object local(boolean choice) {
          class Local<T> extends Open<List<T>> { }
          return choice ? new Local<Integer>() : new Runnable() { public void run() {} };
        }
        record Pair<T>(T first, T... remaining) implements Serializable { }
      }
      """);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17", "-g", "-d",
        classes.toString(), source.toString()) != 0) throw new AssertionError("javac failed");
    var definition = ClassWriter.class.getDeclaredMethod("writeClassDefinition", ClassNode.class, TextBuffer.class, int.class);
    definition.setAccessible(true);
    for (int profile = 0; profile < 3; ++profile) {
      final int mode = profile;
      var options = new HashMap<String,Object>();
      options.put("include-runtime", "0");
      options.put("preferred-line-length", "32");
      options.put("decompile-generics", profile == 1 ? "0" : "1");
      options.put("decompile-enums", profile == 2 ? "0" : "1");
      options.put("mark-corresponding-synthetics", profile == 0 ? "0" : "1");
      if (profile > 0) options.put(IFabricJavadocProvider.PROPERTY_NAME, new IFabricJavadocProvider() {
        public String getClassDoc(StructClass cl) { return "Doc " + cl.qualifiedName + "\n\n第二行\n\n"; }
        public String getFieldDoc(StructClass cl, StructField field) { return null; }
        public String getMethodDoc(StructClass cl, StructMethod method) { return null; }
        public FabricJavadocStyle getClassJavadocStyle(StructClass cl) {
          return mode == 1 ? FabricJavadocStyle.HTML : FabricJavadocStyle.MARKDOWN;
        }
      });
      var processor = WrapperStages.load(classes, options);
      for (var name : List.of("decl/Shape","decl/Open","decl/Fixed","decl/Host")) {
        var root = processor.getMapRootClasses().get(name);
        processor.processClass(root.classStruct);
        printDefinition(profile, new ClassWriter(), definition, root, 0);
      }
    }
  }

  private static void printDefinition(int profile, ClassWriter writer, java.lang.reflect.Method def, ClassNode node, int indent) throws Exception {
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
    TextBuffer text = new TextBuffer();
    def.invoke(writer, node, text, indent);
    WriterSnapshot.print(profile, "definition", node.classStruct.qualifiedName, text);
    for (var child : node.nested) printDefinition(profile, writer, def, child, indent + 1);
  }
}
