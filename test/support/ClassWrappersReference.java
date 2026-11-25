// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.TreeMap;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;

import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.modules.decompiler.stats.SwitchStatement;

class ClassWrappersReference {
  static void dumpCases(Statement stat) {
    if (stat instanceof SwitchStatement sw) {
      for (var group : sw.getCaseValues()) {
        for (var value : group) {
          String label;
          if (value instanceof FieldExprent field) label = "field " + field.getClassname() + "." + field.getName();
          else if (value instanceof ConstExprent constant) label = "constant " + constant.getValue();
          else if (value == null) label = "default";
          else throw new AssertionError(value.type);
          System.out.println("case\t" + label);
        }
      }
    }
    for (var child : stat.getStats()) dumpCases(child);
  }

  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("WrapperSubject.java"), """
      abstract class WrapperSubject {
        enum Kind { LEFT, RIGHT, CENTER }
        static class Member { native long external(int key); }
        int text(String s) {
          return switch (s) {
            case "Aa" -> 1;
            case "BB" -> 2;
            default -> 3;
          };
        }
        abstract int measure(long x, double y);
        int score(Kind kind) {
          return switch (kind) {
            case LEFT -> 31;
            case CENTER -> 47;
            default -> 0;
          };
        }
      }
      """);
    int status = ToolProvider.getSystemJavaCompiler().run(null, null, null,
      "--release", "17", "-g", "-d", classes.toString(), source.toString());
    if (status != 0) throw new AssertionError("javac exit " + status);

    var engine = new Fernflower(null, Map.of(
      IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0",
      IFernflowerPreferences.UNIT_TEST_MODE, "1"), IFernflowerLogger.NO_OP);
    engine.addSource(classes.toFile());
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    var root = processor.getMapRootClasses().get("WrapperSubject");
    processor.processClass(root.classStruct);
    for (var node : new TreeMap<>(processor.getMapRootClasses()).values()) {
      var wrapper = node.getWrapper();
      for (var method : wrapper.getMethods()) {
        var state = method.decompileError != null ? "failed" : method.root == null ? "no-code" : "code";
        System.out.println(node.classStruct.qualifiedName + "\t" + method.methodStruct.getName()
          + "\t" + method.methodStruct.getDescriptor() + "\t" + state);
        if (method.root != null) dumpCases(method.root);
      }
    }
  }
}
