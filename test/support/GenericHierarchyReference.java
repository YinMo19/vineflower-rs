// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Path;
import java.util.Map;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;

class GenericHierarchyReference {
  public static void main(String[] args) {
    var group = Path.of(args[0]);
    var javac = ToolProvider.getSystemJavaCompiler();
    if (javac.run(null, null, null, "-d", args[0], group.resolve("Hierarchy.java").toString()) != 0) {
      throw new IllegalStateException("Failed to compile the hierarchy");
    }
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", "0"), IFernflowerLogger.NO_OP);
    try {
      engine.addSource(group.toFile());
      var cl = DecompilerContext.getStructContext().getClass("keys/Hierarchy");
      for (var owner : cl.getAllGenerics().keySet()) System.out.println(owner);
    } finally {
      engine.clearContext();
    }
  }
}
