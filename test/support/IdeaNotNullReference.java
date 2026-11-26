// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Path;
import java.util.Map;

import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.Init;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;
import org.jetbrains.java.decompiler.util.TextBuffer;

class IdeaNotNullReference {
  public static void main(String[] args) throws Exception {
    System.setProperty("VALIDATE_DECOMPILED_CODE", "true");
    Init.init();
    Path classes = Path.of(args[0]);
    for (int enabled : new int[]{0, 1}) {
      var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
        "include-runtime", "1",
        "resugar-idea-notnull", Integer.toString(enabled)
      ), IFernflowerLogger.NO_OP);
      try {
        if (PluginContext.getCurrentContext().getPlugins().stream().noneMatch(plugin -> plugin.id().equals("IdeaNotNull"))) {
          throw new AssertionError("The upstream plugin jar was not loaded");
        }
        engine.addSource(classes.toFile());
        var processor = DecompilerContext.getClassProcessor();
        processor.loadClasses(null);
        var node = processor.getMapRootClasses().get("pkg/TestIdeaNotNull");
        processor.processClass(node.classStruct);
        for (var method : node.getWrapper().getMethods()) {
          if (method.decompileError != null) throw new AssertionError(method.decompileError);
        }
        var buffer = new TextBuffer();
        new ClassWriter().writeClass(node, buffer, 0);
        WriterSnapshot.print(enabled, "class", node.classStruct.qualifiedName, buffer);
      } finally {
        engine.clearContext();
      }
    }
  }
}
