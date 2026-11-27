import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.api.plugin.Plugin;
import org.jetbrains.java.decompiler.api.plugin.pass.NamedPass;
import org.jetbrains.java.decompiler.api.plugin.pass.Pass;
import org.jetbrains.java.decompiler.api.plugin.pass.PassContext;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;

class KotlinMethodStagesReference {
  public static void main(String[] args) throws Exception {
    for (String line : Files.readAllLines(Path.of(args[0]))) {
      String[] group = line.split("\t");
      var engine = new Fernflower(new ConsoleFileSaver(Path.of(args[0]).toFile()), Map.ofEntries(
        Map.entry("include-runtime", group[1]), Map.entry("thread-count", "1"),
        Map.entry("remove-synthetic", "0"), Map.entry("ignore-invalid-bytecode", "1"),
        Map.entry("verify-anonymous-classes", "1"), Map.entry("__unit_test_mode__", "1"),
        Map.entry("keep-literals", "1"), Map.entry("dump-exception-on-error", "0"),
        Map.entry("remove-empty-try-catch", group[2]), Map.entry("ensure-synchronized-monitors", group[2]),
        Map.entry("incorporate-returns", group[2])
      ), IFernflowerLogger.NO_OP);
      for (int i = 3; i < group.length; i++) {
        engine.addSource(Path.of(group[i]).toFile());
      }
      observeDefinitions(DecompilerContext.getStructContext().getPluginContext(), group[0]);
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      for (ClassNode node : new TreeMap<>(processor.getMapRootClasses()).values()) {
        if (node.type == ClassNode.Type.ROOT) {
          processor.processClass(node.classStruct);
          requireSuccessfulAnalysis(node);
        }
      }
      engine.clearContext();
    }
  }

  @SuppressWarnings("unchecked")
  private static void observeDefinitions(PluginContext plugins, String group) {
    var specs = (Map<Plugin, LanguageSpec>) ExpressionSnapshot.read(
      ExpressionSnapshot.field(PluginContext.class, "languageSpecs"), plugins);
    var spec = specs.entrySet().stream().filter(e -> e.getKey().id().equals("Kotlin"))
      .findFirst().orElseThrow().getValue();
    var passes = (List<Pass>) ExpressionSnapshot.read(
      ExpressionSnapshot.field(spec.pass.getClass(), "passes"), spec.pass);
    var nameField = ExpressionSnapshot.field(NamedPass.class, "name");
    for (int i = 0; i < passes.size(); i++) {
      Pass step = passes.get(i);
      if ("SetVarDefinitions".equals(ExpressionSnapshot.read(nameField, step))) {
        passes.set(i, ctx -> {
          boolean changed = step.run(ctx);
          emit(group, ctx);
          return changed;
        });
        passes.subList(i + 1, passes.size()).clear();
        return;
      }
    }
    throw new IllegalStateException("Kotlin SetVarDefinitions pass is missing");
  }

  private static void emit(String group, PassContext ctx) {
    var method = ctx.getMethod();
    var counters = DecompilerContext.getCounterContainer();
    var root = ctx.getRoot();
    try {
      System.out.println(group + "\t" + method.getClassQualifiedName() + "\t" + method.getName() + method.getDescriptor()
        + "\t" + ControlFlowReference.snapshot(ctx.getGraph(), false)
        + "\t" + StructureReference.snapshot(root, counters, true, true)
        + "\t" + ExpressionSnapshot.snapshot(root, counters, ExpressionSnapshot.Detail.VARIABLE_DEFINITIONS)
        + "\t" + VariableSnapshot.snapshot(ctx.getVarProc(), true));
    } catch (IllegalAccessException e) {
      throw new IllegalStateException(e);
    }
  }

  private static void requireSuccessfulAnalysis(ClassNode node) {
    if (node.type != ClassNode.Type.LAMBDA) {
      for (var method : node.getWrapper().getMethods()) {
        if (method.decompileError != null) {
          throw new IllegalStateException("Kotlin method failed: " + method.methodStruct, method.decompileError);
        }
      }
    }
    for (ClassNode child : node.nested) requireSuccessfulAnalysis(child);
  }
}
