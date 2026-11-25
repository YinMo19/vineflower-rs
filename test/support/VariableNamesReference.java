// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.HashMap;
import java.util.TreeMap;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.ClassesProcessor;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.rels.LambdaProcessor;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;

class VariableNamesReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("Names.java"), """
      class Names<T> {
        static void consume(Object... values) {}
        static int exercise() {
          int first = (int) System.nanoTime();
          int second = first + 1;
          consume(first, second);
          return first - second;
        }
        int mix(int input, long width, T value, String text, int[] indexes) {
          int one = input + 1;
          int two = input + 2;
          double ratio = (double) one / two;
          String[] parts = text.split(" ");
          Runnable collect = () -> consume(one, value);
          class Local { int step(int arg) { int local = arg + one; consume(local); return local; } }
          consume(one, two, ratio, parts, collect, new Local(), indexes);
          return (int)(one + two + width);
        }
      }
      """);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null,
      "-g", "-parameters", "--release", "17", "-d", classes.toString(), source.toString()) != 0)
      throw new AssertionError("javac failed");

    var order = Comparator.comparingInt((VarVersionPair v) -> v.var).thenComparingInt(v -> v.version);
    for (String provider : new String[]{"identity", "jad", "tiny"}) {
      for (var debug : new String[]{"0","1"}) {
        var options = new HashMap<String,Object>();
        options.put("include-runtime","0");
        options.put("__unit_test_mode__","1");
        options.put("use-lvt-names",debug);
        options.put("rename-parameters","1");
        if (!provider.equals("identity")) options.put("variable-renaming",provider);
        var engine = new Fernflower(null, options, IFernflowerLogger.NO_OP);
        engine.addSource(classes.toFile());
        var cp = DecompilerContext.getClassProcessor();
        cp.loadClasses(null);
        var root = cp.getMapRootClasses().get("Names");
        DecompilerContext.startClass(new ImportCollector(root));
        new LambdaProcessor().processClass(root);
        var imports = ClassesProcessor.class.getDeclaredMethod("addClassNameToImport", ClassesProcessor.ClassNode.class, ImportCollector.class);
        imports.setAccessible(true);
        imports.invoke(null, root, DecompilerContext.getImportCollector());
        var initialize = ClassesProcessor.class.getDeclaredMethod("initWrappers", ClassesProcessor.ClassNode.class, LanguageSpec.class);
        initialize.setAccessible(true);
        initialize.invoke(null, root, null);
        System.out.println(provider + " " + debug);
        for (var node : new TreeMap<>(cp.getMapRootClasses()).values()) {
          if (node.type == ClassesProcessor.ClassNode.Type.LAMBDA) continue;
          for (var method : node.getWrapper().getMethods()) {
            System.out.println(node.classStruct.qualifiedName + " " + method.methodStruct);
            if (method.decompileError != null) {
              var e = method.decompileError;
              if (!(e instanceof NullPointerException)
                  || !e.getStackTrace()[0].getClassName().endsWith(".TinyNameProvider")
                  || !e.getMessage().contains("because \"type\" is null")) throw new AssertionError(e);
              System.out.println("Missing Tiny variable type");
              continue;
            }
            for (var pair : method.varproc.getUsedVarVersions().stream().sorted(order).toList()) {
              var local = method.varproc.getVarLVT(pair);
              System.out.println(pair.var + " " + pair.version + " " + method.varproc.getVarName(pair)
                + " " + (local == null ? "-" : local.getName())
                + " " + (method.varproc.getClashingName(pair) == null ? "-" : method.varproc.getClashingName(pair)));
            }
          }
        }
      }
    }
  }
}
