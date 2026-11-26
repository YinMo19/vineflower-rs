// SPDX-License-Identifier: Apache-2.0

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HexFormat;
import java.util.Map;
import java.util.TreeMap;

import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.CounterContainer;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.vineflower.kotlin.KotlinImportCollector;

public final class KotlinBodyReference {
  public static void main(String[] args) throws Exception {
    var fixture = Files.readAllLines(Path.of(args[0]));
    String selected = fixture.size() > 4 ? fixture.get(4) : null;
    var opts = Map.<String, Object>of(
      "thread-count", "1",
      "new-line-separator", "1",
      "include-runtime", fixture.get(2),
      "__unit_test_mode__", "1",
      "keep-literals", "1",
      "preferred-line-length", "60",
      "kt-collapse-string-concat", fixture.get(3),
      "decompile-inner", selected == null ? "1" : "0"
    );
    Fernflower engine = new Fernflower(null, opts, IFernflowerLogger.NO_OP);
    engine.addSource(new File(fixture.get(0)));
    engine.addLibrary(new File(fixture.get(1)));
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    var nodes = new TreeMap<>(processor.getMapRootClasses()).values();
    ImportCollector selectedImports = null;
    if (selected != null) {
      for (var node : nodes) {
        if (node.type != ClassNode.Type.ROOT) continue;
        processor.processClass(node.classStruct);
        if (selected.equals(node.classStruct.qualifiedName)) {
          selectedImports = DecompilerContext.getImportCollector();
        }
      }
    }
    for (var node : nodes) {
      if (node.type != ClassNode.Type.ROOT) continue;
      var cls = node.classStruct;
      if (selected == null) {
        processor.processClass(cls);
      } else if (!selected.equals(cls.qualifiedName)) {
        continue;
      }
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
      var imports = selected == null ? DecompilerContext.getImportCollector() : selectedImports;
      DecompilerContext.setImportCollector(new KotlinImportCollector(imports));
      for (var method : node.getWrapper().getMethods()) {
        if (method.decompileError != null) {
          throw new IllegalStateException(method.methodStruct.getName(), method.decompileError);
        }
        if (method.root == null) continue;
        String key = method.methodStruct.getName() + " " + method.methodStruct.getDescriptor();
        DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, method);
        int statements = method.counter.getCounter(CounterContainer.STATEMENT_COUNTER);
        int expressions = method.counter.getCounter(CounterContainer.EXPRESSION_COUNTER);
        TextBuffer body = method.root.toJava(1);
        body.addBytecodeMapping(method.root.getDummyExit().bytecode);
        TextBuffer full = new TextBuffer();
        full.append(body, cls.qualifiedName, key);
        full.reformat();
        var mapping = new TreeMap<Integer, Integer>();
        for (var tracer : full.getTracers().values()) {
          mapping.putAll(tracer.getMapping());
        }
        String text = full.convertToStringAndAllowDataDiscard();
        System.out.println(cls.qualifiedName + "\t" + key + "\t"
          + statements + "," + expressions + "\t"
          + HexFormat.of().formatHex(text.getBytes(StandardCharsets.UTF_8)) + "\t" + mapping);
      }
    }
  }
}
