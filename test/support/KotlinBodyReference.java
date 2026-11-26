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
    var opts = Map.<String, Object>of(
      "thread-count", "1",
      "new-line-separator", "1",
      "include-runtime", fixture.get(2),
      "__unit_test_mode__", "1",
      "keep-literals", "1",
      "preferred-line-length", "60",
      "kt-collapse-string-concat", fixture.get(3)
    );
    Fernflower engine = new Fernflower(null, opts, IFernflowerLogger.NO_OP);
    engine.addSource(new File(fixture.get(0)));
    engine.addLibrary(new File(fixture.get(1)));
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    for (var node : new TreeMap<>(processor.getMapRootClasses()).values()) {
      if (node.type != ClassNode.Type.ROOT) continue;
      var cls = node.classStruct;
      processor.processClass(cls);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS, cls);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
      DecompilerContext.setImportCollector(new KotlinImportCollector(new ImportCollector(node)));
      for (var method : node.getWrapper().getMethods()) {
        if (method.decompileError != null) {
          throw new IllegalStateException(method.methodStruct.getName(), method.decompileError);
        }
        if (method.root == null) continue;
        String key = method.methodStruct.getName() + " " + method.methodStruct.getDescriptor();
        DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, method);
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
          + method.counter.getCounter(CounterContainer.STATEMENT_COUNTER) + ","
          + method.counter.getCounter(CounterContainer.EXPRESSION_COUNTER) + "\t"
          + HexFormat.of().formatHex(text.getBytes(StandardCharsets.UTF_8)) + "\t" + mapping);
      }
    }
  }
}
