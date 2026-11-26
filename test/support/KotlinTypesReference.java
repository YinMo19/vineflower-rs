// SPDX-License-Identifier: Apache-2.0

import java.lang.reflect.Method;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;
import org.jetbrains.java.decompiler.struct.gen.*;
import org.jetbrains.java.decompiler.util.TextBuffer;

class KotlinTypesReference {
  public static void main(String[] args) throws Exception {
    Init.init();
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", ""), IFernflowerLogger.NO_OP);
    try {
      engine.addSource(Path.of(args[0]).toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      var loader = PluginContext.getCurrentContext().getPlugins().stream()
        .filter(plugin -> plugin.id().equals("Kotlin")).findFirst().orElseThrow().getClass().getClassLoader();
      var types = loader.loadClass("org.vineflower.kotlin.util.KTypes");
      var kotlinType = types.getMethod("getKotlinType", VarType.class, boolean.class);
      var signature = types.getMethod("getJavaSignature", String.class, boolean.class);
      var identifier = loader.loadClass("org.vineflower.kotlin.KotlinWriter").getMethod("toValidKotlinIdentifier", String.class);
      var imports = loader.loadClass("org.vineflower.kotlin.KotlinImportCollector").getConstructor(ImportCollector.class);
      for (var name : processor.getMapRootClasses().keySet().stream().sorted().toList()) {
        var node = processor.getMapRootClasses().get(name);
        var collector = (ImportCollector) imports.newInstance(new ImportCollector(node));
        DecompilerContext.startClass(collector);
        for (var field : node.classStruct.getFields()) {
          System.out.println(identifier.invoke(null, field.getName()));
          var generic = field.getSignature();
          emit(kotlinType, signature, generic == null ? FieldDescriptor.parseDescriptor(field.getDescriptor()).type : generic.type);
        }
        for (var method : node.classStruct.getMethods()) {
          System.out.println(identifier.invoke(null, method.getName()));
          var generic = method.getSignature();
          var descriptor = MethodDescriptor.parseDescriptor(method.getDescriptor());
          for (var ty : generic == null ? List.of(descriptor.params) : generic.parameterTypes) emit(kotlinType, signature, ty);
          emit(kotlinType, signature, generic == null ? descriptor.ret : generic.returnType);
        }
        var buffer = new TextBuffer();
        collector.writeImports(buffer, true);
        System.out.println(buffer.convertToStringAndAllowDataDiscard());
      }
      for (var field : List.of("KOTLIN_TO_JAVA_LANG", "KOTLIN_TO_JAVA_UTIL")) {
        var mappings = (Map<?,?>) types.getField(field).get(null);
        for (var key : mappings.keySet().stream().map(Object::toString).sorted().toList()) {
          for (var nullable : List.of(false, true)) System.out.println("signature|" + key + "|" + nullable + "|" + signature.invoke(null, key, nullable));
        }
      }
    } finally { engine.clearContext(); }
  }

  static void emit(Method kotlinType, Method signature, VarType ty) throws Exception {
    for (var outer : List.of(false, true)) System.out.println(kotlinType.invoke(null, ty, outer));
    for (var nullable : List.of(false, true)) System.out.println(signature.invoke(null, ty.value, nullable));
  }
}
