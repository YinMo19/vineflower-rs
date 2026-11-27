import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.struct.gen.*;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.vineflower.kotlin.KotlinImportCollector;
import org.vineflower.kotlin.KotlinWriter;
import org.vineflower.kotlin.util.KTypes;

class KotlinTypesReference {
  public static void main(String[] args) throws Exception {
    Init.init();
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", ""), IFernflowerLogger.NO_OP);
    try {
      engine.addSource(Path.of(args[0]).toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      for (var name : processor.getMapRootClasses().keySet().stream().sorted().toList()) {
        var node = processor.getMapRootClasses().get(name);
        var collector = new KotlinImportCollector(new ImportCollector(node));
        DecompilerContext.startClass(collector);
        for (var field : node.classStruct.getFields()) {
          System.out.println(KotlinWriter.toValidKotlinIdentifier(field.getName()));
          var generic = field.getSignature();
          emit(generic == null ? FieldDescriptor.parseDescriptor(field.getDescriptor()).type : generic.type);
        }
        for (var method : node.classStruct.getMethods()) {
          System.out.println(KotlinWriter.toValidKotlinIdentifier(method.getName()));
          var generic = method.getSignature();
          var descriptor = MethodDescriptor.parseDescriptor(method.getDescriptor());
          for (var ty : generic == null ? List.of(descriptor.params) : generic.parameterTypes) emit(ty);
          emit(generic == null ? descriptor.ret : generic.returnType);
        }
        var buffer = new TextBuffer();
        collector.writeImports(buffer, true);
        System.out.println(buffer.convertToStringAndAllowDataDiscard());
      }
      for (var mappings : List.of(KTypes.KOTLIN_TO_JAVA_LANG, KTypes.KOTLIN_TO_JAVA_UTIL)) {
        for (var key : mappings.keySet().stream().map(Object::toString).sorted().toList()) {
          for (var nullable : List.of(false, true)) System.out.println("signature|" + key + "|" + nullable + "|" + KTypes.getJavaSignature(key, nullable));
        }
      }
    } finally { engine.clearContext(); }
  }

  static void emit(VarType ty) {
    for (var outer : List.of(false, true)) System.out.println(KTypes.getKotlinType(ty, outer));
    for (var nullable : List.of(false, true)) System.out.println(KTypes.getJavaSignature(ty.value, nullable));
  }
}
