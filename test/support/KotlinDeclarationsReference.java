import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.vineflower.kotlin.KotlinChooser;
import org.vineflower.kotlin.KotlinImportCollector;
import org.vineflower.kotlin.metadata.MetadataNameResolver;
import org.vineflower.kotlin.struct.*;
import org.vineflower.kt.metadata.ProtoBuf;

class KotlinDeclarationsReference {
  public static void main(String[] args) {
    for (int width : new int[]{160,24}) {
      var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", "", "preferred-line-length", Integer.toString(width)), IFernflowerLogger.NO_OP);
      try {
        engine.addSource(Path.of(args[0]).toFile());
        var processor = DecompilerContext.getClassProcessor();
        processor.loadClasses(null);
        for (var name : processor.getMapRootClasses().keySet().stream().sorted().toList()) {
          var node = processor.getMapRootClasses().get(name);
          DecompilerContext.startClass(new KotlinImportCollector(new ImportCollector(node)));
          KotlinChooser.parseMetadataFor(node.classStruct);
          var element = node.classStruct.getAttribute(KElement.KEY);
          if (!(element instanceof KClass cls)) throw new AssertionError(name);
          var resolver = cls.resolver();
          for (var fn : cls.proto().getFunctionList()) {
            var buf = new TextBuffer();
            for (var generic : fn.getTypeParameterList()) {
              var parameter = KTypeParameter.from(generic, resolver);
              for (var bound : parameter.upperBounds()) addType(buf, bound);
            }
            List<KParameter> parameters = new ArrayList<>();
            for (var param : fn.getValueParameterList()) {
              var vararg = param.hasVarargElementType() ? KType.from(param.getVarargElementType(),resolver) : null;
              var value = new KParameter(param.getFlags(),resolver.resolve(param.getName()),KType.from(param.getType(),resolver),vararg,param.getTypeId());
              parameters.add(value);
              value.stringify(1,buf);
              buf.appendLineSeparator();
            }
            addType(buf, KType.from(fn.getReturnType(),resolver));
            if (fn.hasContract()) buf.append(KContract.from(fn.getContract(), parameters,resolver,cls.proto().getTypeTable()).stringify(1));
            buf.reformat();
            System.out.println(buf.convertToStringAndAllowDataDiscard());
          }
        }
      } finally { engine.clearContext(); }
    }
  }
  static void addType(TextBuffer buf, KType type) {
    buf.append(type.toString()).append(' ').append(type.stringify(1)).appendLineSeparator();
  }
}
