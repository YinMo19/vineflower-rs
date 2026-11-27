import java.io.ByteArrayInputStream;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.HexFormat;
import java.util.Map;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.Init;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AnnotationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.vineflower.kotlin.KotlinChooser;
import org.vineflower.kotlin.metadata.BitEncoding;
import org.vineflower.kotlin.metadata.MetadataNameResolver;
import org.vineflower.kt.metadata.ProtoBuf;
import org.vineflower.kt.metadata.jvm.JvmProtoBuf;
import org.vineflower.kt.protobuf.ExtensionRegistryLite;
import org.vineflower.kt.protobuf.MessageLite;

class KotlinMetadataReference {
  public static void main(String[] args) throws Exception {
    Init.init();
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", "0"), IFernflowerLogger.NO_OP);
    try {
      Path root = Path.of(args[0]);
      engine.addSource(root.resolve("kt").toFile());
      engine.addSource(root.resolve("ktold").toFile());
      var context = DecompilerContext.getCurrentContext().structContext;
      var codec = new Codec();
      codec.encodingExamples();
      codec.nameExamples();
      for (var cl : context.getOwnClasses().stream().sorted(Comparator.comparing(c -> c.qualifiedName)).toList()) {
        codec.print(cl);
      }
    } finally {
      engine.clearContext();
    }
  }

  private static final HexFormat HEX = HexFormat.of();

  private static class Codec {
    private final ExtensionRegistryLite registry = ExtensionRegistryLite.newInstance();
    private final KotlinChooser chooser = new KotlinChooser();

    Codec() {
      JvmProtoBuf.registerAllExtensions(registry);
    }

    void encodingExamples() throws Exception {
      String[][] examples = new String[][]{
        {},
        {"", "abcdefgh"},
        {new String(new char[]{0, 0xd800, 0x01ff}), new String(new char[]{0xdc08})},
        {new String(new char[]{0xffff, 0x0081, 0x00ff, 0x0080, 0xfe00}), "XYZ"},
        {"abcdefg"},
        {"abcdefghijk", "lmnopqrstuvwxyz"}
      };
      for (var example : examples) System.out.println("bits|" + HEX.formatHex(BitEncoding.decodeBytes(example)));
    }

    void print(StructClass cl) throws Exception {
      System.out.println("class|" + cl.qualifiedName);
      for (boolean decompile : new boolean[]{false, true}) {
        for (boolean export : new boolean[]{false, true}) {
          DecompilerContext.setProperty("kt-enable", decompile ? "1" : "0");
          DecompilerContext.setProperty("kt-export-metadata", export ? "1" : "0");
          System.out.println("choose|" + chooser.isLanguage(cl));
        }
      }
      var metadata = annotation(cl);
      if (metadata == null) {
        System.out.println("none");
        return;
      }
      var rawKind = field(metadata, "k");
      if (rawKind == null) {
        System.out.println("error");
        return;
      }
      int kind = (Integer)((ConstExprent)rawKind).getValue();
      System.out.println("kind|" + kind);
      var rawData = field(metadata, "d1");
      if (rawData == null) {
        System.out.println(cl.superClass != null && "kotlin/jvm/internal/FunctionReferenceImpl".equals(cl.superClass.getString())
          ? "reference" : "error");
        return;
      }
      try {
        String[] d1 = strings(rawData);
        var input = new ByteArrayInputStream(BitEncoding.decodeBytes(d1));
        var rawStrings = field(metadata, "d2");
        var table = rawStrings == null ? null : JvmProtoBuf.StringTableTypes.parseDelimitedFrom(input, registry);
        var names = rawStrings == null ? null : new MetadataNameResolver(table, strings(rawStrings));
        MessageLite message = switch (kind) {
          case 1 -> ProtoBuf.Class.parseFrom(input, registry);
          case 2, 5 -> ProtoBuf.Package.parseFrom(input, registry);
          case 3 -> ProtoBuf.Function.parseFrom(input, registry);
          default -> null;
        };
        if (kind < 1 || kind > 5) {
          System.out.println("none");
          return;
        }
        var extra = field(metadata, "xs");
        String facade = kind != 5 ? null : extra == null
          ? cl.qualifiedName.split("__")[0] : (String)((ConstExprent)extra).getValue();
        if (names != null) {
          System.out.println("table|" + wire(table));
          int size = table.getRecordList().stream().mapToInt(record -> Math.max(0, record.getRange())).sum();
          for (int i = 0; i < size; ++i) printName(names, i);
        }
        if (message != null) System.out.println("wire|" + wire(message));
        if (kind == 4) {
          for (String part : d1) System.out.println("part|" + units(part));
        } else if (kind == 5) {
          System.out.println("facade|" + units(facade));
        }
      } catch (Exception e) {
        System.out.println("error");
      }
    }

    void nameExamples() throws Exception {
      byte[] elements = HEX.parseHex("0a04220200010a09220200012a030001580a08220200032a0203000a053203eda0800a04080118010a0608ffffffff0f0a0618ffffffff0f");
      var delimited = new java.io.ByteArrayOutputStream();
      delimited.write(elements.length);
      delimited.write(elements);
      var table = JvmProtoBuf.StringTableTypes.parseDelimitedFrom(new ByteArrayInputStream(delimited.toByteArray()), registry);
      var names = new MetadataNameResolver(table,
        new String[]{"abcd", "abcd", "abcd", "ignored", "A$B", "ignored"});
      for (int i = -1; i < 7; ++i) printName(names, i);
    }

    private static void printName(MetadataNameResolver names, int i) {
      try {
        System.out.println("name|" + units(names.resolve(i)));
      } catch (RuntimeException e) {
        System.out.println("name-error");
      }
    }
  }

  private static String wire(MessageLite message) {
    return HEX.formatHex(message.toByteArray());
  }

  private static String units(String string) {
    var result = new StringBuilder();
    string.chars().forEach(unit -> result.append(HEX.toHexDigits((char)unit)));
    return result.toString();
  }

  private static AnnotationExprent annotation(StructClass cl) {
    for (var key : java.util.List.of(StructGeneralAttribute.ATTRIBUTE_RUNTIME_VISIBLE_ANNOTATIONS,
      StructGeneralAttribute.ATTRIBUTE_RUNTIME_INVISIBLE_ANNOTATIONS)) {
      var attribute = cl.getAttribute(key);
      if (attribute == null) continue;
      for (var entry : attribute.getAnnotations()) {
        if ("kotlin/Metadata".equals(entry.getClassName())) return entry;
      }
    }
    return null;
  }

  private static Object field(AnnotationExprent annotation, String name) {
    int index = annotation.getParNames().indexOf(name);
    return index < 0 ? null : annotation.getParValues().get(index);
  }

  private static String[] strings(Object raw) {
    return ((NewExprent)raw).getLstArrayElements().stream()
      .map(expr -> (String)((ConstExprent)expr).getValue()).toArray(String[]::new);
  }
}
