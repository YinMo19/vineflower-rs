import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import javax.tools.ToolProvider;
import net.fabricmc.fernflower.api.FabricJavadocStyle;
import net.fabricmc.fernflower.api.IFabricJavadocProvider;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.InitializerProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.modules.renamer.PoolInterceptor;
import org.jetbrains.java.decompiler.struct.StructMethod;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.vineflower.kotlin.KotlinImportCollector;
import org.vineflower.kotlin.KotlinWriter;
import org.vineflower.kotlin.util.KEnumProcessor;

class KotlinFallbackReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var source = Files.writeString(scratch.resolve("FallbackSubject.java"), """
      package fallback;
      import java.io.IOException;
      import java.util.ArrayList;
      import java.util.List;
      import java.util.RandomAccess;

      abstract class Parent<P> {
        protected abstract Number base(long arg);
        abstract P bridge(P arg);
      }
      @kotlin.Metadata(k = 0, d1 = {})
      interface Face {
        int constant = 3;
        default String method(final String named) { return named; }
      }
      @kotlin.Metadata(k = 0, d1 = {})
      public abstract class FallbackSubject<P> extends Parent<String> {
        @Deprecated public static final String LABEL = "fall back";
        protected transient volatile List<? extends P> values = new ArrayList<>();
        public abstract <T extends List<P> & RandomAccess> T abstractWide(@Deprecated long wide, final T value);
        public native int nativeWide(long tall, String... more) throws IOException;
        @Override protected abstract Number base(long arg);
        @Override String bridge(String arg) { return arg; }
        static int receiver(String $this$receiver, int other) { return other; }
      }
      @kotlin.Metadata(k = 0, d1 = {})
      enum SampleEnum {
        FIRST(12), SECOND(42);
        private final int value;
        SampleEnum(int value) { this.value = value; }
      }
      """);
    var metadata = Files.writeString(scratch.resolve("Metadata.java"), """
      package kotlin;
      @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
      public @interface Metadata {
        int k();
        String[] d1();
      }
      """);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17", "-g", "-parameters",
        "-d", classes.toString(), source.toString(), metadata.toString()) != 0) throw new AssertionError("javac failed");

    int width = 35;
    var options = new HashMap<String, Object>();
    options.put("include-runtime", "0");
    options.put("preferred-line-length", Integer.toString(width));
    options.put("kt-enable", "1");
    options.put("rename-members", "1");
    options.put(IFabricJavadocProvider.PROPERTY_NAME, new IFabricJavadocProvider() {
      public String getClassDoc(StructClass cl) { return null; }
      public String getFieldDoc(StructClass cl, StructField fd) {
        return fd.getName().equals("values") ? "Field info\nSecond line\n" : null;
      }
      public String getMethodDoc(StructClass cl, StructMethod mt) {
        return mt.getName().equals("abstractWide") ? "Method info" : null;
      }
      public FabricJavadocStyle getClassJavadocStyle(StructClass cl) { return FabricJavadocStyle.MARKDOWN; }
    });
    var processor = WrapperStages.load(classes, options);
    DecompilerContext.getStructContext().loadAbstractMetadata(
      "fallback/FallbackSubject nativeWide (J[Ljava/lang/String;)I height tail");
    PoolInterceptor pool = DecompilerContext.getPoolInterceptor();
    for (String name : List.of("fallback/FallbackSubject", "fallback/Face", "fallback/SampleEnum")) {
      var node = processor.getMapRootClasses().get(name);
      processor.processClass(node.classStruct);
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
      DecompilerContext.setImportCollector(new KotlinImportCollector(DecompilerContext.getImportCollector()));
      var wrapper = node.getWrapper();
      InitializerProcessor.extractInitializers(wrapper);
      InitializerProcessor.hideInitalizers(wrapper);
      if (name.endsWith("SampleEnum")) KEnumProcessor.clearEnum(wrapper);
      if (name.endsWith("FallbackSubject")) {
        pool.addName(name + " values Ljava/util/List;", name + " listValues Ljava/util/List;");
        pool.addName(name + " receiver (Ljava/lang/String;I)I", name + " when (Ljava/lang/String;I)I");
      }
      var writer = new KotlinWriter();
      for (StructField field : node.classStruct.getFields()) {
        if (field.isSynthetic()) continue;
        var text = new TextBuffer();
        writer.writeField(wrapper, node.classStruct, field, text, 1);
        WriterSnapshot.print(width, "field", name + "|" + field.getName(), text);
      }
      for (int i = 0; i < node.classStruct.getMethods().size(); ++i) {
        var method = node.classStruct.getMethods().get(i);
        if (name.endsWith("SampleEnum") && !List.of("<init>", "<clinit>").contains(method.getName())) continue;
        var text = new TextBuffer();
        var keep = writer.writeMethod(node, method, i, text, 1);
        WriterSnapshot.print(width, "method", name + "|" + method.getName() + "|" + method.getDescriptor() + "|" + keep, text);
      }
    }
  }
}
