import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.util.TextBuffer;

class CompilationUnitReference {
  public static void main(String[] args) throws Exception {
    Path root = Path.of(args[0]);
    Path classes = Files.createDirectories(root.resolve("classes"));
    Path file = Files.writeString(root.resolve("Unit.java"), """
        package source;
        import java.util.function.*;
        import java.util.List;
        interface Fn<T,R> { R apply(T value); }
        public class Unit {
          private final String prefix;
          private String[] parts = {"a", "b"};
          public Unit(String prefix) { this.prefix = prefix; }
          public Fn<String,String> simple() {return x -> prefix + x;}
          public Fn<String,Fn<Integer,String>> nested() {
            return s -> n -> { String result = s; for (int i=0;i<n;i++) result = result + prefix; return result; };
          }
          public IntFunction<String[]> array() {return String[]::new;}
          public Function<String,String> reference(String s) {return s::concat;}
          public Fn<String,String> local(String s) {
            class Local implements Fn<String,String> { public String apply(String x) {return s + x;} }
            return new Local();
          }
          public Runnable empty() {return new Runnable() { public void run() {} };}
          public int choose(int key) { return switch(key) { case 1,2 -> prefix.length(); default -> key*2; }; }
          record Pair<T>(List<T> items, T... more) {}
          enum Mode { DIRECT, OTHER { public String toString() {return "other";} }; }
        }
        """);
    if (ToolProvider.getSystemJavaCompiler().run(null,null,null,"--release","17","-g","-parameters","-d",classes.toString(),file.toString())!=0)
      throw new AssertionError("javac failed");
    for (int profile=0;profile<4;profile++) {
      var opts = new HashMap<String,Object>();
      opts.put("include-runtime","0");
      opts.put("bytecode-source-mapping","1");
      opts.put("__unit_test_mode__","1");
      opts.put("__dump_original_lines__",profile==2?"1":"0");
      opts.put("preferred-line-length",profile==0?"160":"36");
      opts.put("lambda-to-anonymous-class",profile==1?"1":"0");
      opts.put("mark-corresponding-synthetics",profile==2?"1":"0");
      opts.put("sourcefile-comments",profile==2?"1":"0");
      opts.put("method-to-decompile",profile==3?"nested()Lsource/Fn;":"");
      var processor = WrapperStages.load(classes,opts);
      for (String name : List.of("source/Fn","source/Unit")) {
        var node = processor.getMapRootClasses().get(name);
        processor.processClass(node.classStruct);
        var buffer = new TextBuffer();
        processor.writeClass(node.classStruct,buffer);
        var output = root.resolve(profile+"-"+node.simpleName+".java");
        Files.writeString(output, buffer.convertToStringAndAllowDataDiscard(),StandardCharsets.UTF_8);
        Files.writeString(root.resolve(profile+"-"+node.simpleName+".map"),
          Arrays.toString(DecompilerContext.getBytecodeSourceMapper().getOriginalLinesMapping()));
      }
    }
  }
}
