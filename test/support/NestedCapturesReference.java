import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.rels.NestedClassProcessor;

class NestedCapturesReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    var source = Files.writeString(scratch.resolve("CaptureHost.java"), """
      class CaptureHost {
        int id;
        class Member {
          Member() { this(0L); }
          Member(long user) { id += (int)user; }
        }
        static class StaticMember {}
        Runnable make(long a, String b) {
          class Local implements Runnable {
            int value;
            Local(double explicit) { value = (int) explicit; }
            Local(int tick, int extra) { value = tick + extra; }
            public void run() { System.out.println(id + ":" + a + b + value); }
          }
          Runnable anon = new Runnable() {
            public void run() { System.out.println(a + b); }
          };
          if (id == 0) return new Local(3.0);
          if (id == 1) return new Local(id,2);
          return anon;
        }
        Runnable arrows(long n) { return () -> { Runnable r = () -> System.out.println(n + id); r.run(); }; }
        static java.util.function.LongUnaryOperator delta(long captured) {
          return argument -> { long result = captured - argument; return result * 2; };
        }
        Runnable ref() { return this::touch; }
        void touch() {}
      }
      """);
    if (ToolProvider.getSystemJavaCompiler().run(null,null,null, "-g","-parameters","--release","17","-d",classes.toString(),source.toString()) != 0)
      throw new AssertionError("javac failed");
    for (String debug : new String[]{"0","1"}) {
      for (String anonymous : new String[]{"0","1"}) {
        System.out.println("options " + debug + " " + anonymous);
        compare(classes, debug, anonymous);
      }
    }
  }

  private static void compare(Path classes, String debug, String anonymous) throws Exception {
    var cp = WrapperStages.initialize(classes,"CaptureHost",Map.of("__unit_test_mode__","1","include-runtime","0","use-lvt-names",debug,"lambda-to-anonymous-class",anonymous));
    var root = cp.getMapRootClasses().get("CaptureHost");
    new NestedClassProcessor().processClass(root,root);
    var rows = new java.util.ArrayList<String>();
    NestedCorpusReference.collect(root, rows);
    rows.forEach(System.out::println);
  }
}
