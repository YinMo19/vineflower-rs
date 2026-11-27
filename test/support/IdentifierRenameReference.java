import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.extern.IIdentifierRenamer;
import org.jetbrains.java.decompiler.modules.renamer.ConverterHelper;
import org.jetbrains.java.decompiler.modules.renamer.IdentifierConverter;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;

public class IdentifierRenameReference {
  public static void main(String[] args) throws Exception {
    Path scratch = Path.of(args[0]);
    compile(scratch);
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
      IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0",
      IFernflowerPreferences.RENAME_ENTITIES, "1",
      IFernflowerPreferences.USER_RENAMER_CLASS, Trace.class.getName()
    ), IFernflowerLogger.NO_OP);
    try {
      engine.addLibrary(scratch.resolve("library.jar").toFile());
      engine.addSource(scratch.resolve("source.jar").toFile());
      var context = DecompilerContext.getStructContext();
      var originals = context.getOwnClasses();
      var helperField = Fernflower.class.getDeclaredField("helper");
      helperField.setAccessible(true);
      var helper = (IIdentifierRenamer)helperField.get(engine);
      var pool = DecompilerContext.getPoolInterceptor();
      new IdentifierConverter(context, helper, pool).rename();
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(helper);
      for (String call : Trace.calls) System.out.println(call);
      for (var original : originals) {
        String owner = original.qualifiedName;
        printMapping(pool.getName(owner), owner);
        for (var method : original.getMethods()) {
          String key = owner + " " + method.getName() + " " + method.getDescriptor();
          printMapping(pool.getName(key), key);
        }
        for (var field : original.getFields()) {
          String key = owner + " " + field.getName() + " " + field.getDescriptor();
          printMapping(pool.getName(key), key);
        }
        var renamed = context.getClass(owner);
        System.out.println("class|" + owner + "|" + renamed.qualifiedName);
        for (var method : renamed.getMethods()) {
          System.out.println("method|" + method.getName() + "|" + method.getDescriptor());
        }
        for (var field : renamed.getFields()) {
          System.out.println("field|" + field.getName() + "|" + field.getDescriptor());
        }
        var constants = renamed.getPool();
        for (int i = 1; i < constants.getPool().size(); ++i) {
          if (constants.getConstant(i) instanceof LinkConstant link
            && (link.type == CodeConstants.CONSTANT_Fieldref || link.type == CodeConstants.CONSTANT_Methodref
                || link.type == CodeConstants.CONSTANT_InterfaceMethodref)) {
            link = constants.getLinkConstant(i);
            System.out.println("link|" + i + "|" + link.classname + "|" + link.elementname + "|" + link.descriptor);
          }
        }
      }
      processor.getMapRootClasses().entrySet().stream().sorted(Map.Entry.comparingByKey()).forEach(entry -> {
        var node = entry.getValue();
        System.out.println("node|" + entry.getKey() + "|" + node.simpleName + "|" + node.type + "|" +
          (node.parent == null ? "null" : node.parent.classStruct.qualifiedName));
      });
    } finally {
      engine.clearContext();
    }
  }

  private static void printMapping(String renamed, String key) {
    if (renamed != null) System.out.println("mapping|" + key + "|" + renamed);
  }

  public static final class Trace extends ConverterHelper {
    static final List<String> calls = new ArrayList<>();

    @Override
    public boolean toBeRenamed(Type kind, String owner, String name, String descriptor) {
      boolean rename = super.toBeRenamed(kind, owner, name, descriptor);
      calls.add("check|" + kind.name().substring("ELEMENT_".length()) + "|" + owner + "|" + name + "|" + descriptor + "|" + rename);
      return rename;
    }

    @Override
    public String getNextClassName(String fullName, String simpleName) {
      String result = super.getNextClassName(fullName, simpleName);
      calls.add("new|CLASS|" + fullName + "|" + simpleName + "|" + result);
      return result;
    }

    @Override
    public String getNextFieldName(String owner, String name, String descriptor) {
      String result = super.getNextFieldName(owner, name, descriptor);
      calls.add("new|FIELD|" + owner + "|" + name + "|" + descriptor + "|" + result);
      return result;
    }

    @Override
    public String getNextMethodName(String owner, String name, String descriptor) {
      String result = super.getNextMethodName(owner, name, descriptor);
      calls.add("new|METHOD|" + owner + "|" + name + "|" + descriptor + "|" + result);
      return result;
    }
  }

  private static void compile(Path root) throws Exception {
    Path library = Files.createDirectory(root.resolve("library"));
    Path libSource = Files.writeString(root.resolve("Library.java"), """
      package library;
      public class Library {
        protected String ab(String text) { return text; }
        public native int x(int number);
        public static class c {}
      }
      """);
    Path external = Files.writeString(root.resolve("External.java"), """
      package library;
      public interface External {
        int c(int numeric);
      }
      """);
    javac(List.of("-d", library.toString(), libSource.toString(), external.toString()));
    jar(library, root.resolve("library.jar"));

    Path classes = Files.createDirectory(root.resolve("source"));
    Path source = Files.writeString(root.resolve("Subject.java"), """
      package rename;
      import library.External;
      import library.Library;

      class class_0 {}
      class class_1 {}
      class CON {}
      class m {}
      class Ár {}
      class $a$$b {}
      interface a { m[] m(m[] value); }
      interface b { m[] m(m[] value); }
      interface Together extends a, b, External {}
      interface Further extends Together, b {}

      class Base extends Library implements Together {
        int field_0;
        int q;
        int con;
        m[] z;
        public native int n();
        public m[] m(m[] value) { return value; }
        public int c(int numeric) { return numeric; }
        protected String ab(String text) { return text; }
        public int method_0() { return q; }
        int t() { return super.ab("text").length(); }
        private int a() { return 1; }
        public int a(int value) { return value; }
      }

      class Subject extends Base implements Further {
        public m[] m(m[] value) { return super.m(value); }
        public int c(int numeric) { return super.c(numeric); }
        int a() { return 2; }
        int b(m arg) { return this.a() + this.a(3); }
        m[] array() { return z; }

        class x {
          m val;
          m x(m value) { this.val = value; return this.val; }
        }
        Object worker() {
          class yy {}
          return new yy();
        }
      }

      class x {
        class y {
          void q() {}
        }
      }
      """);
    javac(List.of("-classpath", library.toString(), "-d", classes.toString(), source.toString()));
    jar(classes, root.resolve("source.jar"));
  }

  private static void javac(List<String> flags) {
    var args = new ArrayList<>(List.of("--release", "17", "-encoding", "UTF-8", "-g", "-parameters"));
    args.addAll(flags);
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, args.toArray(String[]::new)) != 0) {
      throw new AssertionError("javac failed");
    }
  }

  private static void jar(Path classes, Path target) throws Exception {
    try (var paths = Files.walk(classes); var output = new ZipOutputStream(Files.newOutputStream(target))) {
      for (Path file : paths.filter(Files::isRegularFile).sorted().toList()) {
        output.putNextEntry(new ZipEntry(classes.relativize(file).toString().replace('\\', '/')));
        Files.copy(file, output);
        output.closeEntry();
      }
    }
  }
}
