import java.io.File;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeSet;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.ClassWriter;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.decompiler.PrintStreamLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.main.rels.MethodWrapper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AssignmentExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ExitExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FieldExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.IfExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.InvocationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.VarExprent;
import org.jetbrains.java.decompiler.modules.decompiler.vars.VarVersionPair;
import org.jetbrains.java.decompiler.util.TextBuffer;

class WriterEnumRecordReference {
  private static final String ENUM_SOURCE = """
    enum WriterEnum {
      A, B(7);
      final int number;
      WriterEnum() { this(3); }
      WriterEnum(int number) { this.number = number; }

      static WriterEnum[] values(int ignored) { return values(); }
      static WriterEnum valueOf(int ignored) { return A; }
      static WriterEnum[] manual = { A };
    }

    class WriterQualifiers {
      static int self = WriterQualifiers.self;
      static int early = WriterQualifiers.later;
      static java.util.function.IntSupplier lazy = () -> WriterQualifiers.later;
      static int later = 7;
    }
    """;
  private static final String RECORD_SOURCE = """
    record WriterWide(long total, double weight, int code, String text) {
      static String lastText;
      public WriterWide {
        lastText = text;
        if (total < 0) total = 0;
        int oldCode = code * 2;
        if (oldCode < 0) throw new IllegalArgumentException("code");
        if (oldCode > 99) code = oldCode;
      }

      WriterWide(long total) { this(total, 0, 0, ""); }
    }

    record WriterExplicit(long total, double weight, int code) {
      public WriterExplicit(long total, double weight, int code) {
        int adjusted = code * 2;
        if (adjusted < 0) throw new IllegalArgumentException("code");
        this.total = total;
        this.weight = weight;
        this.code = adjusted;
      }
    }
    """;
  private static final Method PREPARE;
  private static final Field FORCE_QUALIFIED;

  static {
    try {
      PREPARE = ClassWriter.class.getDeclaredMethod("invokeProcessors", TextBuffer.class, ClassNode.class);
      PREPARE.setAccessible(true);
      FORCE_QUALIFIED = FieldExprent.class.getDeclaredField("forceQualified");
      FORCE_QUALIFIED.setAccessible(true);
    } catch (ReflectiveOperationException e) {
      throw new AssertionError(e);
    }
  }

  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var enums = Files.writeString(scratch.resolve("WriterEnum.java"), ENUM_SOURCE);
    var records = Files.writeString(scratch.resolve("WriterWide.java"), RECORD_SOURCE);
    for (int release : new int[] {8, 17}) {
      var classes = Files.createDirectory(scratch.resolve("java" + release));
      compile(release, classes, "-g", enums);
      if (release == 17) compile(release, classes, "-g", records);
      for (String profile : new String[] {"default", "lvt-off", "enum-off"}) {
        snapshot(classes, profile, true, release == 17);
      }
      if (release == 17) {
        snapshot(classes, "tiny", false, true);
        snapshot(classes, "jad", false, true);
      }
    }
    var noDebug = Files.createDirectory(scratch.resolve("no-debug"));
    compile(17, noDebug, "-g:none", records);
    snapshot(noDebug, "default", false, true);
    snapshot(noDebug, "tiny-params", false, true);
  }

  private static void compile(int release, Path classes, String debug, Path source) throws Exception {
    String home = System.getenv("VINEFLOWER_JDK_" + release);
    var flags = new String[] {"-encoding", "UTF-8", debug, "-d", classes.toString(), source.toString()};
    int status;
    if (home == null) {
      var args = new String[flags.length + 2];
      args[0] = "--release";
      args[1] = Integer.toString(release);
      System.arraycopy(flags, 0, args, 2, flags.length);
      status = ToolProvider.getSystemJavaCompiler().run(null, null, null, args);
    } else {
      var bin = Path.of(home, "bin", "javac" + (File.separatorChar == '\\' ? ".exe" : ""));
      var builder = new ProcessBuilder(bin.toString()).inheritIO();
      builder.command().addAll(java.util.List.of(flags));
      status = builder.start().waitFor();
    }
    if (status != 0) throw new AssertionError("javac exit " + status);
  }

  private static void snapshot(Path classes, String profile, boolean enums, boolean records) throws Exception {
    Map<String, Object> options = new HashMap<>();
    options.put(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0");
    options.put(IFernflowerPreferences.LOG_LEVEL, "warn");
    if (profile.equals("lvt-off")) options.put(IFernflowerPreferences.USE_DEBUG_VAR_NAMES, "0");
    if (profile.startsWith("tiny") || profile.equals("jad")) {
      options.put("variable-renaming", profile.startsWith("tiny") ? "tiny" : "jad");
    }
    if (profile.equals("tiny-params") || profile.equals("jad")) options.put("rename-parameters", "1");
    if (profile.equals("enum-off")) options.put(IFernflowerPreferences.DECOMPILE_ENUM, "0");
    var engine = new Fernflower(new ConsoleFileSaver(null), options, new PrintStreamLogger(System.err));
    try {
      engine.addSource(classes.toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      System.out.println("profile\t" + classes.getFileName() + "\t" + profile);
      if (enums) {
        dumpClass(processor.getMapRootClasses().get("WriterEnum"));
        dumpClass(processor.getMapRootClasses().get("WriterQualifiers"));
      }
      if (records) {
        dumpClass(processor.getMapRootClasses().get("WriterWide"));
        dumpClass(processor.getMapRootClasses().get("WriterExplicit"));
      }
    } finally {
      engine.clearContext();
    }
  }

  private static void dumpClass(ClassNode node) throws Exception {
    DecompilerContext.getClassProcessor().processClass(node.classStruct);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
    var errors = new TextBuffer();
    if (!(boolean) PREPARE.invoke(null, errors, node)) {
      throw new AssertionError(errors.convertToStringAndAllowDataDiscard());
    }
    var wrapper = node.getWrapper();
    System.out.println("class\t" + node.classStruct.qualifiedName);
    for (String key : new TreeSet<>(wrapper.getHiddenMembers())) {
      System.out.println("hidden\t" + key);
    }
    if (node.classStruct.qualifiedName.equals("WriterQualifiers")) {
      var inits = wrapper.getStaticFieldInitializers();
      for (int i = 0; i < inits.size(); i++) {
        for (var expr : inits.get(i).getAllExprents(true, true)) {
          if (expr instanceof FieldExprent field) qualifier(inits.getKey(i), field);
        }
      }
      for (var method : wrapper.getMethods()) {
        if (method.methodStruct.getName().startsWith("lambda$")) {
          method.getOrBuildGraph().iterateExprentsDeep(expr -> {
            if (expr instanceof FieldExprent field) qualifier(method.methodStruct.getName(), field);
            return 0;
          });
        }
      }
    }
    for (var method : wrapper.getMethods()) {
      if (method.methodStruct.getName().equals("<init>")) dumpConstructor(method);
    }
  }

  private static void qualifier(String context, FieldExprent field) {
    try {
      System.out.println("qualifier\t" + context + "\t" + field.getName() + "\t" + FORCE_QUALIFIED.getBoolean(field));
    } catch (IllegalAccessException e) {
      throw new AssertionError(e);
    }
  }

  private static void dumpConstructor(MethodWrapper method) {
    DecompilerContext.resetMethod(method);
    if (method.decompileError != null || method.root == null) throw new AssertionError(method.decompileError);
    System.out.println("constructor\t" + method.methodStruct.getDescriptor() + "\t" + method.isCompactRecordConstructor);
    int index = 1;
    for (var param : method.desc().params) {
      var pair = new VarVersionPair(index, 0);
      System.out.println("formal\t" + index + "\t" + method.varproc.getVarName(pair)
        + "\t" + method.varproc.getClashingName(pair));
      index += param.stackSize;
    }
    method.getOrBuildGraph().iterateExprents(expr -> {
      if (expr instanceof InvocationExprent inv && inv.getFunctype() == InvocationExprent.Type.INIT) {
        System.out.println("call\t" + inv.getClassname() + "\t" + inv.getStringDescriptor());
      } else if (expr instanceof AssignmentExprent assignment && assignment.getLeft() instanceof FieldExprent field) {
        Exprent value = assignment.getRight();
        System.out.println("assign\t" + field.getName() + "\t" + (value instanceof VarExprent var
          ? var.getIndex() + "\t" + (var.getLVT() != null)
          : "non-var"));
      } else if (expr instanceof AssignmentExprent assignment
                 && assignment.getLeft() instanceof VarExprent var && var.isDefinition()) {
        System.out.println("local\t" + var.getIndex() + "\t" + var.getName());
      } else if (expr instanceof IfExprent) {
        System.out.println("if");
      } else if (expr instanceof ExitExprent exit && exit.getExitType() == ExitExprent.Type.THROW) {
        System.out.println("throw");
      }
      return 0;
    });
  }
}
