import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.stats.Statement;
import org.jetbrains.java.decompiler.struct.attr.StructLocalVariableTableAttribute.LocalVariable;
import org.jetbrains.java.decompiler.struct.gen.CodeType;
import org.jetbrains.java.decompiler.struct.gen.VarType;

class OdditiesReference {
  private static List<Exprent> expressions(Statement statement) {
    List<Exprent> result = new ArrayList<>();
    var list = statement.getExprents() == null ? statement.getStatExprents() : statement.getExprents();
    for (Exprent expr : list) result.addAll(expr.getAllExprents(true, true));
    for (Statement child : statement.getStats()) result.addAll(expressions(child));
    return result;
  }

  private static void dump(ClassNode node, boolean nest) throws Exception {
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS, node.classStruct);
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_WRAPPER, node.getWrapper());
    DecompilerContext.setProperty(DecompilerContext.CURRENT_METHOD_WRAPPER, null);
    var imports = DecompilerContext.getImportCollector();
    var writeLocked = ImportCollector.class.getDeclaredField("writeLocked");
    writeLocked.setAccessible(true);
    var packImports = ImportCollector.class.getDeclaredMethod("packImports");
    packImports.setAccessible(true);
    for (var method : node.getWrapper().getMethods()) {
      var root = method.root;
      if (root == null) throw new AssertionError(method.decompileError);
      String name = method.methodStruct.getName();
      switch (name) {
        case "unknownCast", "badCast" -> {
          var cast = expressions(root).stream()
            .filter(e -> e instanceof FunctionExprent f && f.getFuncType() == FunctionExprent.FunctionType.CAST)
            .map(e -> (FunctionExprent)e)
            .findFirst().orElseThrow();
          ((ConstExprent)cast.getLstOperands().get(1)).setConstType(
            name.equals("badCast") ? new VarType(CodeType.ADDRESS) : VarType.VARTYPE_UNKNOWN);
          cast.setNeedsCast(true);
        }
        case "badDefinition" -> {
          var variable = expressions(root).stream()
            .filter(e -> e instanceof VarExprent v && v.isDefinition())
            .map(e -> (VarExprent)e)
            .findFirst().orElseThrow();
          variable.setLVT(null);
          variable.setVarType(null);
          method.varproc.setVarType(variable.getVarVersionPair(), null);
        }
        case "debugUnknown" -> {
          var variable = expressions(root).stream()
            .filter(e -> e instanceof VarExprent v && !v.isDefinition())
            .map(e -> (VarExprent)e)
            .findFirst().orElseThrow();
          variable.setLVT(new LocalVariable(0, 1, "value", "U", variable.getIndex()));
        }
      }

      try (var outer = nest ? imports.lock() : null) {
        Object previousImports = packImports.invoke(imports);
        String outcome = "ok";
        try {
          ExprProcessor.markExprOddities(root);
          if (name.equals("badCast")) throw new AssertionError("bad cast unexpectedly rendered");
        } catch (RuntimeException error) {
          if (!name.equals("badCast") || !error.getMessage().startsWith("invalid type: ")) throw error;
          outcome = "invalid-type";
        }
        if (writeLocked.getBoolean(imports) != nest || !packImports.invoke(imports).equals(previousImports)) {
          throw new AssertionError("changed import state");
        }
        String collision = "";
        if (name.equals("cast")) {
          collision = ":" + imports.getShortName("shadow.types.Instant")
            + ":" + imports.getShortName("java.time.Instant");
        }
        boolean error = root.addErrorComment;
        String warnings = root.commentLines == null ? "" : String.join("|", root.commentLines);
        System.out.println((nest ? "nested" : "unlocked") + "\t" + node.classStruct.qualifiedName
          + "\t" + name + method.methodStruct.getDescriptor() + "\t" + outcome + ":" + error + ":"
          + warnings + collision);
      }
    }
  }

  private static void run(Path classes, boolean nest) throws Exception {
    var engine = new Fernflower(null, Map.of(
      "include-runtime", "1",
      "decompile-assert", nest ? "0" : "1",
      "thread-count", "1"
    ), IFernflowerLogger.NO_OP);
    engine.addSource(classes.toFile());
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    var nodes = new TreeMap<>(processor.getMapRootClasses());
    for (var root : nodes.values()) {
      if (root.type != ClassNode.Type.ROOT) continue;
      processor.processClass(root.classStruct);
      for (var node : nodes.values()) {
        if (node == root || node.parent == root) dump(node, nest);
      }
    }
  }

  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var source = Files.writeString(scratch.resolve("OdditiesSubject.java"), """
      package oddity;
      import java.time.Instant;
      import java.time.Duration;
      import java.util.ArrayList;
      import java.util.List;
      public class OdditiesSubject {
        public int checks(int n) { assert n > 0; return n + 1; }
        public Instant cast(Object value) { return (Instant)value; }
        public Instant badCast(Object value) { return (Instant)value; }
        public Duration unknownCast(Object value) { return (Duration)value; }
        public Object debugUnknown(Object value) { return value; }
        public Object badDefinition(Object value) {
          List<Object> values = new ArrayList<>();
          values.add(value);
          return values.get(0);
        }
      }
      interface OdditiesContract {
        default Object checks(boolean ok) { assert ok; return new Object(); }
      }
      """);
    var classes = Files.createDirectory(scratch.resolve("classes"));
    int status = ToolProvider.getSystemJavaCompiler().run(null, null, null,
      "--release", "8", "-g", "-d", classes.toString(), source.toString());
    if (status != 0) throw new AssertionError("javac exit " + status);
    run(classes, false);
    run(classes, true);
  }
}
