import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Map;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.ClassesProcessor;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.gen.VarType;

class LiteralReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var cases = new ArrayList<String>();
    for (String field : new String[] {
      "boolean truth = true", "char escape = 10", "char single = 39", "char unit = 55296",
      "String text = \"É🐢\"", "long minLong = Long.MIN_VALUE", "int maxInt = Integer.MAX_VALUE",
      "float max = Float.MAX_VALUE", "double tiny = -Double.MIN_VALUE", "double nan = Double.NaN",
      "float negativeInfinity = Float.NEGATIVE_INFINITY", "double positiveInfinity = Double.POSITIVE_INFINITY",
      "double widened = (double)0.1f", "double degrees = 180.0 / Math.PI", "double rad = -Math.PI / 180.0",
      "float degreesFloat = 180.0f / (float)Math.PI", "double e = Math.E", "float negPi = (float)-Math.PI",
      "double negativeZero = -0.0"
    }) cases.add(field);
    for (int n=2; n<=20; n++) {
      cases.add("double times" + n + " = -Math.PI * " + n);
      cases.add("float over" + n + " = (float)(Math.PI / " + n + ")");
      for (int d=2; d<=12 && n<=12; d++) {
        cases.add("double ratio" + n + "_" + d + " = Math.PI * (" + n + ".0 / " + d + ".0)");
        cases.add("float ratioF" + n + "_" + d + " = (float)-Math.PI * (" + n + ".0f / " + d + ".0f)");
      }
    }
    var source = new StringBuilder("class Literals {");
    for (String field : cases) source.append("static final ").append(field).append(";\n");
    var file = Files.writeString(scratch.resolve("Literals.java"), source.append('}').toString());
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release","17","-d",scratch.toString(),file.toString()) != 0)
      throw new AssertionError("javac failed");
    for (var asIs : new String[]{"0","1"}) for (var ascii : new String[]{"0","1"}) {
      var engine = new Fernflower(null, Map.of("keep-literals",asIs,"ascii-strings",ascii,"include-runtime","0"),IFernflowerLogger.NO_OP);
      engine.addSource(scratch.resolve("Literals.class").toFile());
      var cp = DecompilerContext.getClassProcessor();
      cp.loadClasses(null);
      var root = cp.getMapRootClasses().get("Literals");
      DecompilerContext.startClass(new ImportCollector(root));
      DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE,root);
      for (var field : root.classStruct.getFields()) {
        var value = field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
        if (value == null) continue;
        var constant = root.classStruct.getPool().getPrimitiveConstant(value.getIndex()).value;
        var expr = new ConstExprent(new VarType(field.getDescriptor()),constant,null);
        var precedence = expr.getPrecedence();
        var text = expr.toJava(0);
        var tokens = text.getTokens().stream().map(token -> token.getStart() + "+" + token.getLength() + "/" + token.getClass().getSimpleName()).toList();
        System.out.println(asIs + ascii + " " + field.getName() + " " + precedence + " " + text.convertToStringAndAllowDataDiscard() + " " + String.join(",",tokens));
      }
    }
  }
}
