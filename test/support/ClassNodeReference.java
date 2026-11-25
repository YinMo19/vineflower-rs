// SPDX-License-Identifier: Apache-2.0

import java.nio.file.*;
import java.util.*;
import java.util.stream.Collectors;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.NewExprent;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.gen.VarType;

class ClassNodeReference {
  private static class Imports extends ImportCollector {
    Imports(ClassNode root) { super(root); }
    List<String> packages() { return packImports(); }
  }

  public static void main(String[] args) throws Exception {
    var paths = Files.readAllLines(Path.of(args[0]));
    for (String mode : List.of("default", "verify", "flat")) {
      var engine = new Fernflower(new org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver(null), Map.of(
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0",
        IFernflowerPreferences.VERIFY_ANONYMOUS_CLASSES, mode.equals("verify") ? "1" : "0",
        IFernflowerPreferences.DECOMPILE_INNER, mode.equals("flat") ? "0" : "1"
      ), IFernflowerLogger.NO_OP);
      for (String path : paths) engine.addSource(Path.of(path).toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      var nodes = new TreeMap<>(processor.getMapRootClasses());
      for (var node : nodes.values()) {
        if (node.type != ClassNode.Type.ROOT) continue;
        var imports = new Imports(node);
        DecompilerContext.startClass(imports);
        visit(mode, node, imports);
        System.out.println(mode + "\timports\t" + node.classStruct.qualifiedName + "\t" + imports.packages());
      }
      engine.clearContext();
    }
  }

  private static void visit(String mode, ClassNode node, Imports imports) {
    StructClass cl = node.classStruct;
    DecompilerContext.setProperty(DecompilerContext.CURRENT_CLASS_NODE, node);
    var alloc = new NewExprent(new VarType(cl.qualifiedName, true), Collections.emptyList(), null);
    var names = new TreeSet<String>();
    names.add(cl.qualifiedName);
    if (cl.superClass != null) names.add(cl.superClass.getString());
    Collections.addAll(names, cl.getInterfaceNames());
    var inner = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_INNER_CLASSES);
    if (inner != null) for (var entry : inner.getEntries()) names.add(entry.innerName);
    var resolved = names.stream().map(n -> imports.getShortNameInClassContext(n.replace('/', '.'))).toList();
    var nested = node.nested.stream().map(n -> n.classStruct.qualifiedName).collect(Collectors.toList());
    System.out.println(String.join("\t", mode, "node", cl.qualifiedName, node.type.toString(), Integer.toString(node.access),
      Objects.toString(node.simpleName), Objects.toString(node.enclosingMethod), new TreeSet<>(node.enclosingClasses).toString(),
      node.parent == null ? "null" : node.parent.classStruct.qualifiedName, nested.toString(),
      Objects.toString(node.anonymousClassType), alloc.getExprType().toString(), resolved.toString()));
    for (ClassNode child : node.nested) visit(mode, child, imports);
  }
}
