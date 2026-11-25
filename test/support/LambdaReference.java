// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.*;
import org.jetbrains.java.decompiler.main.rels.LambdaProcessor;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;

class LambdaReference {
  static class Imports extends ImportCollector {
    Imports(ClassNode root) { super(root); }
    List<String> entries() { return packImports(); }
  }

  public static void main(String[] args) throws Exception {
    var paths = Files.readAllLines(Path.of(args[0]));
    var addNames = ClassesProcessor.class.getDeclaredMethod("addClassNameToImport", ClassNode.class, ImportCollector.class);
    addNames.setAccessible(true);
    for (String mode : List.of("default", "flat")) {
      var engine = new Fernflower(new ConsoleFileSaver(null), Map.of(
        IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0",
        IFernflowerPreferences.DECOMPILE_INNER, mode.equals("flat") ? "0" : "1"
      ), IFernflowerLogger.NO_OP);
      for (String path : paths) engine.addSource(Path.of(path).toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      var known = processor.getMapRootClasses();
      for (var root : new TreeMap<>(known).values()) {
        if (root.type != ClassNode.Type.ROOT) continue;
        var imports = new Imports(root);
        DecompilerContext.startClass(imports);
        if (!(root.classStruct.isSynthetic() && "package-info".equals(root.simpleName)) &&
            !(root.classStruct.hasModifier(CodeConstants.ACC_MODULE) && root.classStruct.hasAttribute(StructGeneralAttribute.ATTRIBUTE_MODULE))) {
          try {
            new LambdaProcessor().processClass(root);
            addNames.invoke(null, root, imports);
          } catch (IllegalStateException ex) {
            System.out.println(mode + "\t" + root.classStruct.qualifiedName + "\trejected\t" + ex.getMessage());
          }
        }
        snapshot(mode, root, known, imports);
      }
      engine.clearContext();
    }
  }

  private static void snapshot(String mode, ClassNode root, Map<String, ClassNode> known, Imports imports) {
    var nodes = new ArrayList<ClassNode>();
    var ids = new IdentityHashMap<ClassNode, Integer>();
    ids.put(root, 0);
    nodes.add(root);
    for (int i = 0; i < nodes.size(); i++) {
      for (var child : nodes.get(i).nested) {
        if (!ids.containsKey(child)) {
          ids.put(child, nodes.size());
          nodes.add(child);
        }
      }
    }
    for (var n : nodes) {
      var info = n.lambdaInformation;
      String key = n.type == ClassNode.Type.LAMBDA ? n.simpleName : n.classStruct.qualifiedName;
      String children = n.nested.stream().map(c -> ids.get(c).toString()).collect(Collectors.joining(","));
      String lambda = info == null ? "-" : String.join("|", info.method_name, info.method_descriptor,
        info.content_class_name, info.content_method_name, info.content_method_descriptor,
        Integer.toString(info.content_method_invocation_type), info.content_method_key,
        Boolean.toString(info.is_method_reference), Boolean.toString(info.is_content_method_static));
      String imported = info == null ? "-" : imports.getShortName(info.content_class_name.replace('/', '.'));
      System.out.println(String.join("\t", mode, root.classStruct.qualifiedName, ids.get(n).toString(),
        n.type.name(), n.classStruct.qualifiedName, Objects.toString(n.simpleName), Objects.toString(n.enclosingMethod),
        Objects.toString(n.anonymousClassType), Objects.toString(ids.get(n.parent), "-"),
        children, Objects.toString(ids.get(known.get(key)), "-"), lambda, imported));
    }
    System.out.println(mode + "\t" + root.classStruct.qualifiedName + "\timports\t" + imports.entries());
  }
}
