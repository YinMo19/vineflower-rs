// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Path;
import java.util.Map;
import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.*;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.exps.TypeAnnotation;
import org.jetbrains.java.decompiler.struct.*;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.vineflower.kotlin.*;
import org.vineflower.kotlin.expr.KNewExprent;
import org.vineflower.kotlin.struct.*;
import org.vineflower.kotlin.util.KUtils;

class KotlinAnnotationsReference {
  public static void main(String[] args) {
    Init.init();
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", "", "preferred-line-length", "36"), IFernflowerLogger.NO_OP);
    try {
      engine.addSource(Path.of(args[0]).toFile());
      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      var writer = new KotlinWriter();
      for (var name : processor.getMapRootClasses().keySet().stream().sorted().toList()) {
        var node = processor.getMapRootClasses().get(name);
        var cl = node.classStruct;
        var collector = new KotlinImportCollector(new ImportCollector(node));
        DecompilerContext.startClass(collector);
        KotlinChooser.parseMetadataFor(cl);
        var body = new TextBuffer();
        append(body, cl, cl, TypeAnnotation.CLASS_TYPE_PARAMETER);
        for (var fd : cl.getFields()) append(body, cl, fd, TypeAnnotation.FIELD);
        for (var mt : cl.getMethods()) {
          append(body, cl, mt, TypeAnnotation.METHOD_RETURN_TYPE);
          for (int i = 0; i < mt.methodDescriptor().params.length; ++i) {
            boolean nullable = KotlinWriter.processParameterAnnotations(body, mt, i);
            body.append(Boolean.toString(nullable)).appendLineSeparator();
          }
          var def = mt.getAttribute(StructGeneralAttribute.ATTRIBUTE_ANNOTATION_DEFAULT);
          if (def != null) {
            var value = KUtils.replaceExprent(def.getDefaultValue());
            if (value instanceof KNewExprent array) array.setInAnnotation(true);
            body.append(value.toJava(1)).appendLineSeparator();
          }
        }
        body.reformat();
        var header = new TextBuffer();
        writer.writeClassHeader(cl, header, collector);
        System.out.println(name);
        System.out.print(header.convertToStringAndAllowDataDiscard());
        System.out.print(body.convertToStringAndAllowDataDiscard());
      }
    } finally { engine.clearContext(); }
  }

  private static void append(TextBuffer body, StructClass cl, StructMember member, int target) {
    KotlinWriter.appendAnnotations(body, 1, member, cl == member ? -1 : target);
    KotlinWriter.appendJvmAnnotations(body, 1, member, cl.hasModifier(CodeConstants.ACC_INTERFACE),
      cl.getAttribute(KElement.KEY) instanceof KFile, cl.getPool(), target);
  }
}
