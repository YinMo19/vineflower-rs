// SPDX-License-Identifier: Apache-2.0

import java.lang.annotation.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.exps.Exprent;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructMember;
import org.jetbrains.java.decompiler.util.DataInputFullStream;
import static org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute.*;

class AnnotationIdsReference {
  public static void main(String[] args) throws Exception {
    new Fernflower(null, Map.of(), IFernflowerLogger.NO_OP);
    for (String name : List.of("IdDecor", "AnnotationIdFixture")) {
      byte[] bytes = AnnotationIdsReference.class.getResourceAsStream("/" + name + ".class").readAllBytes();
      Files.write(Path.of(args[0], name + ".class"), bytes);
      DecompilerContext.startClass(null);
      var cls = StructClass.create(new DataInputFullStream(bytes), true);
      var ids = new ArrayList<Integer>();
      cls.getFields().forEach(field -> collect(field, ids));
      cls.getMethods().forEach(method -> collect(method, ids));
      collect(cls, ids);
      if (cls.getRecordComponents() != null) {
        cls.getRecordComponents().forEach(component -> collect(component, ids));
      }
      System.out.println(ids);
    }
  }

  private static void collect(StructMember member, List<Integer> ids) {
    for (var key : List.of(ATTRIBUTE_RUNTIME_VISIBLE_ANNOTATIONS, ATTRIBUTE_RUNTIME_INVISIBLE_ANNOTATIONS)) {
      var annotations = member.getAttribute(key);
      if (annotations != null) annotations.getAnnotations().forEach(expr -> collect(expr, ids));
    }
    for (var key : List.of(ATTRIBUTE_RUNTIME_VISIBLE_TYPE_ANNOTATIONS, ATTRIBUTE_RUNTIME_INVISIBLE_TYPE_ANNOTATIONS)) {
      var annotations = member.getAttribute(key);
      if (annotations != null) annotations.getAnnotations().forEach(a -> collect(a.getAnnotation(), ids));
    }
    for (var key : List.of(ATTRIBUTE_RUNTIME_VISIBLE_PARAMETER_ANNOTATIONS, ATTRIBUTE_RUNTIME_INVISIBLE_PARAMETER_ANNOTATIONS)) {
      var annotations = member.getAttribute(key);
      if (annotations != null) {
        annotations.getParamAnnotations().forEach(param -> param.forEach(expr -> collect(expr, ids)));
      }
    }
    var defaultValue = member.getAttribute(ATTRIBUTE_ANNOTATION_DEFAULT);
    if (defaultValue != null) collect(defaultValue.getDefaultValue(), ids);
  }

  private static void collect(Exprent expression, List<Integer> ids) {
    expression.getAllExprents().forEach(child -> collect(child, ids));
    ids.add(expression.id);
  }
}

@Retention(RetentionPolicy.RUNTIME)
@interface IdChild { String value(); }

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE, ElementType.FIELD, ElementType.METHOD, ElementType.PARAMETER, ElementType.RECORD_COMPONENT})
@interface IdDecor {
  IdChild nested() default @IdChild("default");
  int[] array() default {};
  Class<?> klass() default int.class;
  RetentionPolicy policy() default RetentionPolicy.CLASS;
}

@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE_USE)
@interface IdType { int value(); }

@Target(ElementType.PARAMETER)
@interface IdInvisible { int value(); }

@IdDecor(nested = @IdChild("record"), array = {3, 4}, klass = String.class, policy = RetentionPolicy.SOURCE)
record AnnotationIdFixture(@IdDecor @IdType(5) String value) {
  @IdDecor void method(@IdDecor @IdInvisible(6) @IdType(7) Object arg) {
    @IdType(8) String local = (@IdType(9) String) arg;
  }
}
