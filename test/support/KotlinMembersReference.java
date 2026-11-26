// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Map;
import java.util.stream.Collectors;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.Init;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.InitializerProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.vineflower.kotlin.KotlinChooser;
import org.vineflower.kotlin.struct.*;
import org.vineflower.kotlin.util.KotlinObjectProcessors;

class KotlinMembersReference {
  public static void main(String[] args) throws Exception {
    Init.init();
    Path scratch = Path.of(args[0]);
    Path fixtures = Path.of(Files.readString(scratch.resolve("fixtures")));
    var engine = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", "0",
      "kt-enable", "0", "kt-export-metadata", "1"), IFernflowerLogger.NO_OP);
    try {
      engine.addSource(fixtures.resolve("kt").toFile());
      engine.addSource(fixtures.resolve("ktold").toFile());
      var context = DecompilerContext.getStructContext();
      var classes = context.getOwnClasses().stream().sorted(Comparator.comparing(c -> c.qualifiedName)).toList();
      var chooser = new KotlinChooser();
      for (var cl : classes) {
        if (chooser.isLanguage(cl)) throw new AssertionError("Export alone selected Kotlin output");
        printClass(cl);
      }

      var processor = DecompilerContext.getClassProcessor();
      processor.loadClasses(null);
      for (String name : new String[]{"pkg/TestCompanionObject", "pkg/TestObject"}) {
        var node = processor.getMapRootClasses().get(name);
        processor.processClass(node.classStruct);
        InitializerProcessor.extractInitializers(node.getWrapper());
        InitializerProcessor.hideInitalizers(node.getWrapper());
        KotlinObjectProcessors.parseWithCompanion(node);
        KotlinObjectProcessors.markObjectInstance(node.getWrapper());
        System.out.println("processed");
        printClass(node.classStruct);
        for (var nested : node.nested) {
          if (!nested.classStruct.qualifiedName.equals(name)) printClass(nested.classStruct);
        }
      }
    } finally {
      engine.clearContext();
    }

    var library = new Fernflower(new ConsoleFileSaver(null), Map.of("include-runtime", "0",
      "kt-enable", "0", "kt-export-metadata", "0"), IFernflowerLogger.NO_OP);
    try {
      library.addLibrary(fixtures.resolve("kt/ext/Person.class").toFile());
      var cl = DecompilerContext.getStructContext().getClass("ext/Person");
      var method = cl.getMethod("getName", "()Ljava/lang/String;");
      System.out.println("library|" + cl.isOwn() + "|" + element(method.getAttribute(KElement.KEY)));
      if (new KotlinChooser().isLanguage(cl)) throw new AssertionError("Kotlin is disabled");
      KotlinChooser.parseMetadataFor(cl);
      System.out.println("library|" + cl.isOwn() + "|" + element(method.getAttribute(KElement.KEY)));
      printClass(cl);
      for (String subject : new String[]{"KotlinMetadataBadMemberSubject", "KotlinMetadataBadFacadeSubject"}) {
        Path path = scratch.resolve(subject + ".class");
        try (var input = KotlinMembersReference.class.getResourceAsStream("/kotlin/" + subject + ".class")) {
          Files.copy(input, path);
        }
        library.addLibrary(path.toFile());
        printRetry(DecompilerContext.getStructContext().getClass("kotlin/" + subject));
      }
    } finally {
      library.clearContext();
    }
  }

  private static void printRetry(StructClass cl) {
    DecompilerContext.setProperty("kt-enable", "1");
    var method = cl.getMethod("first", "()V");
    var chooser = new KotlinChooser();
    var selected = chooser.isLanguage(cl);
    var first = method.getAttribute(KElement.KEY);
    var selectedAgain = chooser.isLanguage(cl);
    var updated = method.getAttribute(KElement.KEY);
    System.out.println("retry|" + selected + "|" + selectedAgain + "|" + (first == updated));
    printClass(cl);
  }

  private static void printClass(StructClass cl) {
    System.out.println("class|" + cl.qualifiedName + "|" + element(cl.getAttribute(KElement.KEY)));
    System.out.println("primary|" + element(cl.getAttribute(KConstructor.PRIMARY_CONSTRUCTOR)));
    for (var field : cl.getFields()) {
      System.out.println("field|" + field.getName() + "|" + field.getDescriptor() + "|" + element(field.getAttribute(KElement.KEY)));
    }
    for (var method : cl.getMethods()) {
      System.out.println("method|" + method.getName() + "|" + method.getDescriptor() + "|" + element(method.getAttribute(KElement.KEY))
        + "|" + method.getAttribute(KProperty.PropertyMethod.KEY));
    }
  }

  private static String element(KElement value) {
    if (value == null) return "-";
    if (value instanceof KClass cl) return "class|" + cl.flags();
    if (value instanceof KFile file) return "file|" + file.multifileName();
    if (value instanceof KMultifileFacade facade) return "facade|" + String.join(",", facade.files());
    if (value instanceof KFunctionReference) return "reference";
    if (value == KFunction.FAILED_LAMBDA) return "failed-lambda";
    if (value instanceof KHiddenElement hidden) return "hidden|" + hidden.name();
    if (value instanceof KFunction function) {
      return "function|" + function.name() + "|" + function.flags() + "|" + params(function.parameters())
        + "|" + function.returnType() + "|" + function.receiverType()
        + "|" + function.typeParameters().stream().map(KTypeParameter::name).collect(Collectors.joining(","))
        + "|" + function.contextReceiverTypes().stream().map(KType::toString).collect(Collectors.joining(","))
        + "|" + (function.contract() != null) + "|" + function.knownOverride();
    }
    if (value instanceof KConstructor constructor) {
      return "constructor|" + constructor.flags() + "|" + constructor.isPrimary() + "|" + params(constructor.parameters());
    }
    if (value instanceof KProperty property) {
      return "property|" + property.name() + "|" + property.flags() + "|" + property.type()
        + "|" + (property.getter() == null ? "-" : property.getter().flags())
        + "|" + (property.setter() == null ? "-" : property.setter().flags())
        + "|" + property.setterParamName()
        + "|" + (property.underlyingField() == null ? "-" : property.underlyingField().getName())
        + "|" + property.annotations().stream().map(anno -> anno.getClassName()).collect(Collectors.joining(","))
        + "|" + (property.initializer() != null);
    }
    throw new AssertionError(value);
  }

  private static String params(KParameter[] values) {
    return Arrays.stream(values).map(p -> p.name() + ":" + p.flags() + ":" + p.type()
      + ":" + p.varargType() + ":" + p.typeId()).collect(Collectors.joining(","));
  }
}
