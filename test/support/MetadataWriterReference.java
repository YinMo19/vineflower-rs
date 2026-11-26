// SPDX-License-Identifier: Apache-2.0

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HexFormat;
import java.util.List;
import java.util.Map;
import javax.tools.ToolProvider;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleFileSaver;

import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.token.ClassTextToken;
import org.jetbrains.java.decompiler.util.token.FieldTextToken;
import org.jetbrains.java.decompiler.util.token.MethodTextToken;

class MetadataWriterReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var paths = compileFixtures(scratch);
    var fixtures = List.of("pkg/package-info", "module-info", "module-info");
    for (int profile = 0; profile < 3; ++profile) {
      for (int i = 0; i < fixtures.size(); ++i) {
        String name = fixtures.get(i);
        var options = Map.<String, Object>of(
          "include-runtime", "0",
          "ascii-strings", profile == 1 ? "1" : "0",
          "new-line-separator", profile == 1 ? "0" : "1",
          "indent-string", profile == 1 ? "  " : "   ",
          "preferred-line-length", "24",
          "remove-imports", profile == 2 ? "1" : "0"
        );
        var engine = new Fernflower(new ConsoleFileSaver(null), options, IFernflowerLogger.NO_OP);
        engine.addSource(paths.get(i).toFile());
        if (i == 0) engine.addLibrary(scratch.resolve("foreign").toFile());
        var processor = DecompilerContext.getClassProcessor();
        processor.loadClasses(null);
        var root = processor.getMapRootClasses().get(name);
        processor.processClass(root.classStruct);
        var buffer = new TextBuffer();
        processor.writeClass(root.classStruct, buffer);

        var packed = ImportCollector.class.getDeclaredMethod("packImports");
        packed.setAccessible(true);
        @SuppressWarnings("unchecked")
        var imports = (List<String>) packed.invoke(DecompilerContext.getImportCollector());
        var text = buffer.convertToStringAndAllowDataDiscard();
        System.out.println("profile=" + profile + ",fixture=" + i + ",root=" + name);
        System.out.println("text=" + HexFormat.of().formatHex(text.getBytes(StandardCharsets.UTF_8)));
        System.out.println("imports=" + String.join(",", imports));
        printTokens(buffer);
        buffer.reformat();
        System.out.println("wrapped=" + HexFormat.of().formatHex(buffer.convertToStringAndAllowDataDiscard().getBytes(StandardCharsets.UTF_8)));
        printTokens(buffer);
        engine.clearContext();
      }
    }
  }

  private static void printTokens(TextBuffer buffer) {
    for (var token : buffer.getTokens()) {
      String header = token.getStart() + "|" + token.getLength() + "|" + token.isDeclaration() + "|";
      if (token instanceof ClassTextToken cls) {
        System.out.println(header + "class|" + cls.qualifiedName);
      } else if (token instanceof MethodTextToken method) {
        System.out.println(header + "method|" + method.className + "|" + method.name + "|" + method.descriptor);
      } else if (token instanceof FieldTextToken field) {
        System.out.println(header + "field|" + field.className + "|" + field.name + "|" + field.descriptor.descriptorString);
      } else {
        throw new AssertionError(token.getClass());
      }
    }
  }

  private static List<Path> compileFixtures(Path root) throws Exception {
    var foreign = root.resolve("foreign");
    compile(root.resolve("foreign-src"), foreign, Map.of("ext/Group.java", """
      package ext;
      public class Group {
        public static class Member {}
      }
      """), List.of());

    var packageSources = new java.util.HashMap<>(annotations());
    packageSources.put("pkg/package-info.java", """
      @meta.Hidden
      @meta.Single("one")
      @meta.Meta.Marker
      @first.Ambiguous
      @second.Ambiguous
      @meta.Meta.Config(
        words = {"rétro", "long enough to exceed the preferred line width"},
        number = (byte) 3, letter = 'Ω', switches = {true, false},
        types = {ext.Group.Member.class, int.class, java.util.Map.Entry.class},
        mode = meta.Meta.Mode.SECOND,
        nested = {@meta.Meta.Note(name = "inner", flags = {4}),
                  @meta.Meta.Note(name = "inner", flags = {4})},
        empty = {}, single = {9}, precise = 91.25d, width = 9L)
      package pkg;
      """);
    for (var name : List.of("first", "second")) {
      packageSources.put(name + "/Ambiguous.java",
        "package " + name + "; @java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME) public @interface Ambiguous {}");
    }
    compile(root.resolve("package-src"), root.resolve("package"), packageSources,
      List.of("-classpath", foreign.toString()));

    var moduleSources = new java.util.HashMap<>(annotations());
    moduleSources.put("module-info.java", """
      @meta.Hidden
      @meta.Meta.Marker
      @meta.Meta.Config(types = {api.Api.Service.class}, words = {"module"}, number = 1)
      module example.writer {
        requires transitive java.sql;
        requires static java.desktop;
        requires static transitive java.logging;
        exports api;
        exports privateapi to target.reader, target.tool;
        opens reflect to target.tool, target.reader;
        opens unqualified;
        uses api.Api.Service;
        uses java.lang.Thread.UncaughtExceptionHandler;
        provides api.Api.Service with api.Api.Second, api.Api.First;
      }
      """);
    moduleSources.put("api/Api.java", """
      package api;
      public class Api {
        public interface Service {}
        public static class First implements Service {}
        public static class Second implements Service {}
      }
      """);
    moduleSources.put("privateapi/Value.java", "package privateapi; public class Value {}");
    moduleSources.put("reflect/Value.java", "package reflect; public class Value {}");
    moduleSources.put("unqualified/Value.java", "package unqualified; public class Value {}");
    compile(root.resolve("module-src"), root.resolve("module"), moduleSources, List.of());

    compile(root.resolve("open-src"), root.resolve("open"), Map.of("module-info.java",
      "@Deprecated open module example.open { }"), List.of());
    return List.of(root.resolve("package"), root.resolve("module"), root.resolve("open"));
  }

  private static Map<String, String> annotations() {
    return Map.of(
      "meta/Meta.java", """
        package meta;
        import java.lang.annotation.*;
        public class Meta {
          @Target({ElementType.PACKAGE, ElementType.MODULE}) @Retention(RetentionPolicy.RUNTIME)
          public @interface Marker {}
          @Target({ElementType.PACKAGE, ElementType.MODULE}) @Retention(RetentionPolicy.RUNTIME)
          public @interface Config {
            byte number() default 0;
            char letter() default 'x';
            boolean[] switches() default {};
            Class<?>[] types() default {};
            Mode mode() default Mode.FIRST;
            String[] words() default {};
            Note[] nested() default {};
            int[] empty() default {};
            int[] single() default {};
            double precise() default 0;
            long width() default 0;
          }
          public enum Mode { FIRST, SECOND }
          public @interface Note { String name(); int[] flags(); }
        }
        """,
      "meta/Hidden.java", """
        package meta;
        import java.lang.annotation.*;
        @Target({ElementType.PACKAGE, ElementType.MODULE}) @Retention(RetentionPolicy.CLASS)
        public @interface Hidden {}
        """,
      "meta/Single.java", """
        package meta;
        import java.lang.annotation.*;
        @Target({ElementType.PACKAGE, ElementType.MODULE}) @Retention(RetentionPolicy.RUNTIME)
        public @interface Single { String value(); }
        """);
  }

  private static void compile(Path sourceRoot, Path classes, Map<String, String> files, List<String> extra)
    throws Exception {
    Files.createDirectories(classes);
    var arguments = new ArrayList<>(List.of("--release", "17", "-Xlint:-module", "-d", classes.toString()));
    arguments.addAll(extra);
    for (var entry : new java.util.TreeMap<>(files).entrySet()) {
      var file = sourceRoot.resolve(entry.getKey());
      Files.createDirectories(file.getParent());
      Files.writeString(file, entry.getValue());
      arguments.add(file.toString());
    }
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, arguments.toArray(String[]::new)) != 0) {
      throw new AssertionError("javac failed for " + sourceRoot);
    }
  }
}
