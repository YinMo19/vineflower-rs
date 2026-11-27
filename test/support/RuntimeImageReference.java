import java.io.IOException;
import java.lang.module.ModuleDescriptor;
import java.net.URI;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Map;

public class RuntimeImageReference {
  private static final String DESCRIPTOR = "module-info.class";
  private static final String RESOURCE = "java/util/currency.data";

  public static void main(String[] args) throws IOException {
    try (var jrt = FileSystems.newFileSystem(URI.create("jrt:/"), Map.of("java.home", args[0]));
         var modules = Files.list(jrt.getPath("modules"))) {
      var roots = modules.toList();
      var names = new ArrayList<String>();
      for (var root : roots) {
        try (var descriptor = Files.newInputStream(root.resolve(DESCRIPTOR))) {
          names.add(ModuleDescriptor.read(descriptor).toNameAndVersion());
        }
      }
      for (int i = 0; i < roots.size(); i++) {
        var root = roots.get(i);
        var classes = new ArrayList<String>();
        var directories = new ArrayList<String>();
        var others = new ArrayList<String>();
        try (var walk = Files.walk(root)) {
          walk.map(root::relativize).map(Path::toString).forEach(name -> {
            if (name.endsWith("/")) {
              directories.add("dir\t" + name.substring(0, name.length() - 1));
            } else if (name.endsWith(".class")) {
              classes.add("class\t" + name.substring(0, name.length() - 6));
            } else {
              others.add("other\t" + name);
            }
          });
        }
        System.out.println("module\t" + names.get(i));
        classes.forEach(System.out::println);
        directories.forEach(System.out::println);
        others.forEach(System.out::println);
      }

      var base = jrt.getPath("modules", "java.base");
      Files.copy(base.resolve(RESOURCE), Path.of(args[1], "currency.data"));
      Files.copy(base.resolve("java/util/ListIterator.class"), Path.of(args[1], "ListIterator.class"));
    }
  }
}
