import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.decompiler.ConsoleDecompiler;

class DriverCliReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var library = Files.createDirectory(scratch.resolve("library"));
    var own = Files.createDirectory(scratch.resolve("own"));
    var libSource = Files.writeString(scratch.resolve("Library.java"), """
      package external;
      public class Library {
        public static <T> T identity(T value) { return value; }
      }
      """);
    var ownSource = Files.writeString(scratch.resolve("Subject.java"), """
      package fixture;
      import external.Library;
      public class Subject {
        public String text(int value) {
          if (value < 0) {
            return Library.identity("negative");
          }
          return Library.identity("ok");
        }
      }
      """);
    var compiler = ToolProvider.getSystemJavaCompiler();
    int status = compiler.run(null, null, null, "--release", "17", "-g", "-d",
      library.toString(), libSource.toString());
    if (status != 0) throw new AssertionError(status);
    status = compiler.run(null, null, null, "--release", "17", "-g", "-cp", library.toString(),
      "-d", own.toString(), ownSource.toString());
    if (status != 0) throw new AssertionError(status);

    var resource = Files.writeString(own.resolve("fixture/resource.txt"), "kept\n");
    var jar = scratch.resolve("source.jar");
    try (var zip = new ZipOutputStream(Files.newOutputStream(jar))) {
      put(zip, "META-INF/MANIFEST.MF", """
        Created-By: CLI fixture
        Manifest-Version: 1.0

        Name: fixture/resource.txt
        Description: A continued manifest value that should be reconstructed
         and wrapped by the archive saver.

        """.getBytes(StandardCharsets.UTF_8));
      put(zip, "fixture/Subject.class", Files.readAllBytes(own.resolve("fixture/Subject.class")));
      put(zip, "fixture/resource.txt", Files.readAllBytes(resource));
    }

    var config = Files.writeString(scratch.resolve("args.cfg"), """
      -jrt=0
      -bsm=1
      -dcl=1
      --silent
      """);
    var external = "-e=" + library;
    var reference = Files.createDirectory(scratch.resolve("reference"));
    ConsoleDecompiler.main(new String[] {
      "-cfg=" + config, "--file", external, own.toString(), reference.resolve("directory.jar").toString()
    });
    ConsoleDecompiler.main(new String[] {
      "-cfg=" + config, "--file", external, jar.toString(), reference.resolve("archive.jar").toString()
    });
    // Legacy JarOutputStream reports the duplicate manifest when it copies resources.
    var savedStdout = System.out;
    try (var discarded = new java.io.PrintStream(java.io.OutputStream.nullOutputStream())) {
      System.setOut(discarded);
      ConsoleDecompiler.main(new String[] {
        "-cfg=" + config, "--legacy-saving", external, jar.toString(), reference.resolve("legacy").toString()
      });
    } finally {
      System.setOut(savedStdout);
    }
    ConsoleDecompiler.main(new String[] {
      "-cfg=" + config, "--folder", external, jar.toString(), reference.resolve("folder").toString()
    });
    ConsoleDecompiler.main(new String[] {
      "--dump-text-tokens", "-cfg", config.toString(), external, own.resolve("fixture/Subject.class").toString()
    });
  }

  private static void put(ZipOutputStream zip, String name, byte[] data) throws Exception {
    zip.putNextEntry(new ZipEntry(name));
    zip.write(data);
    zip.closeEntry();
  }
}
