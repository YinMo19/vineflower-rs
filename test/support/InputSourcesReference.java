import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Map;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IContextSource;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.struct.ContextUnit;
import org.jetbrains.java.decompiler.struct.StructContext;
import static org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute.ATTRIBUTE_RUNTIME_VISIBLE_ANNOTATIONS;

public class InputSourcesReference {
  public static void main(String[] args) throws Exception {
    var scratch = Path.of(args[0]);
    var folder = Files.createDirectory(scratch.resolve("folder"));
    var assets = Files.createDirectory(folder.resolve("assets"));
    var children = Files.createDirectory(folder.resolve("children"));
    Files.write(assets.resolve("note.txt"), bytes("native folder"));
    Files.write(folder.resolve("IdDecor.class"), classBytes("IdDecor"));
    makeZip(children.resolve("nested.zip"), "", false, "InputNestedFixture");
    var alias = scratch.resolve("archive.data");
    makeZip(alias, "", true, "InputNestedFixture");
    var longComment = scratch.resolve("long-comment.data");
    makeZip(longComment, "z".repeat(1024), false, "InputNestedFixture");
    var empty = scratch.resolve("empty.data");
    try (var zip = new ZipOutputStream(Files.newOutputStream(empty))) {}

    var renamed = scratch.resolve("Alias.class");
    byte[] decorated = classBytes("IdDecor");
    byte[] withTrailer = Arrays.copyOf(decorated, decorated.length + 24);
    System.arraycopy(new byte[]{80, 75, 5, 6}, 0, withTrailer, decorated.length, 4);
    Files.write(renamed, withTrailer);

    var broken = Files.writeString(scratch.resolve("broken.zip"), "bad zip");
    var brokenFolder = Files.createDirectory(scratch.resolve("broken-folder"));
    Files.copy(broken, brokenFolder.resolve("child.jar"));
    var brokenClass = Files.writeString(scratch.resolve("broken.class"), "bad class");

    var context = freshContext();
    context.addSpace(folder.toFile(), true);
    dump("folder", context);
    System.out.println("directory-resource\t" + resource(context.getUnits().get(0), "/assets/note.txt"));
    for (var path : new String[]{"assets", "absent"}) {
      try {
        resource(context.getUnits().get(0), path);
        throw new AssertionError("directory source read " + path);
      } catch (IOException expected) {}
    }
    Files.write(scratch.resolve("InputAddedFixture.class"), classBytes("InputAddedFixture"));
    var added = folder.resolve("InputAddedFixture.class");
    Files.copy(scratch.resolve("InputAddedFixture.class"), added);
    context.reloadContext();
    dump("reloaded", context);
    Files.delete(added);

    context = freshContext();
    context.addSpace(alias.toFile(), false);
    context.addSpace(longComment.toFile(), true);
    context.addSpace(empty.toFile(), true);
    context.addSpace(scratch.resolve("missing.jar").toFile(), true);
    dump("archives", context);
    var archive = context.getUnits().get(0);
    System.out.println("duplicate-resource\t" + resource(archive, "copy-a.txt"));
    System.out.println("utf8-resource\t" + resource(archive, "unicodé.txt"));
    for (var name : new String[]{"alpha.txt", "beta.txt"}) {
      System.out.println("raw-name-resource\t" + name + "\t" + resource(archive, name));
    }
    System.out.println("archive-class\t" + context.getClass("InputNestedFixture").qualifiedName);
    if (!resource(archive, "empty/").isEmpty()) {
      throw new AssertionError("ZIP directory resource is not empty");
    }
    try {
      resource(archive, "absent");
      throw new AssertionError("read absent ZIP entry");
    } catch (NullPointerException expected) {}

    context = freshContext();
    context.addSpace(renamed.toFile(), true);
    dump("renamed", context);
    var annotations = context.getClass("IdDecor").getAttribute(ATTRIBUTE_RUNTIME_VISIBLE_ANNOTATIONS);
    System.out.println("annotation-ids\t" + annotations.getAnnotations().stream().map(a -> a.id).toList());

    for (var path : new Path[]{broken, brokenFolder, brokenClass}) {
      try {
        freshContext().addSpace(path.toFile(), true);
        throw new AssertionError("accepted malformed input " + path);
      } catch (UncheckedIOException expected) {
        System.out.println("rejected\t" + path.getFileName());
      }
    }
  }

  private static StructContext freshContext() {
    new Fernflower(null, Map.of("include-runtime", "0"), IFernflowerLogger.NO_OP);
    return DecompilerContext.getStructContext();
  }

  private static void dump(String label, StructContext context) throws Exception {
    System.out.println(label);
    for (var unit : context.getUnits()) {
      System.out.println("unit\t" + unit.isOwn() + "\t" + unit.isRoot() + "\t" + unit.getName());
      var raw = source(unit).getEntries();
      for (var entry : raw.classes()) {
        printEntry("raw-class", entry);
      }
      for (var name : unit.getClassNames()) {
        System.out.println("class\t" + name);
      }
      for (var dir : unit.getDirectoryNames()) {
        System.out.println("dir\t" + dir);
      }
      for (var entry : unit.getOtherEntries()) {
        printEntry("other", entry);
      }
    }
  }

  private static void printEntry(String kind, IContextSource.Entry entry) {
    System.out.println(kind + "\t" + entry.basePath() + "\t" + entry.multirelease() + "\t" + entry.path());
  }

  private static IContextSource source(ContextUnit unit) throws Exception {
    var field = ContextUnit.class.getDeclaredField("source");
    field.setAccessible(true);
    return (IContextSource) field.get(unit);
  }

  private static String resource(ContextUnit unit, String path) throws Exception {
    try (var stream = source(unit).getInputStream(path)) {
      return new String(stream.readAllBytes(), StandardCharsets.UTF_8);
    }
  }

  private static byte[] classBytes(String name) throws IOException {
    try (var stream = InputSourcesReference.class.getResourceAsStream("/" + name + ".class")) {
      return stream.readAllBytes();
    }
  }

  private static byte[] bytes(String text) {
    return text.getBytes(StandardCharsets.UTF_8);
  }

  private static void makeZip(Path path, String comment, boolean rawNames, String name) throws IOException {
    try (var zip = new ZipOutputStream(Files.newOutputStream(path))) {
      zip.setComment(comment);
      entry(zip, "zeta/a.txt", bytes("nested resource"));
      entry(zip, "empty/", new byte[0]);
      entry(zip, name + ".class", classBytes(name));
      entry(zip, "META-INF/versions/11/" + name + ".class", classBytes(name));
      entry(zip, "META-INF/versions/11/value.txt", bytes("versioned"));
      entry(zip, "META-INF/versions/１１/value-unicode.txt", bytes("versioned using BMP digits"));
      entry(zip, "META-INF/versions/non-number/value.txt", bytes("ordinary"));
      for (var raw : new String[]{"alpha.txt", "beta.txt"}) {
        // Info-ZIP Unicode Path field. Both entries advertise the same alternate name.
        var crc = new CRC32();
        crc.update(bytes(raw));
        var unicode = bytes("common.txt");
        var extra = ByteBuffer.allocate(9 + unicode.length).order(ByteOrder.LITTLE_ENDIAN);
        extra.putShort((short) 0x7075).putShort((short) (5 + unicode.length));
        extra.put((byte) 1).putInt((int) crc.getValue()).put(unicode);
        var file = new ZipEntry(raw);
        file.setExtra(extra.array());
        zip.putNextEntry(file);
        zip.write(bytes(raw));
        zip.closeEntry();
      }
      entry(zip, "copy-a.txt", bytes("first"));
      entry(zip, "copy-b.txt", bytes("second"));
      entry(zip, "unicodé.txt", bytes("UTF-8 path and payload"));
    }
    if (rawNames) {
      byte[] zipBytes = Files.readAllBytes(path);
      byte[] duplicate = bytes("copy-b.txt");
      for (int i = 0; i + duplicate.length <= zipBytes.length; ++i) {
        if (Arrays.equals(zipBytes, i, i + duplicate.length, duplicate, 0, duplicate.length)) {
          zipBytes[i + 5] = 'a';
        }
        if (zipBytes[i] == 80 && zipBytes[i + 1] == 75) {
          if (zipBytes[i + 2] == 3 && zipBytes[i + 3] == 4) {
            zipBytes[i + 7] &= ~8;
          } else if (zipBytes[i + 2] == 1 && zipBytes[i + 3] == 2) {
            zipBytes[i + 9] &= ~8;
          }
        }
      }
      Files.write(path, zipBytes);
    }
  }

  private static void entry(ZipOutputStream out, String path, byte[] data) throws IOException {
    out.putNextEntry(new ZipEntry(path));
    out.write(data);
    out.closeEntry();
  }
}

class InputNestedFixture {}

class InputAddedFixture {}
