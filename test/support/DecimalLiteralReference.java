// SPDX-License-Identifier: Apache-2.0

import java.io.BufferedWriter;
import java.io.OutputStreamWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.SplittableRandom;
import javax.tools.ToolProvider;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.modules.decompiler.exps.ConstExprent;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.gen.VarType;

class DecimalLiteralReference {
  private static final int[] FLOAT_FIELDS = {
    0, 0x80000000, 1, 0x80000001, 0x007fffff, 0x00800000, 0x3f800001,
    0x4b800001, 0x52800000, 0x5e800001, 0x7f7fffff,
  };
  private static final long[] DOUBLE_FIELDS = {
    0, 0x8000000000000000L, 1, 0x8000000000000001L, 0x000fffffffffffffL,
    0x0010000000000000L, 0x3ff0000000000001L, 0x4340000000000001L,
    0x43d0000000000001L, 0x44b52d02c7e14af6L, 0x7fefffffffffffffL,
  };

  public static void main(String[] args) throws Exception {
    if (Runtime.version().feature() != 17) {
      throw new AssertionError("The finite literal reference uses JDK 17 decimal conversion");
    }
    Path scratch = Path.of(args[0]);
    Path classes = Files.createDirectory(scratch.resolve("classes"));
    var source = new StringBuilder("class DecimalConstants {\n");
    for (int i = 0; i < FLOAT_FIELDS.length; i++) {
      source.append("static final float f").append(i).append(" = ")
        .append(Float.toHexString(Float.intBitsToFloat(FLOAT_FIELDS[i]))).append("F;\n");
    }
    for (int i = 0; i < DOUBLE_FIELDS.length; i++) {
      source.append("static final double d").append(i).append(" = ")
        .append(Double.toHexString(Double.longBitsToDouble(DOUBLE_FIELDS[i]))).append(";\n");
    }
    Path javaFile = Files.writeString(scratch.resolve("DecimalConstants.java"), source.append('}'));
    if (ToolProvider.getSystemJavaCompiler().run(null, null, null, "--release", "17",
        "-d", classes.toString(), javaFile.toString()) != 0) {
      throw new AssertionError("javac failed");
    }

    var engine = new Fernflower(null, Map.of("keep-literals", "1", "include-runtime", "0"),
      IFernflowerLogger.NO_OP);
    engine.addSource(classes.toFile());
    var subject = DecompilerContext.getStructContext().getClass("DecimalConstants");
    try (var output = new BufferedWriter(new OutputStreamWriter(System.out))) {
      for (var field : subject.getFields()) {
        var constant = field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
        var value = subject.getPool().getPrimitiveConstant(constant.getIndex()).value;
        write(output, "class", field.getName(), new VarType(field.getDescriptor()), value);
      }

      // Probe both ends and the interior of each binary exponent range.
      for (int exponent = 0; exponent < 255; exponent++) {
        for (int mantissa : new int[]{0, 1, 0x003fffff, 0x00400000, 0x007fffff}) {
          int bits = (exponent << 23) | mantissa;
          writeFloat(output, bits);
          writeFloat(output, bits | Integer.MIN_VALUE);
        }
      }
      for (long exponent = 0; exponent < 2047; exponent++) {
        for (long mantissa : new long[]{0, 1, 0x0007ffffffffffffL, 0x0008000000000000L,
            0x000fffffffffffffL}) {
          long bits = (exponent << 52) | mantissa;
          writeDouble(output, bits);
          writeDouble(output, bits | Long.MIN_VALUE);
        }
      }

      // Decimal powers and their neighbors stress changes of notation and
      // rounding at values that a shortest-round-trip formatter may choose differently.
      for (int exponent = -45; exponent <= 38; exponent++) {
        int bits = Float.floatToRawIntBits(Float.parseFloat("1e" + exponent));
        for (int offset = -2; offset <= 2; offset++) {
          writeFloat(output, bits + offset);
        }
      }
      for (int exponent = -324; exponent <= 308; exponent++) {
        long bits = Double.doubleToRawLongBits(Double.parseDouble("1e" + exponent));
        for (long offset = -2; offset <= 2; offset++) {
          writeDouble(output, bits + offset);
        }
      }

      var random = new SplittableRandom(0x6325c8b4479a3d11L);
      for (int i = 0; i < 4096; i++) {
        writeFloat(output, random.nextInt());
        writeDouble(output, random.nextLong());
      }
    }
  }

  private static void writeFloat(BufferedWriter output, int bits) throws Exception {
    float value = Float.intBitsToFloat(bits);
    if (Float.isFinite(value)) {
      write(output, "float", Integer.toHexString(bits), VarType.VARTYPE_FLOAT, value);
    }
  }

  private static void writeDouble(BufferedWriter output, long bits) throws Exception {
    double value = Double.longBitsToDouble(bits);
    if (Double.isFinite(value)) {
      write(output, "double", Long.toHexString(bits), VarType.VARTYPE_DOUBLE, value);
    }
  }

  private static void write(BufferedWriter output, String kind, String key, VarType type, Object value)
      throws Exception {
    var literal = new ConstExprent(type, value, null).toJava(0).convertToStringAndAllowDataDiscard();
    output.write(kind + "\t" + key + "\t" + literal + "\n");
  }
}
