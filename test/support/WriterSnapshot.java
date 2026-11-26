// SPDX-License-Identifier: Apache-2.0

import java.nio.charset.StandardCharsets;
import java.util.HexFormat;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.token.ClassTextToken;
import org.jetbrains.java.decompiler.util.token.FieldTextToken;
import org.jetbrains.java.decompiler.util.token.MethodTextToken;
import org.jetbrains.java.decompiler.util.token.VariableTextToken;

class WriterSnapshot {
  static void print(int width, String kind, String name, TextBuffer buffer) {
    System.out.println("section=" + width + "|" + kind + "|" + name);
    printPhase("raw", buffer);
    buffer.reformat();
    printPhase("wrapped", buffer);
  }

  private static void printPhase(String phase, TextBuffer buffer) {
    String text = buffer.convertToStringAndAllowDataDiscard();
    System.out.println(phase + "=" + HexFormat.of().formatHex(text.getBytes(StandardCharsets.UTF_8)));
    for (var token : buffer.getTokens()) {
      String range = token.getStart() + "|" + token.getLength() + "|" + token.isDeclaration() + "|";
      String data;
      if (token instanceof ClassTextToken cls) {
        data = "class|" + cls.qualifiedName;
      } else if (token instanceof FieldTextToken field) {
        data = "field|" + field.className + "|" + field.name + "|" + field.descriptor.descriptorString;
      } else if (token instanceof MethodTextToken method) {
        data = "method|" + method.className + "|" + method.name + "|" + method.descriptor;
      } else if (token instanceof VariableTextToken var) {
        data = "variable|" + var.parameter + "|" + var.className + "|" + var.methodName + "|" +
          var.methodDescriptor + "|" + var.index + "|" + var.name;
      } else {
        throw new AssertionError(token.getClass());
      }
      System.out.println(range + data);
    }
  }
}
