// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import org.jetbrains.java.decompiler.code.MethodProperties;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.extern.IFernflowerPreferences;
import org.jetbrains.java.decompiler.modules.code.MethodPropertiesProcessor;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

class MethodPropertiesReference {
  public static void main(String[] args) throws Exception {
    new Fernflower(null, Map.of(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME, "0"), IFernflowerLogger.NO_OP);
    for (String path : Files.readAllLines(Path.of(args[0]))) {
      var cl = StructClass.create(new DataInputFullStream(Files.readAllBytes(Path.of(path))), true);
      for (var method : cl.getMethods()) {
        var properties = new MethodProperties(method);
        MethodPropertiesProcessor.parse(method, cl, properties);
        String field = properties.assertField == null ? "-" : properties.assertField.getName();
        System.out.println(cl.qualifiedName + "\t" + method.getName() + " " + method.getDescriptor()
          + "\t" + properties.isSyntheticReferenceLambda + "\t" + field);
        method.releaseResources();
      }
    }
  }
}
