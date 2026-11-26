// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Files;
import java.nio.file.Path;

import org.jetbrains.java.decompiler.main.decompiler.ConsoleDecompiler;

public final class KotlinLambdaReference {
  public static void main(String[] args) throws Exception {
    ConsoleDecompiler.main(Files.readAllLines(Path.of(args[0])).toArray(String[]::new));
  }
}
