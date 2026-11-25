// SPDX-License-Identifier: Apache-2.0

import java.nio.file.Path;
import java.util.Map;
import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.main.ClassesProcessor;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.main.Fernflower;
import org.jetbrains.java.decompiler.main.collectors.ImportCollector;
import org.jetbrains.java.decompiler.main.extern.IFernflowerLogger;
import org.jetbrains.java.decompiler.main.rels.LambdaProcessor;

class WrapperStages {
  static ClassesProcessor initialize(Path classes, String name, Map<String,Object> options) throws Exception {
    var processor = load(classes, options);
    initialize(processor, processor.getMapRootClasses().get(name));
    return processor;
  }

  static ClassesProcessor load(Path classes, Map<String,Object> options) {
    var engine = new Fernflower(null,options,IFernflowerLogger.NO_OP);
    engine.addSource(classes.toFile());
    var processor = DecompilerContext.getClassProcessor();
    processor.loadClasses(null);
    return processor;
  }

  static void initialize(ClassesProcessor processor, ClassNode root) throws Exception {
    DecompilerContext.startClass(new ImportCollector(root));
    new LambdaProcessor().processClass(root);
    var imports = ClassesProcessor.class.getDeclaredMethod("addClassNameToImport", ClassNode.class, ImportCollector.class);
    imports.setAccessible(true);
    imports.invoke(null, root, DecompilerContext.getImportCollector());
    var wrappers = ClassesProcessor.class.getDeclaredMethod("initWrappers", ClassNode.class, LanguageSpec.class);
    wrappers.setAccessible(true);
    wrappers.invoke(null, root,null);
  }
}
