import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import org.jetbrains.java.decompiler.main.plugins.PluginSources;
import org.jetbrains.java.decompiler.main.plugins.ServicePluginSource;

/** Use the distribution's plugin registrations when an oracle also links their classes directly. */
class BundledPluginReference {
  public static void main(String[] args) throws Throwable {
    PluginSources.PLUGIN_SOURCES.removeIf(ServicePluginSource.class::isInstance);
    try {
      Class.forName(args[0]).getMethod("main", String[].class)
        .invoke(null, (Object) Arrays.copyOfRange(args, 1, args.length));
    } catch (InvocationTargetException e) {
      throw e.getCause();
    }
  }
}
