import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.StringJoiner;

public class HashMapReference {
    public static void main(String[] args) throws Exception {
        var input = new BufferedReader(new InputStreamReader(System.in));
        var coverage = new Coverage();
        HashMap<Object, Integer> map = new HashMap<>();
        String kind = "";
        String line;
        while ((line = input.readLine()) != null) {
            String[] command = line.split(" ");
            String step = command[0];
            String op = command[1];
            String result = "-";
            if (op.equals("new")) {
                kind = command[2];
                int capacity = Integer.parseInt(command[3]);
                map = capacity < 0 ? new HashMap<>() : new HashMap<>(capacity);
                coverage.before = new int[0];
            } else {
                switch (op) {
                    case "put":
                        result = nullable(map.put(key(kind, command[2]), Integer.valueOf(command[3])));
                        break;
                    case "compute":
                        result = map.computeIfAbsent(
                            key(kind, command[2]), k -> Integer.valueOf(command[3])).toString();
                        break;
                    case "replace":
                        result = nullable(map.replace(key(kind, command[2]), Integer.valueOf(command[3])));
                        break;
                    case "remove":
                        result = nullable(map.remove(key(kind, command[2])));
                        break;
                    case "retain":
                        var visited = new StringJoiner(",");
                        int divisor = Integer.parseInt(command[2]);
                        int residue = Integer.parseInt(command[3]);
                        for (var it = map.entrySet().iterator(); it.hasNext();) {
                            var entry = it.next();
                            visited.add(encode(entry.getKey()));
                            if (Math.floorMod(entry.getValue(), divisor) == residue) it.remove();
                        }
                        result = visited.toString();
                        break;
                    case "clear":
                        map.clear();
                        break;
                    case "copy":
                        map = new HashMap<>(map);
                        coverage.before = new int[0];
                        break;
                    case "clone":
                        @SuppressWarnings("unchecked")
                        var cloned = (HashMap<Object, Integer>) map.clone();
                        map = cloned;
                        coverage.before = new int[0];
                        break;
                    case "putAll":
                        var incoming = new LinkedHashMap<Object, Integer>();
                        for (int i = 2; i < command.length; i += 2)
                            incoming.put(key(kind, command[i]), Integer.valueOf(command[i + 1]));
                        map.putAll(incoming);
                        break;
                    default:
                        throw new IllegalArgumentException(op);
                }
            }
            var entries = new StringJoiner(",");
            for (var entry : map.entrySet())
                entries.add(encode(entry.getKey()) + "=" + entry.getValue());
            System.out.println(step + "\t" + result + "\t" + entries);
            coverage.observe(op, map);
        }
        coverage.check();
    }

    private static String nullable(Integer value) {
        return value == null ? "-" : value.toString();
    }

    private static Object key(String kind, String encoded) {
        if (encoded.equals("~")) return null;
        return switch (kind) {
            case "int" -> Integer.valueOf(encoded);
            case "long" -> Long.valueOf(encoded);
            case "text" -> {
                var text = new StringBuilder();
                for (int i = 0; i < encoded.length(); i += 4) {
                    text.append((char)Integer.parseInt(encoded.substring(i, i + 4), 16));
                }
                yield text.toString();
            }
            default -> throw new IllegalArgumentException(kind);
        };
    }

    private static String encode(Object key) {
        if (key == null) return "~";
        if (!(key instanceof String text)) return key.toString();
        var encoded = new StringBuilder();
        for (int i = 0; i < text.length(); i++) {
            String unit = Integer.toHexString(text.charAt(i));
            encoded.append("0".repeat(4 - unit.length())).append(unit);
        }
        return encoded.toString();
    }

    /** Inspect the JDK table to ensure the traces take the intended paths. */
    private static final class Coverage {
        private final Class<?> node = Class.forName("java.util.HashMap$Node");
        private final Class<?> tree = Class.forName("java.util.HashMap$TreeNode");
        private final Field table = accessible(HashMap.class, "table");
        private final Field next = accessible(node, "next");
        private final Field parent = accessible(tree, "parent");
        private int[] before = new int[0];
        private int putTreeify;
        private int computeTreeify;
        private int splitKeepsBoth;
        private int splitKeepsOne;
        private int splitKeepsNeither;
        private int iteratorKeepsSmallTree;
        private int iteratorMovesOffRoot;
        private int removeUntreeify;

        private Coverage() throws Exception {}

        private static Field accessible(Class<?> cls, String name) throws Exception {
            Field field = cls.getDeclaredField(name);
            field.setAccessible(true);
            return field;
        }

        private void observe(String op, Map<?, ?> map) throws Exception {
            Object[] buckets = (Object[])table.get(map);
            if (buckets == null) return;
            int[] counts = new int[buckets.length];
            for (int i = 0; i < buckets.length; i++) {
                Object head = buckets[i];
                boolean isTree = tree.isInstance(head);
                for (Object n = head; n != null; n = next.get(n)) counts[i] += isTree ? 1 : -1;
                if (op.equals("retain") && isTree) {
                    if (parent.get(head) != null) iteratorMovesOffRoot++;
                    if (counts[i] <= 6) iteratorKeepsSmallTree++;
                }
                if (before.length == counts.length) {
                    if (before[i] < 0 && counts[i] > 0) {
                        if (op.equals("put")) putTreeify++;
                        if (op.equals("compute")) computeTreeify++;
                    } else if (before[i] > 0 && counts[i] < 0 && op.equals("remove")) {
                        removeUntreeify++;
                    }
                }
            }
            if (before.length > 0 && before.length * 2 == counts.length) {
                for (int i = 0; i < before.length; i++) {
                    if (before[i] <= 0) continue;
                    int lo = counts[i], hi = counts[i + before.length];
                    if (lo > 0 && hi > 0) splitKeepsBoth++;
                    if ((lo > 0 && hi < 0) || (lo < 0 && hi > 0)) splitKeepsOne++;
                    if (lo < 0 && hi < 0) splitKeepsNeither++;
                }
            }
            before = counts;
        }

        private void check() {
            int[] counts = {putTreeify, computeTreeify, splitKeepsBoth, splitKeepsOne,
                splitKeepsNeither, iteratorKeepsSmallTree, iteratorMovesOffRoot, removeUntreeify};
            for (int count : counts) {
                if (count == 0) throw new AssertionError("Uncovered tree-bin path: " + java.util.Arrays.toString(counts));
            }
            System.err.println("Tree-bin transitions: " + java.util.Arrays.toString(counts));
        }
    }
}
