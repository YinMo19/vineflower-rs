public class Ledger<K, V> {
    class Entry {
        final K key;
        final V value;
        final Entry previous;

        Entry(K key, V value, Entry previous) {
            this.key = key;
            this.value = value;
            this.previous = previous;
        }

        Entry update(V value) {
            return new Entry(key, value, this);
        }
    }

    int count(Entry entry) {
        int count = 0;
        if (entry != null) {
            do {
                count++;
                entry = entry.previous;
            } while (entry != null);
        }
        return count;
    }

    int historyLength(K key, V value) {
        Entry first = new Entry(key, value, null);
        return count(first.update(value));
    }

    public static void main(String[] args) {
        Ledger<String, Integer> ledger = new Ledger<>();
        System.out.println(ledger.count(null));
        System.out.println(ledger.historyLength("key", 10));
    }
}
