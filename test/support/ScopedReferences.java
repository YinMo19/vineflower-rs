import java.util.function.Function;

public class ScopedReferences {
    static <T extends Number> T copy(T value) {
        class Copier {
            T apply(T input) {
                return input;
            }
        }
        return new Copier().apply(value);
    }

    static <T extends CharSequence> int length(T text) {
        Function<Integer, Integer> copyNumber = ScopedReferences::copy;
        return copyNumber.apply(text.length());
    }

    public static void main(String[] args) {
        System.out.print(length("scope"));
    }
}
