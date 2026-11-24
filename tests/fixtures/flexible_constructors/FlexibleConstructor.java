public class FlexibleConstructor {
    private static int trace;
    final int value;
    int audit;
    int afterSuper = step(9);

    public FlexibleConstructor(int input) {
        int prepared = step(input);
        if (prepared < 0) {
            throw new IllegalArgumentException("negative");
        }
        this.value = prepared;
        step(2);
        new String("constructed");
        super();
        this.audit = step(prepared);
    }

    public FlexibleConstructor() {
        int prepared = step(4);
        this.audit = step(5);
        this(prepared);
    }

    public FlexibleConstructor(boolean alternate) {
        this(step(6), this.audit = step(7), step(8));
    }

    private FlexibleConstructor(int first, int second, int third) {
        this(first + second + third);
    }

    private static int step(int value) {
        trace = trace * 10 + value;
        return value;
    }
}

enum FlexibleConstructorEnum {
    FIRST;

    final int value;

    FlexibleConstructorEnum() {
        int prepared = twice(3);
        this(prepared);
    }

    FlexibleConstructorEnum(int value) {
        this.value = value;
    }

    private static int twice(int value) {
        return value * 2;
    }
}

record FlexibleConstructorRecord(int value) {
    FlexibleConstructorRecord() {
        int prepared = Math.abs(-4);
        this(prepared);
    }
}
