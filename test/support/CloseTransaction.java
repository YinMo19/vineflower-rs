public class CloseTransaction {
    private static void step(int stage, int failure) {
        System.out.print(stage);
        if (stage == failure) {
            throw new IllegalStateException();
        }
    }

    private static void close(boolean open, int failure) {
        if (open) {
            assert failure >= 0 : "invalid step";
            try {
                step(1, failure);
            } catch (IllegalStateException e) {
                step(2, failure);
            } finally {
                try {
                    step(3, failure);
                    step(4, failure);
                } finally {
                    step(5, failure);
                }
            }
        }
    }

    public static void main(String[] args) {
        for (int failure : new int[] {-1, 0, 1, 3, 4, 5}) {
            try {
                close(false, failure);
                close(true, failure);
            } catch (AssertionError e) {
                System.out.print("assert");
            } catch (IllegalStateException e) {
                System.out.print("!");
            }
            System.out.println();
        }
    }
}
