// 1. Write the contract of abs and verify it.
//   ./esc hw/Absolute.java
public class Absolute {

    // Returns the absolute value of n.
    //@ requires n > -2147483648 && n <= 2147483647;
    //@ ensures \result >= 0 && (\result == n || \result == -n);
    public static int abs(int n) {
        if (n < 0) {
            return -n;
        }
        return n;
    }
}
