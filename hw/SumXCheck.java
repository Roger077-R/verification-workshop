import org.cprover.CProver;

// 6. A harness for SumX.sum with the contract of exercise 2.
//   ./bmc SumXCheck.check --unwind 10 --no-unwinding-assertions
public class SumXCheck {

    public static void check(int x) {
        
        CProver.assume(0 <= x && x <= 1000);
        int result = SumX.sum(x);
        assert(result == x * (x + 1) / 2);

    }
}
