# Homework: answers

Name(s): Range Feng, Hongchen Zhao

## OpenJML

### 1. Absolute

Q: What does OpenJML complain about before you write a contract, and for which input?

A: It conplains about the following for input `n`

```text
hw/Absolute.java:9: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method abs: int negation
            return -n;
                   ^
1 verification failure
```


Q: Which `requires` did you need, and why? Could you avoid it by changing the `ensures`?

A: We need `requires n > -2147483468 && n <= 2147483467` since two's complement encoding is not symmetric,
i.e. there is no 2147483468 since -(-2147483468) yields -2147483468 again. We canno tavoid changing `ensures`
clause since it is used for verifying the return value.

### 2. SumX

Q: Which proof obligations fail? Is the program wrong?

A: There are two main problems. One is `s = s + 1`, since we only have the range of i. Therefore, we can't promise that `s = s + i` won't cause an overflow. Another thing is that we want `s = x*(x+1)/2` but we don't have this relation. So we need to add `loop_invariant : s == i(i+1)/2` then it can deduce the result satisfies the postcondition. 

Q: Largest N for which `x <= N` verifies? What happens with N + 1, and why?

A : It will cause an INT overflow. The largest `N` should be `N = 65535`. If we have `N = 65536` then `65536*65536/2 = 2147450880` which is greater than `Integer.MAX_VALUE`. Therefore, when it operates ` s = s + i` it will fail. This is an `ArithmeticOperationRange`

### 3. Max

Q: Is the remaining failure caused by your invariants or by the code? (Your hypothesis.)

A: The remaining failure is caused by the code, not by a missing invariant. The loop condition skips the last array element. For example, with `[0, 1]`, the loop does not execute and the method returns 0, which is not greater than or equal to every array element.

### 4. BinarySearch

Q: What does OpenJML report, in which method, and for which concrete call? How large must the array be?

A: It reports the following in method `midpoint`

```text
hw/BinarySearch.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method midpoint: overflow in int sum
        return (lo + hi) / 2;
                   ^
hw/BinarySearch.java:8: verify: The prover cannot establish an assertion (Postcondition: hw/BinarySearch.java:6:) in method midpoint
        return (lo + hi) / 2;
        ^
hw/BinarySearch.java:6: verify: Associated declaration: hw/BinarySearch.java:8:
    //@ ensures lo <= \result && \result <= hi;
        ^
3 verification failures
NOT VERIFIED: see the messages above
```

which can be produced by setting `lo` and `hi` both be `INT_MAX`. The array must be at least 1,073,741,734 elements.

Q: What happens without `/*@ pure @*/` on `midpoint`, and why?

A: Removing it produces even more verification failures as follows

```text
hw/BinarySearch.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method midpoint: overflow in int sum
        return (lo + hi) / 2;
                   ^
hw/BinarySearch.java:8: verify: The prover cannot establish an assertion (Postcondition: hw/BinarySearch.java:6:) in method midpoint
        return (lo + hi) / 2;
        ^
hw/BinarySearch.java:6: verify: Associated declaration: hw/BinarySearch.java:8:
    //@ ensures lo <= \result && \result <= hi;
        ^
hw/BinarySearch.java:21: verify: The prover cannot establish an assertion (Assignable: hw/BinarySearch.java:20:) in method search: \everything
            int mid = midpoint(lo, hi);
                              ^
hw/BinarySearch.java:20: verify: Associated declaration: hw/BinarySearch.java:21:
        while (lo <= hi) {
        ^
hw/BinarySearch.java:18: verify: The prover cannot establish an assertion (LoopInvariant) in method search
        //@ loop_invariant (\forall int j; hi < j && j < a.length; a[j] > key);
            ^
hw/BinarySearch.java:17: verify: The prover cannot establish an assertion (LoopInvariant) in method search
        //@ loop_invariant (\forall int j; 0 <= j && j < lo; a[j] < key);
            ^
7 verification failures
```

The new failures are all inside `search` method since `midpoint` is no longer pure, which implies that `lo` and `hi` may be changed by `midpoint`,
breaking the loop invariants.

## JBMC

### 5. Max, again

Q: What input did JBMC find, and what goes wrong? Was your hypothesis of exercise 3 right?

A: Yes, the hypothesis of exercise 3 is correct.

Q: Smallest `--unwind` and `--max-nondet-array-length` that find it? Relation to the small scope hypothesis?

A: The minimal `--unwind` is `--unwind 2` and the minimal `--max-nondet-array-length` is `--max-nondet-array-length 2`. In this case you can find a counterexample for `assertion: assert r>= a[j]`. If you just want to find `unwinding assertion loop`, then `1,1` is enough. And this satisfies small scope hypothesis since we can find a bug in a small case.

Q: Why does `--unwind 5` with unwinding assertions fail on the fixed version? Smallest K with `--max-nondet-array-length 4`, and why not one less? What has been proved?

A: If we just use `./bmc MaxCheck --unwind 5` then it will have a `unwinding assertion loop`. The reason is if we only iterate for 5 times, when we have an array of length longer than 5, then this will fail. Since we restrict the length of the array to 4, it can iterates for 4 times and 1 time to check the exit condition. Therefore, under
`./bcm MaxCheck.check --unwind 5 --max-nondet-array-length 5` can prove that the size of the array is {1,2,3,4}, this algorithm is true

### 6. SumX

Q: Which values of `x` were checked with `--unwind 10 --no-unwinding-assertions`? Why does it fail with unwinding assertions? Which K is a proof? Sizes and times for K = 10, 100 and that K.

A: Without unwinding assertions, only `x = 0..10` is fully checked; longer executions are ignored. With unwinding assertions, K = 10 fails because the precondition allows `x` up to 1000. K = 1001 fully unwinds the loop and proves the postcondition for every allowed `x`. Formula sizes and times for K = 10, 100, and 1001 are run-dependent; record the variables, clauses, and time reported by JBMC.

Q: What did OpenJML need from you, and what did JBMC need?

A: OpenJML needed an inductive loop invariant relating `s` to `i` (and a decreases clause). JBMC needed a harness expressing the precondition and postcondition, plus a sufficient unwind bound; it did not need loop invariants.


### 7. BinarySearch

Q: Why does JBMC miss the bug with the `search` harness? Could a larger bound help?

A: JBMC misses it since we assumed that the length of the array is at most 5. Even if `hi` and `lo` both reach the highest value possible,
`hi + lo` will not exceed `INT_MAX`. Therefore, it misses the bug.
A larger bound could help, but with proper settings, such as larger loop unroll.


Q: What did the `midpoint` harness find?

It finds that with large enough input (e.g. `lo` be 630071278, `hi` be 1807605771) that causes addition overflow, midpoint would produce incorrect return value.
With fixed one, it passes the verification.


## Comparison

### 8. Comparison

| program | OpenJML: result, what you wrote | JBMC: result, bound used |
| --- | --- | --- |
| SumX | Verified for `0 <= x <= 1000` with loop invariants | Successful with `--unwind 1001` and the same input bound |
| Max | Verified after fixing the loop bound and adding invariants and a decreases clause | Successful with `--unwind 5 --max-nondet-array-length 4` |
| BinarySearch | Verified fixed computation for midpoint `lo + (hi - lo) / 2` | Successful with `--unwind 6 --max-nondet-array-length 5` for `search` and `--unwind 1` for `midpoint` specification |

Q: When would you use each tool?

