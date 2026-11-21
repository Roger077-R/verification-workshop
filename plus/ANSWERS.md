# Homework plus: answers

Name(s):

### 1. Invariants from an LLM

| method | LLM | rounds | mistakes | final invariants by |
| --- | --- | --- | --- | --- |
| count | Codex (GPT-6) | 1 | None reported | Codex, verified by OpenJML |
| reverse | Codex (GPT-6) | 1 | None reported | Codex, verified by OpenJML |
| isqrt | Codex (GPT-6) | 1 | None reported | Codex, verified by OpenJML |
| dutchFlag | Codex (GPT-6) | 1 | None reported | Codex, verified by OpenJML |

OpenJML 21.0.29 with Z3 5.1.0 verified all four methods with `./esc plus/LlmLoops.java --progress`.


Q: Why is it safe to use invariants written by an LLM here, even if the LLM is often wrong?

A: OpenJML checks that each invariant holds on entry and is preserved by every iteration. At exit, it uses the invariant and the false guard to prove the method's postcondition. It also checks that the `decreases` expression is nonnegative when the loop body runs and strictly decreases with each iteration. The LLM supplies candidate annotations, and OpenJML decides whether they establish the specified properties.

#### Preconditions and loop annotations

The `requires` clauses below go before their methods. Each loop's annotations go immediately before its `for` or `while` statement.

**`count`**

```java
//@ requires a != null;
```

```java
//@ loop_invariant 0 <= i && i <= a.length;
//@ loop_invariant 0 <= c && c <= i;
//@ loop_invariant c == (\num_of int k; 0 <= k && k < i; a[k] == x);
//@ decreases a.length - i;
```

After processing `a[0..i)`, `c` counts exactly the entries equal to `x`. Since `c <= i` and the guard gives `i < a.length`, incrementing `c` cannot overflow.

**`reverse`**

```java
//@ requires a != null;
```

```java
//@ loop_invariant 0 <= i && i <= a.length;
//@ loop_invariant -1 <= j && j < a.length;
//@ loop_invariant j == a.length - 1 - i && i <= j + 1;
//@ loop_invariant (\forall int k; 0 <= k && k < a.length && (k < i || j < k);
//@     a[k] == \old(a[a.length - 1 - k]));
//@ loop_invariant (\forall int k; i <= k && k <= j; a[k] == \old(a[k]));
//@ decreases j - i + 1;
```

The endpoints `i` and `j` are mirror indices. Positions outside `[i,j]` have their final values, and positions inside still have their entry values. If the loop leaves a single middle element, its mirror index is itself.

**`isqrt`**

```java
//@ requires 0 <= n && n <= 1000000;
```

```java
//@ loop_invariant 0 <= r && r <= 1000;
//@ loop_invariant r * r <= n;
//@ decreases 1000 - r;
```

The upper bound on `r` keeps `(r + 1) * (r + 1)` within the Java `int` range. The invariant gives the lower bound on `n`, and the false guard at exit gives the upper bound.

**`dutchFlag`**

```java
//@ requires a != null;
//@ requires (\forall int k; 0 <= k && k < a.length; 0 <= a[k] && a[k] <= 2);
```

```java
//@ loop_invariant 0 <= lo && lo <= mid && mid <= hi && hi <= a.length;
//@ loop_invariant (\forall int k; 0 <= k && k < lo; a[k] == 0);
//@ loop_invariant (\forall int k; lo <= k && k < mid; a[k] == 1);
//@ loop_invariant (\forall int k; mid <= k && k < hi; 0 <= a[k] && a[k] <= 2);
//@ loop_invariant (\forall int k; hi <= k && k < a.length; a[k] == 2);
//@ decreases hi - mid;
```

The loop maintains a prefix of zeros, then ones, then an unprocessed region, then a suffix of twos. When `mid == hi`, the unprocessed region is empty, so the array is sorted.

### 2. The Zune bug

Q: `--unwind 31 --no-unwinding-assertions` says SUCCESSFUL. Does that mean `yearOf` is correct for every day it checked?

A: No, it only unrolls the first 31 loops, and will miss the potential infinite loops if there is one.
It will also miss the bugs for more than 31 loops, but it is not the case here since the method is only for the first 30 years. 


Q: What does JBMC report without `--no-unwinding-assertions`? Is K too small, or is something else wrong?

A: It reports an infinite loop with `days` be 1827. `K` is not too small here.


Q: What is wrong with the loop? Which date froze the Zune?

A: The loop misses the case where there the days decreases as year increases until exactly 366 days remains and the year is a leap year at the same time.
The date froze Zune is 1827 days since the year 1980, which is 1 Jan, 1985.


Q: With your fix, what is the smallest K that gives VERIFICATION SUCCESSFUL with unwinding assertions? What exactly has been proved?

A: The smallest K is 22 with the fix.
It proves that `yearOf` method places days within 365*30 days back to the first 30 years without proving the exact year of the day.


Q: A colleague changes `days > 366` to `days >= 366`. Which harness notices, and why?

A: OpenJML notices since it breaks the loop invariant.


Q (★): Why does `./esc` say OK on the original? What changes with `decreases`?

A: It says OK on the original since it satisfies the specifications. `decreases` requires `days` to decrease or `years` to increase,
which is not true if it is leap year but misses inner `days` check.


### 3. Range

Q: Why does `size()` not verify? Give concrete values.

A: It does not verify since there is a potential overflow issue. For example, `hi` be maximum of int value and `lo` be 0 since
incrementing `hi` would overflow.


Q: Compare JBMC's counterexample with your answer above.

A: JBMC gives the counterexample of `hi` be 1491599252 and `lo` be -1496580019, whose sum in absolute value exceeds the maximum
value of integer. They both result in an arithmetic overflow.

Fixed the issue by using represent the size in `long`. 


### 4. StackAr

Q: Which tool reports your bug, and how? Could a bug get past OpenJML but not JBMC, or the other way around?

### 5. SafeLock

Q: Smallest K that finds a bug? Which sequence of events? What is wrong in the code?

A: The smallest K that finds a bug is 5.
The sequence of events is entering pin -1078972882, entering pin -1078972882, close, entering pin -1615811026, and entering pin -1615843794.
When calling `close`, `failed` counter resets even when the lock does not open,
which enables us to close the door before exceeding maximum attempts for infinite attempts.

Q: Formula size and time for K = 8, 10, 12.

A: The table is the following

| K | Formula size | Time |
|:--|:-------------|:-----|
|8  |46050 variables, 68865 clauses|0.15s|
|10 |56941 variables, 87971 clauses|0.29s|
|12 |67836 variables, 107563 clauses|0.54s|


Q: Does SUCCESSFUL with K = 12 mean the property holds for every sequence? Can unwinding assertions help?

A: No, it only shows that the property holds for sequences of at most 12 events.
The unwinding assertions cannot help since it cannot prove unbounded sequences.

