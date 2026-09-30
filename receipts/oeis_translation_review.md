# Translations of OEIS names into the definition language (generated; for review)

Written by `python/make_oeis_auto.py`. For each accepted entry: the `%N` text verbatim, the encoding the parser read from it (`docs/DEFINITION_LANGUAGE.md` gives the grammar and semantics), and the Lean definition emitted from the encoding. Lean proves statements about the Lean definition; whether the encoding is what the English means is for the reader to check here. Every encoding reproduces every listed term at the entry offset.

## A000032 (offset 0, 39 terms checked)

- **Source (%N):** Lucas numbers beginning at 2: L(n) = L(n-1) + L(n-2), L(0) = 2, L(1) = 1.
- **Encoding:** LinRec: a(n) = 1*a(n-1) + 1*a(n-2) + 0 for n >= 2; a(0) = 2, a(1) = 1
- **Relation proved:** exact, family `fib`
- **Lean definition:**

```lean
def A000032 : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | m + 2 => 1 * A000032 (m + 1) + 1 * A000032 (m + 0) + 0
```

## A000045 (offset 0, 41 terms checked)

- **Source (%N):** Fibonacci numbers: F(n) = F(n-1) + F(n-2) with F(0) = 0 and F(1) = 1.
- **Encoding:** LinRec: a(n) = 1*a(n-1) + 1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 1
- **Relation proved:** exact, family `fib`
- **Lean definition:**

```lean
def A000045 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 1 * A000045 (m + 1) + 1 * A000045 (m + 0) + 0
```

## A000129 (offset 0, 32 terms checked)

- **Source (%N):** Pell numbers: a(0) = 0, a(1) = 1; for n > 1, a(n) = 2*a(n-1) + a(n-2).
- **Encoding:** LinRec: a(n) = 2*a(n-1) + 1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 1
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A000129 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 2 * A000129 (m + 1) + 1 * A000129 (m + 0) + 0
```

## A000204 (offset 1, 39 terms checked)

- **Source (%N):** Lucas numbers (beginning with 1): L(n) = L(n-1) + L(n-2) with L(1) = 1, L(2) = 3.
- **Encoding:** LinRec: a(n) = 1*a(n-1) + 1*a(n-2) + 0 for n >= 3; a(1) = 1, a(2) = 3
- **Relation proved:** exact, family `fib`
- **Lean definition:**

```lean
def A000204 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | m + 2 => 1 * A000204 (m + 1) + 1 * A000204 (m + 0) + 0
```

## A001075 (offset 0, 27 terms checked)

- **Source (%N):** a(0) = 1, a(1) = 2, a(n) = 4*a(n-1) - a(n-2).
- **Encoding:** LinRec: a(n) = 4*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 1, a(1) = 2
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A001075 : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | m + 2 => 4 * A001075 (m + 1) + (-1) * A001075 (m + 0) + 0
```

## A001108 (offset 0, 24 terms checked)

- **Source (%N):** a(n)-th triangular number is a square: a(n+1) = 6*a(n) - a(n-1) + 2, with a(0) = 0, a(1) = 1.
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 2 for n >= 2; a(0) = 0, a(1) = 1
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A001108 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 6 * A001108 (m + 1) + (-1) * A001108 (m + 0) + 2
```

## A001109 (offset 0, 25 terms checked)

- **Source (%N):** a(n)^2 is a triangular number: a(n) = 6*a(n-1) - a(n-2) with a(0)=0, a(1)=1.
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 1
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A001109 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 6 * A001109 (m + 1) + (-1) * A001109 (m + 0) + 0
```

## A001254 (offset 0, 33 terms checked)

- **Source (%N):** Squares of Lucas numbers.
- **Encoding:** Coord: 1 * X_fib(1 m + 0) ^ 2
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A001254 (m : ℕ) : ℤ := (PerfectPower.FibOrbit.L (1 * m + 0)) ^ 2
```

## A001353 (offset 0, 28 terms checked)

- **Source (%N):** a(n) = 4*a(n-1) - a(n-2) with a(0) = 0, a(1) = 1.
- **Encoding:** LinRec: a(n) = 4*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 1
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A001353 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 4 * A001353 (m + 1) + (-1) * A001353 (m + 0) + 0
```

## A001519 (offset 0, 31 terms checked)

- **Source (%N):** a(n) = 3*a(n-1) - a(n-2) for n >= 2, with a(0) = a(1) = 1.
- **Encoding:** LinRec: a(n) = 3*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 1, a(1) = 1
- **Relation proved:** exact, family `fib`
- **Lean definition:**

```lean
def A001519 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | m + 2 => 3 * A001519 (m + 1) + (-1) * A001519 (m + 0) + 0
```

## A001541 (offset 0, 23 terms checked)

- **Source (%N):** a(0) = 1, a(1) = 3; for n > 1, a(n) = 6*a(n-1) - a(n-2).
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 1, a(1) = 3
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A001541 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | m + 2 => 6 * A001541 (m + 1) + (-1) * A001541 (m + 0) + 0
```

## A001542 (offset 0, 24 terms checked)

- **Source (%N):** a(n) = 6*a(n-1) - a(n-2) for n > 1, a(0)=0 and a(1)=2.
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 2
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A001542 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | m + 2 => 6 * A001542 (m + 1) + (-1) * A001542 (m + 0) + 0
```

## A001652 (offset 0, 24 terms checked)

- **Source (%N):** a(n) = 6*a(n-1) - a(n-2) + 2 with a(0) = 0, a(1) = 3.
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 2 for n >= 2; a(0) = 0, a(1) = 3
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A001652 : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | m + 2 => 6 * A001652 (m + 1) + (-1) * A001652 (m + 0) + 2
```

## A001653 (offset 1, 24 terms checked)

- **Source (%N):** Numbers k such that 2*k^2 - 1 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (-1) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A001653Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + (-1)}
def A001653 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(1, 1)] (n - 1 + 0)
```

## A001835 (offset 0, 28 terms checked)

- **Source (%N):** a(n) = 4*a(n-1) - a(n-2), with a(0) = 1, a(1) = 1.
- **Encoding:** LinRec: a(n) = 4*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 1, a(1) = 1
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A001835 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | m + 2 => 4 * A001835 (m + 1) + (-1) * A001835 (m + 0) + 0
```

## A001906 (offset 0, 31 terms checked)

- **Source (%N):** F(2n) = bisection of Fibonacci sequence: a(n) = 3*a(n-1) - a(n-2).
- **Encoding:** Coord: 1 * Y_fib(2 m + 0)
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A001906 (m : ℕ) : ℤ := PerfectPower.FibOrbit.F (2 * m + 0)
```

## A002315 (offset 0, 23 terms checked)

- **Source (%N):** NSW numbers: a(n) = 6*a(n-1) - a(n-2); also a(n)^2 - 2*b(n)^2 = -1 with b(n) = A001653(n+1).
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 1, a(1) = 7 (initial values read from the listed terms)
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A002315 : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | m + 2 => 6 * A002315 (m + 1) + (-1) * A002315 (m + 0) + 0
```

## A002878 (offset 0, 30 terms checked)

- **Source (%N):** Bisection of Lucas sequence: a(n) = L(2*n+1).
- **Encoding:** Coord: 1 * X_fib(2 m + 1)
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A002878 (m : ℕ) : ℤ := PerfectPower.FibOrbit.L (2 * m + 1)
```

## A005248 (offset 0, 30 terms checked)

- **Source (%N):** Bisection of Lucas numbers: a(n) = L(2*n) = A000032(2*n).
- **Encoding:** Coord: 1 * X_fib(2 m + 0)
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A005248 (m : ℕ) : ℤ := PerfectPower.FibOrbit.L (2 * m + 0)
```

## A005319 (offset 0, 22 terms checked)

- **Source (%N):** a(n) = 6*a(n-1) - a(n-2).
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 4 (initial values read from the listed terms)
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A005319 : ℕ → ℤ
  | 0 => 0
  | 1 => 4
  | m + 2 => 6 * A005319 (m + 1) + (-1) * A005319 (m + 0) + 0
```

## A007598 (offset 0, 31 terms checked)

- **Source (%N):** Squared Fibonacci numbers: a(n) = F(n)^2 where F = A000045.
- **Encoding:** Coord: 1 * Y_fib(1 m + 0) ^ 2
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A007598 (m : ℕ) : ℤ := (PerfectPower.FibOrbit.F (1 * m + 0)) ^ 2
```

## A011944 (offset 0, 17 terms checked)

- **Source (%N):** a(n) = 14*a(n-1) - a(n-2) with a(0) = 0, a(1) = 2.
- **Encoding:** LinRec: a(n) = 14*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 2
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A011944 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | m + 2 => 14 * A011944 (m + 1) + (-1) * A011944 (m + 0) + 0
```

## A025169 (offset 0, 27 terms checked)

- **Source (%N):** a(n) = 2*Fibonacci(2*n+2).
- **Encoding:** Coord: 2 * Y_fib(2 m + 2)
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A025169 (m : ℕ) : ℤ := 2 * PerfectPower.FibOrbit.F (2 * m + 2)
```

## A033888 (offset 0, 24 terms checked)

- **Source (%N):** a(n) = Fibonacci(4*n).
- **Encoding:** Coord: 1 * Y_fib(4 m + 0)
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A033888 (m : ℕ) : ℤ := PerfectPower.FibOrbit.F (4 * m + 0)
```

## A033890 (offset 0, 22 terms checked)

- **Source (%N):** a(n) = Fibonacci(4*n + 2).
- **Encoding:** Coord: 1 * Y_fib(4 m + 2)
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A033890 (m : ℕ) : ℤ := PerfectPower.FibOrbit.F (4 * m + 2)
```

## A048739 (offset 0, 29 terms checked)

- **Source (%N):** Expansion of 1/((1 - x)*(1 - 2*x - x^2)).
- **Encoding:** GF: P = [1], Q = [1, -3, 1, 1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A048739 : ℕ → ℤ := PerfectPower.OEISLib.gf3 [1] 3 (-1) (-1)
```

## A049684 (offset 0, 24 terms checked)

- **Source (%N):** a(n) = Fibonacci(2n)^2.
- **Encoding:** Coord: 1 * Y_fib(2 m + 0) ^ 2
- **Relation proved:** definition is the coordinate, family `fib`
- **Lean definition:**

```lean
def A049684 (m : ℕ) : ℤ := (PerfectPower.FibOrbit.F (2 * m + 0)) ^ 2
```

## A052454 (offset 1, 26 terms checked)

- **Source (%N):** Positive integer values of k such that 10*k^2 - 9 is a square.
- **Encoding:** SetSquare: {k >= 1 : 10 k^2 + (-9) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A052454Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + (-9)}
def A052454 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(1, 1), (9, 3), (41, 13)] (n - 1 + 0)
```

## A052530 (offset 0, 27 terms checked)

- **Source (%N):** a(n) = 4*a(n-1) - a(n-2), with a(0) = 0, a(1) = 2.
- **Encoding:** LinRec: a(n) = 4*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 2
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A052530 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | m + 2 => 4 * A052530 (m + 1) + (-1) * A052530 (m + 0) + 0
```

## A052542 (offset 0, 32 terms checked)

- **Source (%N):** a(n) = 2*a(n-1) + a(n-2), with a(0) = 1, a(1) = 2, a(2) = 4.
- **Encoding:** LinRec: a(n) = 2*a(n-1) + 1*a(n-2) + 0 for n >= 3; a(0) = 1, a(1) = 2, a(2) = 4
- **Relation proved:** exact from index 1, family `pell2`
- **Lean definition:**

```lean
def A052542 : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | m + 3 => 2 * A052542 (m + 2) + 1 * A052542 (m + 1) + 0
```

## A052995 (offset 0, 30 terms checked)

- **Source (%N):** Expansion of 2*x*(1 - x)/(1 - 3*x + x^2).
- **Encoding:** GF: P = [0, 2, -2], Q = [1, -3, 1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact from index 1, family `fib`
- **Lean definition:**

```lean
def A052995 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [0, 2, (-2)] 3 (-1)
```

## A067900 (offset 0, 20 terms checked)

- **Source (%N):** a(n) = 14*a(n-1) - a(n-2); a(0) = 0, a(1) = 8.
- **Encoding:** LinRec: a(n) = 14*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 8
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A067900 : ℕ → ℤ
  | 0 => 0
  | 1 => 8
  | m + 2 => 14 * A067900 (m + 1) + (-1) * A067900 (m + 0) + 0
```

## A074061 (offset 0, 26 terms checked)

- **Source (%N):** Positive integers k such that 24*k^2 - 23 is a square.
- **Encoding:** SetSquare: {k >= 1 : 24 k^2 + (-23) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A074061Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 24 * k ^ 2 + (-23)}
def A074061 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 24 5 1 [(1, 1), (19, 4)] (n - 0 + 0)
```

## A075796 (offset 1, 19 terms checked)

- **Source (%N):** Numbers k such that 5*k^2 + 5 is a square.
- **Encoding:** SetSquare: {k >= 0 : 5 k^2 + (5) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075796Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 5 * k ^ 2 + 5}
def A075796 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 5 9 4 [(5, 2)] (n - 1 + 0)
```

## A075835 (offset 1, 21 terms checked)

- **Source (%N):** Numbers k such that 13*k^2 + 4 is a square.
- **Encoding:** SetSquare: {k >= 0 : 13 k^2 + (4) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075835Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 13 * k ^ 2 + 4}
def A075835 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 13 649 180 [(2, 0), (11, 3), (119, 33)] (n - 1 + 0)
```

## A075836 (offset 1, 25 terms checked)

- **Source (%N):** Numbers k such that 10*k^2 + 9 is a square.
- **Encoding:** SetSquare: {k >= 0 : 10 k^2 + (9) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075836Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + 9}
def A075836 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(3, 0), (7, 2), (13, 4)] (n - 1 + 0)
```

## A075839 (offset 1, 18 terms checked)

- **Source (%N):** Numbers k such that 11*k^2 - 2 is a square.
- **Encoding:** SetSquare: {k >= 0 : 11 k^2 + (-2) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075839Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 11 * k ^ 2 + (-2)}
def A075839 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 11 10 3 [(3, 1)] (n - 1 + 0)
```

## A075841 (offset 1, 20 terms checked)

- **Source (%N):** Numbers k such that 2*k^2 - 9 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (-9) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075841Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + (-9)}
def A075841 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(3, 3)] (n - 1 + 0)
```

## A075843 (offset 0, 17 terms checked)

- **Source (%N):** Numbers k such that 99*k^2 + 1 is a square.
- **Encoding:** SetSquare: {k >= 0 : 99 k^2 + (1) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075843Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 99 * k ^ 2 + 1}
def A075843 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 99 10 1 [(1, 0)] (n - 0 + 0)
```

## A075844 (offset 0, 17 terms checked)

- **Source (%N):** Numbers k such that 11*k^2 + 4 is a square.
- **Encoding:** SetSquare: {k >= 0 : 11 k^2 + (4) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075844Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 11 * k ^ 2 + 4}
def A075844 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 11 10 3 [(2, 0)] (n - 0 + 0)
```

## A075848 (offset 0, 21 terms checked)

- **Source (%N):** Numbers k such that 2*k^2 + 9 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (9) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075848Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 9}
def A075848 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(3, 0)] (n - 0 + 0)
```

## A075869 (offset 1, 16 terms checked)

- **Source (%N):** Numbers k such that 5*k^2 - 9 is a square.
- **Encoding:** SetSquare: {k >= 0 : 5 k^2 + (-9) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075869Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 5 * k ^ 2 + (-9)}
def A075869 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 5 9 4 [(6, 3)] (n - 1 + 0)
```

## A075870 (offset 1, 23 terms checked)

- **Source (%N):** Numbers k such that 2*k^2 - 4 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (-4) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075870Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + (-4)}
def A075870 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(2, 2)] (n - 1 + 0)
```

## A075871 (offset 1, 12 terms checked)

- **Source (%N):** Numbers k such that 13*k^2 + 1 is a square.
- **Encoding:** SetSquare: {k >= 0 : 13 k^2 + (1) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A075871Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 13 * k ^ 2 + 1}
def A075871 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 13 649 180 [(1, 0)] (n - 1 + 0)
```

## A077446 (offset 1, 28 terms checked)

- **Source (%N):** Numbers k such that 2*k^2 + 14 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (14) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A077446Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 14}
def A077446 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(4, 1), (8, 5)] (n - 1 + 0)
```

## A078057 (offset 0, 32 terms checked)

- **Source (%N):** Expansion of (1+x)/(1-2*x-x^2).
- **Encoding:** GF: P = [1, 1], Q = [1, -2, -1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A078057 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, 1] 2 1
```

## A079291 (offset 0, 25 terms checked)

- **Source (%N):** Squares of Pell numbers.
- **Encoding:** Coord: 1 * Y_pell2(1 m + 0) ^ 2
- **Relation proved:** definition is the coordinate, family `pell2`
- **Lean definition:**

```lean
def A079291 (m : ℕ) : ℤ := (PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) ^ 2
```

## A079935 (offset 1, 27 terms checked)

- **Source (%N):** a(n) = 4*a(n-1) - a(n-2) with a(1) = 1, a(2) = 3.
- **Encoding:** LinRec: a(n) = 4*a(n-1) + -1*a(n-2) + 0 for n >= 3; a(1) = 1, a(2) = 3
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A079935 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | m + 2 => 4 * A079935 (m + 1) + (-1) * A079935 (m + 0) + 0
```

## A080806 (offset 1, 26 terms checked)

- **Source (%N):** Positive integer values of n such that 6*n^2-5 is a square.
- **Encoding:** SetSquare: {k >= 1 : 6 k^2 + (-5) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A080806Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 6 * k ^ 2 + (-5)}
def A080806 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 6 5 2 [(1, 1), (7, 3)] (n - 1 + 0)
```

## A082405 (offset 0, 18 terms checked)

- **Source (%N):** a(n) = 34*a(n-1) - a(n-2); a(0)=0, a(1)=6.
- **Encoding:** LinRec: a(n) = 34*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 0, a(1) = 6
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A082405 : ℕ → ℤ
  | 0 => 0
  | 1 => 6
  | m + 2 => 34 * A082405 (m + 1) + (-1) * A082405 (m + 0) + 0
```

## A082651 (offset 1, 25 terms checked)

- **Source (%N):** Positive integer values of n such that 5n^2+11 is a square.
- **Encoding:** SetSquare: {k >= 1 : 5 k^2 + (11) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A082651Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 5 * k ^ 2 + 11}
def A082651 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 5 9 4 [(4, 1), (16, 7)] (n - 1 + 0)
```

## A094347 (offset 0, 18 terms checked)

- **Source (%N):** a(n) = 14*a(n-1) - a(n-2); a(0) = a(1) = 2.
- **Encoding:** LinRec: a(n) = 14*a(n-1) + -1*a(n-2) + 0 for n >= 2; a(0) = 2, a(1) = 2
- **Relation proved:** exact, family `sqrt3`
- **Lean definition:**

```lean
def A094347 : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | m + 2 => 14 * A094347 (m + 1) + (-1) * A094347 (m + 0) + 0
```

## A106256 (offset 1, 24 terms checked)

- **Source (%N):** Numbers n such that 12*n^2 + 13 is a square.
- **Encoding:** SetSquare: {k >= 0 : 12 k^2 + (13) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A106256Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 12 * k ^ 2 + 13}
def A106256 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 12 7 2 [(5, 1), (11, 3)] (n - 1 + 0)
```

## A128588 (offset 1, 38 terms checked)

- **Source (%N):** Expansion of g.f. x*(1+x+x^2)/(1-x-x^2).
- **Encoding:** GF: P = [0, 1, 1, 1], Q = [1, -1, -1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact from index 2, family `fib`
- **Lean definition:**

```lean
def A128588 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [0, 1, 1, 1] 1 1
```

## A133283 (offset 1, 18 terms checked)

- **Source (%N):** Numbers k such that 30*k^2 + 6 is a square.
- **Encoding:** SetSquare: {k >= 0 : 30 k^2 + (6) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A133283Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 30 * k ^ 2 + 6}
def A133283 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 30 11 2 [(6, 1)] (n - 1 + 0)
```

## A133326 (offset 1, 30 terms checked)

- **Source (%N):** Numbers n such that 2*n^2 + 41 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (41) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A133326Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 41}
def A133326 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(7, 2), (13, 8)] (n - 1 + 0)
```

## A144797 (offset 1, 30 terms checked)

- **Source (%N):** Numbers k such that 2*k^2 + 17 is a square.
- **Encoding:** SetSquare: {k >= 0 : 2 k^2 + (17) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A144797Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 17}
def A144797 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(5, 2), (7, 4)] (n - 1 + 0)
```

## A176981 (offset 0, 31 terms checked)

- **Source (%N):** Expansion of 2+(1-2*x)/(-1+2*x+x^2).
- **Encoding:** GF: P = [1, -2, -2], Q = [1, -2, -1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact from index 1, family `pell2`
- **Lean definition:**

```lean
def A176981 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, (-2), (-2)] 2 1
```

## A182435 (offset 0, 24 terms checked)

- **Source (%N):** a(n) = 6*a(n-1) - a(n-2) - 2 with n>1, a(0)=0, a(1)=1.
- **Encoding:** LinRec: a(n) = 6*a(n-1) + -1*a(n-2) + -2 for n >= 2; a(0) = 0, a(1) = 1
- **Relation proved:** exact, family `pell2`
- **Lean definition:**

```lean
def A182435 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 6 * A182435 (m + 1) + (-1) * A182435 (m + 0) + (-2)
```

## A212804 (offset 0, 50 terms checked)

- **Source (%N):** Expansion of (1 - x)/(1 - x - x^2).
- **Encoding:** GF: P = [1, -1], Q = [1, -1, -1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact, family `fib`
- **Lean definition:**

```lean
def A212804 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, (-1)] 1 1
```

## A215928 (offset 0, 32 terms checked)

- **Source (%N):** a(n) = 2*a(n-1) + a(n-2) for n > 2, a(0) = a(1) = 1, a(2) = 2.
- **Encoding:** LinRec: a(n) = 2*a(n-1) + 1*a(n-2) + 0 for n >= 3; a(0) = 1, a(1) = 1, a(2) = 2
- **Relation proved:** exact from index 1, family `pell2`
- **Lean definition:**

```lean
def A215928 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | m + 3 => 2 * A215928 (m + 2) + 1 * A215928 (m + 1) + 0
```

## A239365 (offset 1, 16 terms checked)

- **Source (%N):** Numbers n such that 10*n^2+4 is a square.
- **Encoding:** SetSquare: {k >= 1 : 10 k^2 + (4) is a square}, increasing; k = 0 solves the equation but the listed terms start after it: positive k
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A239365Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + 4}
def A239365 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(2, 0)] (n - 1 + 1)
```

## A259131 (offset 1, 22 terms checked)

- **Source (%N):** Numbers n such that 13*n^2 + 52 is a square.
- **Encoding:** SetSquare: {k >= 0 : 13 k^2 + (52) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A259131Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 13 * k ^ 2 + 52}
def A259131 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 13 649 180 [(13, 3), (130, 36), (1417, 393)] (n - 1 + 0)
```

## A273052 (offset 1, 19 terms checked)

- **Source (%N):** Numbers n such that 7*n^2 + 8 is a square.
- **Encoding:** SetSquare: {k >= 0 : 7 k^2 + (8) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A273052Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 7 * k ^ 2 + 8}
def A273052 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 7 8 3 [(6, 2)] (n - 1 + 0)
```

## A273053 (offset 1, 22 terms checked)

- **Source (%N):** Numbers n such that 15*n^2 + 16 is a square.
- **Encoding:** SetSquare: {k >= 0 : 15 k^2 + (16) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A273053Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 15 * k ^ 2 + 16}
def A273053 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 15 4 1 [(4, 0)] (n - 1 + 0)
```

## A273054 (offset 1, 18 terms checked)

- **Source (%N):** Numbers n such that 19*n^2 + 20 is a square.
- **Encoding:** SetSquare: {k >= 0 : 19 k^2 + (20) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A273054Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 19 * k ^ 2 + 20}
def A273054 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 19 170 39 [(18, 4), (96, 22)] (n - 1 + 0)
```

## A288219 (offset 0, 38 terms checked)

- **Source (%N):** a(n) = a(n-1) + a(n-2) for n >= 3, where a(0) = 2, a(1) = 4, a(2) = 7.
- **Encoding:** LinRec: a(n) = 1*a(n-1) + 1*a(n-2) + 0 for n >= 3; a(0) = 2, a(1) = 4, a(2) = 7
- **Relation proved:** exact from index 1, family `fib`
- **Lean definition:**

```lean
def A288219 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | m + 3 => 1 * A288219 (m + 2) + 1 * A288219 (m + 1) + 0
```

## A309330 (offset 1, 15 terms checked)

- **Source (%N):** Numbers k such that 10*k^2 + 40 is a square.
- **Encoding:** SetSquare: {k >= 0 : 10 k^2 + (40) is a square}, increasing
- **Relation proved:** increasing enumeration of the set, family `engine`
- **Lean definition:**

```lean
def A309330Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + 40}
def A309330 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(20, 6)] (n - 1 + 0)
```

## A373566 (offset 0, 39 terms checked)

- **Source (%N):** Expansion of x - 1/(x - 1/(x + 1)).
- **Encoding:** GF: P = [1, 2, -1, -1], Q = [1, -1, -1] (coefficients in x, lowest terms, Q(0) = 1)
- **Relation proved:** exact from index 2, family `fib`
- **Lean definition:**

```lean
def A373566 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, 2, (-1), (-1)] 1 1
```

