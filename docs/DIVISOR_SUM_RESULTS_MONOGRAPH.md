# Divisor sums, perfect powers, and complete quartic classifications

PerfectPower can now answer a familiar arithmetic question: when does adding all the positive divisors of a number produce a perfect power? The new collection connects that question to the repository's effective quartic machinery, adds an exact census through one million, and classifies square divisor sums throughout an explicit two-prime-power grid. These are different kinds of results, with different domains of completeness. Every packet records that domain.

The photograph that motivated this work displays the classical multiplicative formula for the sum of divisors. If n is the product of distinct primes p raised to exponents a, then sigma(n) is the product of the geometric sums 1+p+...+p^a. Each divisor independently chooses one exponent for each prime. Expanding the product therefore enumerates each divisor once. The formula requires a genuine prime factorization; treating a composite base as a prime would give the wrong divisor sum.

The strongest immediately available application is sigma(p^4)=1+p+p^2+p^3+p^4. The repository already proves that this polynomial is a square at exactly the positive integer input 3. Thus the only prime fourth power with square divisor sum is 81, whose divisor sum is 121. The new Lean bridge connects the geometric polynomial to ArithmeticFunction.sigma, rather than leaving that identity implicit in prose.

## What was built

The quartic catalogue contains 3,080 distinct equations and 5,401 integer points counted across those equations. Exactly 1,361 equations have no integer points. The catalogue contains every x^4+c*x+d with c between -25 and 25 and d between -20 and 20, excluding the zero perturbation. It also contains the nondegenerate equations x^4+u*x^3+v*x^2+w*x+z with u,v,w,z between -2 and 2, and all 401 shifts of 1+x+x^2+x^3+x^4 with shift between -200 and 200. Overlapping equations are stored once, with their category memberships retained.

Seven coefficient tuples in the small quartic box have zero normalized remainder and are excluded from this finite solver catalogue. They are not declared insoluble. A square polynomial can have infinitely many square values, so forcing it into a finite-list schema would be a mathematical error. The exclusion list is explicit in complete_quartics.json.

Every listed quartic is solved over all integer x and all integer y. The Python lists use a global coordinate bound already proved by the generic Lean solver. This is stronger than checking a convenient numerical window. Python execution is still distinct from a kernel proof of each particular list. CompleteQuartics.lean contains a proof-producing native command for every catalogue row; validation metadata records which emitted instances have actually been compiled.

The bounded divisor-sum census covers every integer n from 1 through 1,000,000, for target degrees 2 through 8. It finds 6,871 square divisor sums, 957 cubes, 273 fourth powers, 128 fifth powers, 44 sixth powers, 52 seventh powers, and 33 eighth powers. A number can belong to several degrees, and n=1 is included in each degree. These counts are not disjoint classes, and no assertion is made about numbers beyond one million.

The prime-power grid contains 1,344 rows: every prime at most 1,000, with exponent from 1 through 8. The two-prime catalogue contains all 218 products p^a*q^b from that grid with p<q whose divisor sums are squares. Exactly 216 have individual divisor-sum factors that are not squares. The remaining two have both factors square. The result is complete in this finite grid, not a global classification of every two-prime integer.

The 401 shifted divisor-sum classifications are also stored separately in prime_shift_classifications.json. Exactly 50 shifts admit prime inputs, producing 100 signed prime points. These lists are globally complete for each listed shift because the input interval comes from the quartic theorem; their finite primality filtering is exact Python execution.

The standalone results.html browser supports coefficient and category searches, empty-curve filtering, and full matching-row exports. It preserves large integers as decimal strings and needs no external scripts or network access.

## The interaction that matters

A tempting shortcut would be to require each factor sigma(p^a) to be a square. That discards almost the entire two-prime result set. For example, sigma(2)=3 and sigma(11)=12. Neither is a square, but sigma(22)=3*12=36. A useful solver must recognize matching square classes, not just individual squares.

For positive integers A and B, let g=gcd(A,B). Then A*B is a square exactly when A/g and B/g are both squares. The quotients are coprime. If their product is a square, every prime exponent in each quotient is even, since the quotients share no prime factors. Conversely, if A=g*u^2 and B=g*v^2, then A*B=(g*u*v)^2.

This gives an exact join procedure without factoring the often large geometric sums. Each successful join records g, u, v, and the product root g*u*v. The final square identity can be replayed with integer multiplication alone. The Lean common_factor_square theorem proves the sufficient identity generically. The current partition and enumeration are Python computations; the generic sufficient identity is not a Lean proof of the complete grid enumeration.

The supplied divisor sums are partitioned into equivalence classes modulo rational squares. Two values belong to the same class exactly when their product is a square. The class label is a supplied representative, not a purported canonical squarefree kernel. This matters because the algorithm deliberately avoids prime factorization of those values. The grid yields 1,275 classes.

Distinct prime bases are essential. Multiplicativity applies to coprime integers. A product p^a*p^b must instead be treated as the single prime power p^(a+b); multiplying the two separate geometric sums gives the wrong answer. The join code excludes equal bases and records each distinct-prime pair in one canonical order.

## Why the quartic lists are complete

The direct family is y^2=(L*x^2+a*x+b)^2+c*x+d, with L nonzero and (c,d) not both zero. Its proven bound is |x| <= |a|+|b|+|c|+|d|+1. When the perturbation is nonzero, factoring the difference of squares forces the quadratic expression to be controlled by the smaller linear perturbation. This contradicts sufficiently large |x|. When the perturbation vanishes, the root of c*x+d is retained, including zero y and both signs where applicable.

A general square-leading quartic is normalized by scaling y and completing the quadratic square. For x^4+u*x^3+v*x^2+w*x+z, the scaling factor is 8. The completed quadratic has coefficients 8, 4u, and 4v-u^2, with a linear remainder determined exactly by the original coefficients. The generic solver proves a bound for x in this normalized equation.

Enumeration then returns to the original polynomial. It does not divide every scaled integer point by 8 and pretend that the result is integral. Only exact square roots of the original integer polynomial are admitted. This preserves the integrality condition through the change of variables.

For the shifted divisor-sum polynomial, the normalized coefficients are 8,4,3,40,55+64k. Its linear remainder coefficient is always 40, so no shift makes the normalized remainder identically zero. The current bound is 48+|55+64k|. For k=0 the bound is 103; the complete integer points are (-1,-1), (-1,1), (0,-1), (0,1), (3,-11), and (3,11). Restricting to positive prime inputs leaves only 3.

The bound is sufficient rather than optimized. Work limits reject oversized complete intervals instead of returning a truncated list labeled complete. In the supplied shift range all intervals fit the existing native solver budget. Larger requests may need a sharper bound or a different method.

## Exact census machinery

The sigma census uses a linear sieve. It stores each integer's least prime factor, the maximal power of that factor dividing the integer, and the geometric sum for that power. Extending by the same least prime updates the geometric sum; extending by a new coprime prime multiplies sigma by p+1. Each composite is reached through its least-prime construction once.

No floating-point root test is used. Squares use integer square roots. Higher degrees use integer binary search, with an upper bound derived from bit length. Every recorded root is checked by exact exponentiation. This avoids errors near large powers and permits the same arithmetic routines to handle integers far beyond machine-word size.

The census stores all hit triples (n,sigma(n),root), not just aggregate counts. The two-prime grid stores every prime-power row and its square-class assignment. The quartic catalogue stores ascending polynomial coefficients, the complete signed point list, the bound, the normalization data where needed, and the generic theorem reference. summary.json records hashes and sizes of the core result files.

## Reproducing and using the collection

From the repository root, run `PYTHONPATH=python python python/build_divisor_sum_atlas.py`. This rebuilds the complete default collection using the Python standard library. The limit, prime limit, maximum exponent, and output directory are explicit command-line options. Increasing the bounded census does not automatically strengthen any global claim.

Run `PYTHONPATH=python python -m perfectpower divisor-sum --factors '[[2,1],[11,1]]'` to compute sigma(22) from a validated prime factorization and report exact roots for degrees 2 through 8. Composite bases, duplicate primes, nonpositive exponents, and prime-validation requests beyond the trial budget are rejected. An empty factorization denotes n=1.

Run `PYTHONPATH=python python -m perfectpower sigma-quartic --shift 0` to obtain the complete integer points, positive inputs, and prime inputs for sigma(p^4). Change the shift to classify sigma(p^4)+k. The command computes from the generic solver rather than guessing from the one-million census.

Run `PYTHONPATH=python python -m perfectpower sigma-quartic --shift 7 --emit-lean --name shifted_sigma` to emit a standalone native proof-producing command. Its theorem describes the geometric quartic; PerfectPower.DivisorSum.shifted_prime_fourth_complete connects that equation to the actual divisor sum under the prime hypothesis.

The generated catalogue is intentionally kept under receipts rather than automatically imported into every repository build. Thousands of exact-list proofs can be expensive to elaborate, and an ordinary user should not pay that cost just to use the generic theorems. The check script compiles the catalogue explicitly and reports its actual status.

## Validation and scope

Independent tests compare sigma through 1,500 against direct enumeration of every divisor. A separate exhaustive grid compares the square-class join against all pairs and direct multiplication-square tests. Every catalogue point is replayed against its original polynomial. Root tests cover exact powers, neighboring nonpowers, and thousand-digit inputs. These tests exercise different mathematical routes, rather than simply repeating the generator's implementation.

The Python suite and Lean logs are retained with the collection. The new bridge uses Mathlib's existing divisor-sum theorems and the repository's previously completed quartic theorem. It does not claim a new classical divisor-sum formula, a global solution of sigma(n)=y^d, or a generic solution of all quartics.

There are productive next steps. Square classes can support three-prime and larger joins, preferably with explicit state and output budgets. Other prime-power exponents lead to quadratic, cubic, higher-degree Runge, or Pell-type families already represented elsewhere in the repository. Complete global answers still require the appropriate family theorem; extending a scan is not a substitute for one.

The practical mathematical value of this collection is that a simple divisor-sum question now has a concrete path into effective equations, exact interaction rules, complete special-family solutions, and reproducible finite data. It is a results repository that can be queried and extended, rather than a folder of unexplained numerical coincidences.

## Completed release checks

This push compiled six divisor-sum bridge theorems and 2,686 complete literal quartic lists, with 2,686 kernel proofs equating those lists to the saved packet points. All 5,378 axiom reports contain only the standard logical axioms. The checked catalogue indices are recorded explicitly, including all shifts from -3 through 3. The remaining 394 emitted instances are not claimed to have been compiled in this push.

The full Python suite passes 464 tests with four existing skips; all nine focused divisor-sum tests pass. A cold rebuild reproduces every core mathematical JSON file, the full Lean catalogue, and all static proof chunks byte for byte. The offline browser embeds all 3,080 curves and all 218 joins, preserves exact integers as decimal strings, and passes JavaScript syntax checking.

Resume literal-list checking with `python scripts/check_divisor_sum_catalogue.py --start-case 2000 --stop-case 2050 --batch-size 10` in a Lean-enabled checkout. Successful batches checkpoint their exact case indices against the full catalogue source hash. The default interval checks all cases; a normal import of PerfectPower uses the generic theorems and divisor-sum bridges without compiling the entire atlas.
