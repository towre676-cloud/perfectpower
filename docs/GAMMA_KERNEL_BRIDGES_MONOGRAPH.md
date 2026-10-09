# Universal Gamma arithmetic bridges

Version 0.6.2 replaces two Gamma proof gaps with reusable Lean results and checked calls on original factorial expressions. The residue-block factorial-unit algorithm is proved for every natural index and every prime-power modulus. The sufficient direction of Landau's criterion is proved for arbitrary finite slope lists. An exact rational-cell certificate now produces a theorem that a balanced factorial ratio is integral at every natural index.

The converse direction of Landau's criterion remains open in this library. Python and JSON interpretation are still outside formal program refinement. Proof status distinguishes emitted source from a kernel-accepted reconstructed query.

## The original factorial unit

For prime p and natural n, define
\[
U_p(n!)=\frac{n!}{p^{v_p(n!)}}.
\]
The target is its residue modulo \(M=p^k\), for positive k. Ordinary inversion of a factorial would be invalid when its p valuation is positive. This computation removes the entire prime-power factor first.

Write \(B_p(n)=\prod_{1\le j\le n,\ p\nmid j}j\). The exact recurrence is
\[
U_p(n!)=B_p(n)\,U_p(\lfloor n/p\rfloor!).
\]
FactorialUnit.stripped_step proves this equality in natural numbers. Its induction distinguishes whether p divides n+1. In the divisible case, the quotient index increases by one and removing p gives the complementary factor of the quotient. Otherwise the new factor already is prime-free and the quotient index stays fixed. The proof uses Mathlib's multiplicativity of complementary factors and factorial successor identity.

The residue factor is one when p divides i+1 and is i+1 modulo M otherwise. It is periodic with period M because p divides M. A separate general theorem, periodic_product, expresses a periodic product in any commutative monoid as the product of complete periods and a remainder prefix.

Combining this theorem with the exact stripped recurrence proves algorithm_correct for every n and every M divisible by p. The public prime_power_correct specialization identifies the algorithm with the cast of the actual complementary factor of n!, rather than another transcript-producing function.

The executable Lean algorithm uses structural recursion with sufficient fuel. It stops when the quotient reaches zero and never traverses unused fuel. Binary modular powering has its own general correctness theorem. Instance checking thus avoids constructing n! and avoids a linear exponentiation loop. Prefix products still cost work proportional to M, so the certificate budget charges M at every quotient level.

## Original factorial-ratio integrality

For finite lists a and b of nonnegative natural slopes, put
\[
A(n)=\prod_i(a_i n)!,\quad D(n)=\prod_j(b_j n)!,\quad
\Delta(x)=\sum_i\lfloor a_i x\rfloor-\sum_j\lfloor b_j x\rfloor.
\]

LandauIntegral.integral_of_nonnegative proves
\[
(\forall x\in\mathbb Q,\ \Delta(x)\ge0)
\Longrightarrow(\forall n\in\mathbb N,\ D(n)\mid A(n)).
\]
Its conclusion is divisibility of the original products, so their rational quotient is an integer. No analytic Landau equivalence is assumed.

The proof relates factorial-product factorizations to sums of prime valuations. Legendre's theorem writes each valuation as a finite sum of natural quotients. A common truncation bound is derived for every slope in both lists. The sums are compared term by term at rational arguments \(n/p^r\). Comparison of all prime exponents gives divisibility. Nonzero factorial products are proved explicitly; nonprime factorization coordinates vanish.

Balancing the slope sums makes the step function invariant under every integer shift. Every rational argument decomposes into its integer floor and fractional part. Consequently, nonnegative_of_cells transports a complete proof on \([0,1)\) to all rational arguments. Rational arguments suffice for the Legendre proof; no real approximation enters the result.

## Finite cells, universal conclusion

The Python emitter uses all exact rational breakpoints of the balanced slope lists. Each cell is half-open and right-continuous. For every cell and distinct slope c, the generated Lean theorem derives \(\lfloor cx\rfloor=j\) from exact cell bounds. Lean checks both inequalities defining the floor. Substitution then proves the nonnegative cell value.

The coverage theorem handles every rational point in \([0,1)\), including internal breakpoints. Integer-shift periodicity supplies the endpoint one. The final original_integral_for_all_indices declaration quantifies over every natural n. This is a universal theorem, not extrapolation from a bounded factorial scan.

The emitter accepts positive integer slope lists under existing Gamma domain limits. It rejects unbalanced inputs and negative step verdicts. Empty lists give the identity ratio. A rejected negative step is not a new proof of the converse direction. Deriving a nonintegral index from an arbitrary negative cell remains separate.

## Interfaces and trust boundary

The public modules are perfectpower.checked_factorial_unit and perfectpower.checked_landau. Proposal functions retain the source specification, exact arithmetic transcript, generated theorem, and source and specification hashes.

Run inside the pinned Lean/Mathlib environment:

~~~sh
PYTHONPATH=python lake env python -m perfectpower checked-factorial-unit --n 37 --prime 2 --depth 3 --check
PYTHONPATH=python lake env python -m perfectpower checked-landau --numerator '[12,1]' --denominator '[6,4,3]' --check
~~~

The first result is unit 5 modulo eight. The second proves universal original-factorial integrality. Omitting the check flag emits a proposal. HTTP operations checked_factorial_unit and checked_landau also emit proposals; they do not invoke Lean.

Both checkers reconstruct the entire packet from its specification before tool execution. Any mutation of arithmetic output, source, status or hashes is rejected. They compile reconstructed source and the generic theorem module in a private directory. Required theorem audits must depend only on propext, Classical.choice and Quot.sound. Missing audits, compiler failures, custom axioms, reduction axioms and timeouts reject acceptance.

Checking requires Lean 4.20.0 and the pinned Mathlib on LEAN_PATH, available through lake env in a source checkout. An installed wheel includes the two new mathematical source files but still needs the external Mathlib environment. It does not contain a compiled Mathlib distribution.

Acceptance binds the reconstructed specification and theorem source to the generic library hash. It leaves execution_verified false, preserving the remaining program-refinement boundary while certifying the original mathematical object.

## Validation and remaining work

The focused gate compiles both modules and audits 21 generic theorems. Tests check independently stripped factorials, original factorial divisibility, exact cell endpoints and interiors, domains, total budgets, JSON transport, service proposals and packet mutations. Actual kernel queries cover zero, dyadic and odd primes, higher depth, repeated and cancelled slopes, empty lists, and index \(10^{30}\).

The query receipt stores ten accepted queries, including an independent Bober family. It also records proposal source hashes for all 52 vendored Bober families. Those 52 proposals are not reported as 52 kernel acceptances. Existing Gamma tests and installed-wheel checks also pass. The focused audit is added to the global audit definition; the historical full repository rebuild was not rerun.

Make targets gamma-bridges-kernel and gamma-bridge-receipts reproduce the focused gate and stored representative queries. CI invokes the gate, and release verification requires it. Version 0.6.2 includes the new assets and checks their installed hashes.

Finding 16 now has a delivered checked route, with converse and interpreter obligations retained. The other research rows remain open: global Mordell formal completeness, Matveev premises, general norm representatives and effective exponent bounds, smooth metric identification, arbitrary marked normalized periods, arbitrary irregular systems, general nonsplit wild genus-two reduction at two, all-level Weil intertwining and orbit bounds, production adoption evidence, and physical prediction mechanisms.

The three-seed physical-wall results from e69e484 are preserved. Their uncertainty and resolution dependence remain attached to that empirical calculation and do not justify a formal arithmetic claim.

Incoming interval-certified bounce computations and Galois conductor calculations through 709d2f3 are also preserved. The latter covers supported odd wild cases and split dyadic genus-two Jacobians, while general nonsplit dyadic reduction and Lean refinement remain open. PARI-dependent calculations were not independently rerun here.

The installed-wheel verifier now builds from a fresh source copy, excluding prior build outputs. This repairs stale setuptools output across repeated or concurrent checks. Both new modules also pass all 15 configured Batteries linters with zero errors.
