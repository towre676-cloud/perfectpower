# Source definitions and Lean closure (PerfectPower 0.9.6)

This chapter upgrades the recent generating-function, binary-value, analytic-tail and A=B-inspired work from exact Python replay to Lean mathematical foundations. The audit compiles nine source modules and prints the axioms of all 69 named theorems in them. It includes the existing standard-library generating-function foundation, four new mathematical modules, and four generated binomial recurrence packets. A Python acceptance Boolean is never a premise of the generated theorem.

## Finite sums with their boundaries

`CertifiedTelescoping.lean` defines S_p(n) as the actual rational finite sum of binomial(n,k)^p over 0≤k≤n. It proves binomial shift identities with their zero-support cases, a finite telescoping theorem, and both endpoint cancellations for the certificate G(k)=k^p b(k) binomial(n+r,k)^p. The supplied rational certificate polynomials are checked by algebra inside Lean. Consequently the following are all-index identities of the defined sums, including their initial cases:

(n+1)S_2(n+1)=2(2n+1)S_2(n).

(n+2)^2 S_3(n+2)=(7n^2+21n+16)S_3(n+1)+8(n+1)^2 S_3(n).

(n+2)^3 S_4(n+2)=2(2n+3)(3n^2+9n+7)S_4(n+1)+4(n+1)(4n+3)(4n+5)S_4(n).

The first power is exactly 2^n. A general second-order uniqueness theorem proves that two rational sequences with equal seeds and the same recurrence agree everywhere when the leading coefficient never vanishes. Exact two-state recursions for the cube and fourth-power sums are then proved equal to their finite-sum definitions at every index. This removes reliance on finite-prefix agreement for these four families.

The generic antidifference bridge retains the starting index and both endpoints. It turns a checked shift ratio and rational certificate identity into the sum on any finite interval. Geometric sums and the inverse-product telescope are instantiated as all-cutoff theorems. These statements do not assert a complete Gosper or Zeilberger discovery algorithm.

`export_lean_binomial` accepts a replayed packet in the supported four-family language and emits its exact serialized rational recurrence as a theorem about the actual sum. The exporter restricts namespace syntax, rejects altered coefficients, and embeds the source packet SHA-256. The retained generated sources must equal fresh exporter output before the audit proceeds. Lean checks the emitted algebra, including nonzero denominators, rather than trusting the exporter to have performed a calculation correctly. The Python parser and exporter themselves have not been formally verified.

## What a binary64 word means

`CertifiedBinary64.lean` defines exact stored-value semantics using integer division and remainder, a 52-bit fraction, the normal hidden bit, the sign block, and the subnormal exponent. Its guarded decoder refuses words outside the unsigned 64-bit range and exponent 2047. Lean proves field reconstruction and bounds, preservation of dyadic normalization, exact multiplication, and a common-scale integer accumulation identity. A dyadic root witness implies the claimed rational perfect power.

The integer quotient rounder is proved to choose the floor or ceiling, obey the below-half and above-half cases, select the even integer on ties, and incur at most half a unit of cleared-denominator error. These are general integer statements. They cover the rounding decision kernel, not the entire Python `round_bits` encoder, exponent selection, overflow policy, or its byte transport through `struct`.

For actual retained words, Lean proves that stored 0.25 is the square of 1/2, whereas stored 0.1 is exactly 3602879701896397/36028797018963968 and is not any rational square. The latter uses its reduced denominator and an exact integer square gap. Infinity is refused and negative zero has exact value zero. These are statements about stored bits, not about an ideal real decimal value or a noisy physical measurement.

## Actual infinite remainders

`CertifiedSeriesBounds.lean` proves a weighted triangular recurrence majorant by strong induction. A second theorem derives the majorant from the normalized source coefficient recurrence itself: a_n=p_n−Σ_{j<n}q_{j+1}a_{n-j-1}. If the weighted numerator coefficients are bounded by P and every denominator prefix has absolute weighted mass at most δ<1, then |a_n|R^n≤P/(1−δ) for every n. Thus the coefficient envelope is connected to a source recurrence, not merely supplied as an unexplained assertion.

A signed geometric envelope proves summability and an absolute infinite-tail bound. Applying it to |a_n|R^n≤M gives the disk bound at |z|<R. For the recursively defined positive binomial terms, Lean proves nonnegativity, a bound on every eventual ratio, and a lower and upper interval for the actual infinite sum. The square-root interval theorem explicitly selects the nonnegative branch using squared endpoint witnesses.

The analytic identification of that recursively defined binomial sum with (1−x)^(-α) remains a separate obligation. These theorems establish the series bounds; they do not import an unproved identity with an analytic function. The complete Python packet schema and refinement of every rational-series constructor are also separate implementation obligations.

## Minimal machines from the whole response

`CertifiedRealization.lean` constructs the Hankel matrix directly from the response C A^n x, and proves its observability/reachability factorization. An invertible r-by-r Hankel block cannot factor through fewer than r states. Therefore every alternative finite rational realization with the same response at all natural times has dimension at least r. This proves an actual minimality lower bound, rather than inferring minimality from a fitted prefix. The Fibonacci two-state realization supplies a fully checked nonsingular block and a two-state lower bound.

The module also proves all-time transport through an intertwining map, and equality of protected readouts for every iterate. This is useful to DynaComp as mathematical infrastructure, but does not formalize every DynaComp compiler or its numerical application receipts. Likewise the Python rational-function cancellation algorithm and companion constructor do not acquire an execution proof merely from the Hankel theorem.

## Audit and proof map

Run `make series-kernel` with the pinned Lean 4.20.0 and Mathlib revision c211948581bde9846a99e32d97a03f0d5307c31e. The checker recompiles all nine modules, rejects compiler warnings or errors, verifies regenerated packet sources, and rejects any audited axiom outside propext, Classical.choice and Quot.sound. Its JSON receipt binds the checked source, packet files and compiler logs by SHA-256. No `sorry`, custom axiom, `native_decide`, or `ofReduceBool` is used by these proofs.

The local run used official selected Mathlib build caches. A small existing runtime shim redirected executable-path discovery to /proc/self/exe in the hosted environment; it does not alter Lean's kernel or mathematical library. The full historical root build and historical heavy catalogue audits were not repeated in this sweep. The targeted Python regression comprises 64 tests across telescoping, generating functions, generating arithmetic and binary generating functions.

The current closure is recorded in `receipts/series_kernel/proof_map.json`. Older backlog documents are historical status reports, not an exhaustive current obligation list. General Baker bounds, arbitrary-polynomial perfect-power automation, normalized-curve local parameters and basis completeness, analytic Euler-period identification, general monomial-solver completeness, and remaining compiler execution refinements are not closed by this release. Some historically listed structural targets have since received separate proofs and must be reconciled against their own receipts before claiming a complete repository-wide closure. This edition intentionally records that boundary rather than renaming research goals as finished Lean work.
