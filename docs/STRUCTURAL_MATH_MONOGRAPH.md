# Structural arithmetic, exact inequalities and native two-isogeny bounds

This release turns three reusable parts of the earlier research into executable PerfectPower APIs: prime-exponent species, rational certificates for polynomial inequalities and linear stability, and native squareclass descent for elliptic curves with rational two-torsion. It integrates species with the existing population and catalogue machinery, reuses the PSG polynomial algebra for inequality identities, and supplies replayable evidence for both sides of a two-isogeny. It adds no dependencies to the core package.

## What was recovered and what was chosen

The source review covered the earlier SIT species monograph, the coercivity-invariant graduate monograph, the Phase III scalar Schur recurrence, the PSG source recovery, and the 571a1 Cassels–Tate laboratory. Their strongest reusable common denominator is exact finite algebra with explicit source binding. This release extracts that denominator rather than importing every theoretical claim from those documents.

The SIT exponent/occupation coordinates become a structural population engine. Coercivity and invariant-square calculations become rational Gram and constrained lower-bound certificates. The scalar Schur work becomes real rational Toeplitz positivity with singular frontiers retained. The Selmer work motivates complete squareclass candidates, rigorous local exclusions and a two-sided rational rank bound in a supported two-torsion family. Existing factored local sieves, observable machines, witness resolvents, weighted Hodge routines and the Fisher replay are reused or left in their established modules.

Two old homotopy claims were not used as implementation premises: cohomology requires a kernel modulo an image, and a minimal L-infinity structure with unary bracket zero must satisfy graded Jacobi for its binary bracket. Arbitrary homotopy transfer, complex Schur recursion, general Selmer groups, Cassels–Tate pairings and global elliptic saturation are outside this addition.

## Species and complete bounded structural populations

For a positive integer, sort its positive prime exponents into a nonincreasing tuple a = (a1,...,ar). A species forgets which primes carried those exponents. Its least representative is m(a) = product p_i^a_i, using the first r primes in increasing order. Pairing larger exponents with smaller primes minimizes the product: exchanging exponents A >= B on primes p < q multiplies the incorrectly ordered product by (q/p)^(A-B) >= 1. Replacing any prime by a smaller unused prime also decreases the representative.

The occupation coordinates are c_i = a_i - a_(i+1), with a_(r+1)=0. Conversely, a_i is the sum of c_j for j >= i. Thus m(a) is also the product of the first-i primorials raised to c_i. Trailing zero occupations are removed; the empty tuple represents 1.

The engine computes total multiplicity Omega = sum a_i, support r, divisor count tau = product(a_i+1), the divisor-lattice rank polynomial product(1+z+...+z^a_i), and the gcd of the exponents. A species is a d-th power exactly when d divides every exponent. The number of its divisors that are d-th powers is product(floor(a_i/d)+1). The unit is treated separately as a power of every positive degree.

`SpeciesPopulation(N)` contains precisely the tuples with m(a) <= N. This counts structural types, not all integers <= N. Its dynamic-programming state retains the next prime index, the preceding exponent cap, the remaining integer product bound, and optional remaining divisor-count and Omega targets. Branches append one positive exponent in ascending order; the stop branch precedes extensions. Exact integer division updates the bound. Every tuple has exactly one path, so branch counts support forward selection and inverse ranking without enumerating integers up to N.

The optional filters intersect: `power=d` requires exponents divisible by d; `power_free=k` requires every exponent below k; `divisor_count=t` and `omega=s` impose exact targets. Counts, ranks and selections use integer arithmetic throughout. Exhausting the state budget raises `WorkLimit`; a partial traversal is never published as a complete count. Bounds are limited to 512 bits and standalone exponent tuples to 128 entries, each at most 4096.

```python
from perfectpower.species import SpeciesPopulation, invariants
from perfectpower.populations import ExactPopulation

p = SpeciesPopulation(10**12)
assert p.count() == 4357
assert p.rank(p.select(2178)) == 2178
q = ExactPopulation({'kind': 'species', 'bound': 1000, 'power': 2})
rows = q.sample(min(5, q.count()), seed=71)
best = q.optimize('divisor_count', sense='max')
```

The existing population protocol supplies sampling, pages, partitions, exports, persistent catalogue entries and complete bounded optimization of four scalar invariants. Optimization traverses the species ranks within an explicit work budget. General polynomial restrictions and four-way population comparisons are not defined for this new kind; unsupported restrictions raise. Selection records retain the exponent tuple as their identity and check the scalar payload on inverse ranking.

Reproduced populations contain 289 species below 10^6, using 233 states, and 4357 below 10^12, using 2831 states. Below 10^100, requiring squares with divisor count 81 leaves five species and uses twelve states. This constrained result does not imply inexpensive unconstrained counting at that bound.

## Exact positivity and constrained polynomial bounds

A rational symmetric matrix is certified by A = L D L-transpose with L unit lower triangular and every diagonal entry of D nonnegative. A zero pivot is accepted only if the remaining residual column is zero. This admits singular positive semidefinite matrices and rejects indefinite zero-diagonal examples without division by zero. The checker reconstructs the matrix, validates the factors and signs, and optionally binds an independently supplied source matrix. Positive definiteness requires every pivot to be strictly positive.

A polynomial Gram certificate retains its polynomial basis z and matrix Q, checks Q >= 0, and reconstructs the polynomial z-transpose Q z coefficient by coefficient. Weighted squares are a diagonal Gram special case. Automatic discovery covers globally nonnegative quadratics through their affine Gram matrix. Higher-degree certificates require supplied witnesses; there is no general SDP search or completeness claim.

For a domain g_i >= 0 and h_j = 0, a lower bound f >= ell is accepted only after the exact identity

    f - ell = sum_I sigma_I product_(i in I) g_i + sum_j q_j h_j

has been checked. Every sigma_I has a checked nonnegative Gram certificate; every q_j is a retained polynomial. Empty index sets supply global nonnegative terms. Products of constraints permit preordering certificates. Since each summand in the first sum is nonnegative on the declared domain and the second sum vanishes there, the inequality follows for every real point in that domain. A representation of -1 establishes infeasibility. Source polynomials, variable order and domain constraints remain in the packet, so replay cannot silently substitute a different problem.

Quadratic minimization checks the Hessian for positive semidefiniteness and solves its rational stationarity equation. A solution point plus a basis of the Hessian kernel describes every real minimizer. An inconsistent stationarity equation is rejected as convex and unbounded below; nonconvex or higher-degree objectives are rejected by this discovery API. The constant lower bound is separately replayable.

```sh
python -m perfectpower quadratic-minimum --variables x,y --objective '(x-y-2)^2/3+5'
python -m perfectpower inequality-bound --variables x,y --objective '3-x^2-y^2' --lower 2 --inequalities '["1-x^2-y^2"]' --squares '[{"indices":[0],"polynomials":["1"]}]' --out bound.json
python -m perfectpower inequality-check bound.json
```

The last certificate proves f >= 2 on the closed unit disk. `inequality-check` also replays PSD, Gram, Toeplitz and linear Lyapunov packets. A quadratic-minimum result contains a nested lower-bound packet; callers replay that nested packet with `check_lower_bound`.

## An exact new result for the recovered PSG factors

The retained source has six Darboux factors:

    v, a, 2a-1, v+4-8a, av-2a-2pv+1, 2av+4a-4pv-v-2.

Define E as the sum of their squares. Completing the two squares a^2 + (2a-1)^2 = 5(a-2/5)^2 + 1/5 gives E >= 1/5 globally. The release records and replays that coefficient identity with all the other squares retained. This is a certified lower bound; global sharpness is not asserted.

On the equality domain v=0, E = a^2 + 88(a-1/2)^2. Its exact minimum is 22/89, attained at a=44/89 with arbitrary real p. The implementation obtains this from quadratic minimization and transports it back to the original three-variable polynomial using the exact ideal multiplier (E-E|v=0)/v. It also evaluates the original E at the reported point. These statements concern the declared algebraic sum of squares; no physical energy interpretation or Lyapunov monotonicity of E is inferred.

## Real Toeplitz frontiers and linear stability

For rational real moments c_0,...,c_(n-1), the Toeplitz matrix T_ij = c_|i-j| is checked by the same singular-aware decomposition. Packets retain the moments, scalar pivots, leading determinants and successive pivot ratios. A ratio after a zero pivot is `null`, not a fabricated reflection coefficient. The examples include the singular all-ones matrix and a strictly positive margin below floating-point resolution. Complex Hermitian moments and a full scalar reflection recurrence are not implemented here.

For x-dot = A x, a certificate retains a positive definite rational metric P, a nonnegative rational alpha, and the residual R = -A-transpose P - P A - 2 alpha P >= 0. Hence the squared P-norm obeys V(t) <= exp(-2 alpha t) V(0) for t >= 0. Alpha zero establishes nonincrease; it alone does not assert strict asymptotic decay. The synthesis routine solves the rational Lyapunov equation for A+alpha I with right-hand side -I and then checks the resulting metric. Synthesis supports dimension at most eight; supplied metrics and PSD checks support dimension at most 64.

```sh
python -m perfectpower linear-stability --matrix '[[-1,10],[0,-2]]' --alpha 1/4
python -m perfectpower toeplitz-schur --moments '[1,"1/2","1/4"]'
```

The first example certifies a nonnormal system through a metric rather than relying on its Euclidean symmetric part. There is no nonlinear contraction or interval-coefficient claim.

## Native descent and two-sided rank bounds

The supported model is E: y^2 = x(x^2+a x+b), with integral a,b and b(a^2-4b) nonzero. For each nonzero rational point, its x squareclass has a signed squarefree representative d dividing b. A corresponding homogeneous cover is

    w^2 = d u^4 + a u^2 v^2 + (b/d) v^4.

Primitive integral cover points with u nonzero and v positive map to x=d u^2/v^2, y=d u w/v^3. Recovery from a rational point and lifting back check the equations exactly. The point (0,0) and the identity O are explicitly exceptional in the transport interface. Their descent images are respectively the squareclass of b and 1, already in the candidate universe.

Candidate generation factors b within a work budget and enumerates every signed squarefree divisor. At a prime power p^k, primitive pairs are exhausted by two projective charts: v=1 with arbitrary u, and u=1 with v divisible by p. Unit scaling changes the quartic by a fourth power and preserves square membership. The routine enumerates these complete finite charts against all squares modulo p^k. No surviving chart means a genuine rational obstruction; a surviving chart remains unresolved. The real test excludes covers whose quartic is strictly negative on every nonzero real pair. The default finite tests are modulo 8, 9, 5 and 7. Primes, depths, class dimensions and total chart work have explicit caps.

The two-isogenous curve is E': y^2 = x(x^2-2a x+a^2-4b). Classical two-isogeny descent gives

    2^rank E(Q) = |alpha(E(Q))| |alpha(E'(Q))| / 4.

Each actual image is an elementary two-group contained in its finite surviving candidate set. If the two survivor counts are K and K', their dimensions are at most floor(log2 K) and floor(log2 K'). Therefore the sum of those two integer bounds minus two is a rigorous rational Mordell–Weil rank upper bound. This argument does not require the finite survivor sets themselves to be groups, to have power-of-two cardinality, or to equal complete Selmer groups. Rank upper bound zero proves exact rational rank zero; a positive upper bound leaves the rank unresolved.

```python
from perfectpower.descent_squareclasses import two_isogeny_rank_bound, check_rank_bound
receipt = two_isogeny_rank_bound(0, -1)
assert receipt['rank_exact'] == 0
assert check_rank_bound(receipt, 0, -1)
```

```sh
python -m perfectpower two-torsion-descent --a 0 --b -2 --rank-bound
```

The reproduced corpus contains all 306 nonsingular integral models with -6 <= a <= 6 and -12 <= b <= 12. Rank upper bounds are zero for 99, one for 171, two for 35 and three for one. Thus 99 models have proved rational rank zero by this calculation and the classical identity. These are models, not asserted distinct isomorphism classes. This is neither a basis computation nor an integral-point census; rank zero still permits torsion points.

The underlying classical descent is described in John Cremona, *Algorithms for Modular Elliptic Curves*, Chapter III, section 3.6: https://johncremona.github.io/book/fulltext/chapter3.pdf. Rational SOS witness reconstruction is also discussed by Peyrl and Parrilo: https://www.mit.edu/~parrilo/pubs/files/PeyrlParrilo-ComputingSumOfSquaresDecompositionsWithRationalCoefficients.pdf. The code here performs exact witness generation in the stated cases and exact replay; it does not claim to implement their complete algorithms.

## Reproduction, evidence and remaining limits

Run `make structural-math` to execute the focused tests and regenerate `receipts/structural_math/`. The receipts include structural populations, the PSG coefficient identities, matrix certificates and both descent sides for every corpus model. The source map is in `receipts/structural_math/source_provenance.json`. The handoff at the repository root gives entry points for subsequent development.

The test suite independently traverses integers for small species bounds, checks every combination of the supported filters, tests rank inverses, sampling and catalogue persistence, checks PSD matrices constructed independently as B B-transpose, rejects altered packets, and compares local charts against every primitive residue pair on small moduli. Rational point/cover round trips and public CLI calls are included. Existing population and Mordell descent regressions and a wheel installed outside the checkout provide additional integration checks; the release verification receipt records their actual outcomes.

All new acceptance is exact Python arithmetic and mathematical reasoning. Every new certificate labels `formal_verification` false. No new Lean theorem has been compiled, and no repository-wide Lean or historical numerical census is claimed by this release. General SOS discovery, fast arbitrary factorization, global elliptic saturation and automatic formalization remain separate work.
