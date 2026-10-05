# Polynomial capacity: coordinates, integer domains and discrete dynamics

PerfectPower's useful unit is an exact reduction with a preserved integer image. A finite registry can then serve infinitely many polynomial presentations. This expansion adds automatic rational polynomial decomposition, complete nonlinear integer pullbacks, two-sided polynomial transport, complete Boolean sign domains, and global integer polynomial optimization. It integrates the reductions with the arithmetic engine and whole-query simplifier.

The stored experiment contains 6,422 nonlinear pullback equations. Every expanded result agrees with an independent reference construction; 141 equations previously unresolved become complete. All 3,080 quartic objectives agree with independently bounded exhaustive optimization, including every tie. Another 311,080 integer predicate evaluations agree with the returned sign domains. These are reproducible mathematical corpus results. They establish neither a world record nor superiority to general computer algebra systems.

## One mechanism, several uses

The new interfaces share ascending integer coefficient lists, exact rational algebra, complete integer fibres, explicit work budgets, and serialized evidence. `polynomial-decompose` discovers coordinates. `polynomial-relation` solves supported equations with polynomials on both sides. `polynomial-domain` returns every integer satisfying a Boolean polynomial predicate. `polynomial-optimize` returns a global minimum or maximum and every attaining integer.

The coefficient interfaces accept degree at most 64 and coefficient bit length at most 16,384. The domain solver accepts up to 128 atom occurrences and Boolean nesting depth 64 by default. Root transcripts share a node budget. Decomposition counts coefficient multiplication work and limits intermediate rational bit lengths. Exceeding a budget raises a work-limit exception or leaves the arithmetic problem unresolved; it never upgrades an incomplete list to completeness.

The broadest complete class here is univariate integer polynomial predicates and optimization, within these resource budgets. General multivariate Diophantine equations remain partial. Automatic decomposition broadens the reach of proved leaves without making an undecidable general problem decidable.

## Discovering a polynomial coordinate

Let F have degree N and suppose a proper right component has degree m, where m divides N and k=N/m. Over characteristic zero, an affine change in the intermediate coordinate lets us choose a monic inner polynomial T with constant coefficient zero. Normalize F by its leading coefficient. Then its leading part agrees with T to the kth power; lower outer terms have degree at most N-m.

Consequently coefficients of degrees N-1 through N-m+1 determine the m-1 remaining coefficients of T successively. At each step the next unknown appears linearly with coefficient k. This is the classical approximate-root construction. Once T is fixed, subtract its powers from F in descending degree to recover the outer coefficients H. Accept the decomposition only if the remainder is identically zero.

$$
F(x)=H(T(x)).
$$

The implementation tests every proper divisor m. For a fixed degree there is at most one normalized candidate: the triangular coefficient equations prove uniqueness. Thus a completed discovery run covers all rational proper right-component degrees modulo affine changes of the intermediate coordinate. It does not enumerate every equivalent affine presentation or every decomposition chain. Recursive solving can expose further layers when needed.

The returned inner component is primitive integral, has constant coefficient zero and positive leading coefficient. Its outer component may be rational; coefficients are serialized exactly. Nonmonic inputs, negative leading coefficients and multiple possible component degrees are covered. Chebyshev T6 is a focused example with proper right components of both degrees two and three.

This construction is classical. Kozen and Landau's *Polynomial Decomposition Algorithms*, Journal of Symbolic Computation 7 (1989), 445-456, supplies the relevant characteristic-zero algorithmic background: https://www.cs.cornell.edu/~kozen/Papers/poly.pdf. The present implementation uses transparent bounded rational arithmetic; it does not claim their optimized asymptotic complexity or a new decomposition theorem.

## Complete nonlinear pullback

A decomposition is useful only if its integer image survives the transport. Choose a positive common denominator s for H and define the integral polynomial K=s^d H. Then the original power equation has the exact equivalence

$$
y^d=F(x)\quad\Longleftrightarrow\quad (sy)^d=K(T(x)).
$$

Solve the smaller-degree outer equation v^d=K(u). If its complete finite list is available, retain only witnesses v divisible by s and solve every integer fibre T(x)=u. A complete Sturm transcript identifies all integer roots of each fibre, including multiple preimages. The lifted witness is y=v/s. Empty fibres are retained as empty evidence; both signs of an even power are inherited.

For example, take T=x^3+2x^2-5x-3 and y^2=T(x)^3-2. The unconditional outer Mordell curve has coordinate u=3 and witnesses ±5. Its fibre factors as

$$
T(x)-3=(x-2)(x+1)(x+3).
$$

The complete lifted answer is x in {-3,-1,2}, with y independently equal to either -5 or 5. Selecting one inverse branch would lose four solutions. Merely testing the final equation on a proposed list would also fail to establish completeness; the outer completeness and complete fibre transcripts supply that obligation.

The compiler tries existing direct leaves first, then unconditional Mordell registry leaves, exact dth-power coefficient-content removal, and discovered proper decompositions. Content scaling uses prime exponent divisibility: if y^d=r^d G(x), then r divides y, so the equation reduces to (y/r)^d=G(x). Every recursive proper composition lowers polynomial degree. Unsupported outer equations remain unresolved; infinite generators remain structured rather than being sampled into finite lists.

One must not cancel a nonlinear outer map. H(T(x))=H(S(y)) does not imply T(x)=S(y), because H need not be injective. The implemented transport uses a complete outer solution relation and complete integer fibres, preserving every branch.

## Polynomials on both sides

The relation interface accepts L(x)=R(y). Either side may be affine, in which case the other coordinate gives an exact filtered generator with a divisibility condition. A nonzero quadratic side a*y^2+b*y+c admits complete-square transport even when a is negative:

$$
(2ay+b)^2=4aL(x)+b^2-4ac.
$$

The transformed square equation is handled by the polynomial compiler. Every transformed witness is then lifted through its original affine fibre. An exact polynomial-power side R(y)=W(y)^d works similarly, with complete nonlinear fibres W(y)=v. Both orientations are tried.

For x^3-2=(2y-1)^2, the complete points are (3,-2) and (3,3). For x^3-2=(y^2-5)^2, the complete answer is (3,0). These examples show why the witness is a coordinate with its own image, rather than an unrestricted square-root placeholder.

The current relation solver is not a complete solver for arbitrary separated polynomial equations. If neither an affine generator nor a supported finite power transport is available, it returns unresolved. A shared nonlinear outer component is not treated as cancellable.

## Complete integer sign domains

An atom is a polynomial compared with zero using =, !=, <, <=, > or >=. Arbitrary finite combinations with and, or and not are supported. For each distinct nonconstant polynomial, the solver obtains a complete real-root Sturm transcript down to intervals between adjacent integers.

Collect both endpoints of every unit interval containing real roots. Each collected integer becomes a singleton cell; intervening integer ranges and the two tails become additional cells. A root-containing unit interval has no integer strictly between its endpoints, even if it contains several nearby real roots. Every remaining gap has no real root in its interior. Polynomial signs are therefore constant on the integer points of each gap, and exact evaluation at one representative suffices. Singleton cells handle zeros and endpoint changes explicitly.

Repeated roots require no special sign-flip assumption. Root locations come from the squarefree root computation, while truth values are evaluated on the original polynomial. Constant polynomials, the zero polynomial and empty Boolean combinations are evaluated directly.

The accepted cells merge into a finite union of closed integer intervals. A null endpoint denotes an infinite tail. The result is complete over all integers and reports a finite cardinality precisely when all accepted intervals are bounded. The solver scans the transcript cells, not the integers inside an interval.

For instance, a quadratic translated by H=10^80 can define exactly [H,H+3]. Coordinate magnitude does not force enumeration of the preceding integers. Evidence replay checks the supplied root trees, exact sample signs, Boolean evaluation and merged intervals without rerunning root discovery.

## Global integer optimization from discrete dynamics

Given a feasible sign domain and objective G, use the exact forward difference

$$
\Delta G(n)=G(n+1)-G(n).
$$

Its sign governs integer motion directly: positive differences increase the objective, negative differences decrease it, and zeros give adjacent ties. This avoids assuming that rounding a real derivative critical point preserves every integer optimizer.

Isolate all real roots of the difference into unit integer intervals. Candidate coordinates consist of feasible finite endpoints, endpoints of root-containing unit intervals, and their successors when feasible. Between these regions the difference has fixed strict sign, so an integer objective is strictly monotone and cannot have an omitted interior minimum. Every zero difference is in a retained critical region, so adjacent ties survive. This argument also covers disconnected Boolean domains and isolated feasible points.

On an unbounded feasible tail, the objective's degree parity and leading coefficient decide whether the value tends to negative infinity. Such a result is explicitly UNBOUNDED. If no feasible coordinate exists the result is EMPTY. A constant objective returns the entire feasible domain as its optimizer set, possibly infinite. Maximum queries apply the same reasoning to -G and restore original values.

Consider the translated quartic

$$
G(x)=(x-H)^2(x-H-1)^2,\qquad H=10^{60}.
$$

Its global minimum is zero, attained at exactly H and H+1. The saved run uses 401 root-tree nodes and no interval scan over that enormous translation. The receipt retains the complete difference tree and both ties. This is an exact integer result, not a numerical critical-point estimate.

## Whole-query integration

The arithmetic engine now invokes composition after its established direct methods fail. Its verifier dispatches the new composition and content proofs. The whole-query simplifier also recognizes supported separated polynomial equalities, substitutes every complete finite pair into the remaining assertions, and preserves side conditions and unrelated variables.

A final univariate pass converts a complete one-variable polynomial Boolean query to a QF_LIA interval union. It keeps the variable's original integer value, so the replacement is pointwise equivalent, not merely equisatisfiable. Reverse model lifting follows every preceding coordinate map and checks the original query context.

For the familiar square-cube parameterization a coupled inequality can become t^3>=8 and then the linear restriction t>=2. This is useful to a downstream linear solver even though no variable is removed in that last step. Empty and universal domains are preserved explicitly.

The final univariate SMT converter supports degree 64 with its own polynomial normalization. The earlier multivariate matcher remains degree eight. Unsupported division, modulus, conditionals or nonpolynomial operations cause the new pass to decline and preserve the residual. This interface remains a single-query integer fragment; the separate incremental command replay tool handles command scopes and histories.

## Stored corpus and independent checks

The source ledger is `receipts/divisor_sum/complete_quartics.json`, with 3,080 complete quartic point lists. Its SHA256 is recorded in the new summary. Each quartic is composed with two nonsymmetric maps, having ascending coefficients [0,-4,1,1] and [0,1,0,1,2]. This produces 6,160 degree-12 and degree-16 equations.

The runner also takes every available unconditional nonzero Mordell target between -100 and 100: 131 outer curves. Two cubic or quintic coordinates per curve give another 262 equations of degrees nine and fifteen. Nonempty curves receive a translated coordinate that plants an independently known integer preimage. Reference fibres are computed using the rational-root theorem and signed divisors, independently of the Sturm implementation.

Of these 6,422 equations, the previous engine already completed 6,281. All transformed quartics were already covered. The new completion gain is 141 transformed Mordell equations. The expanded compiler completes every case and agrees on all 4,132 point occurrences. Occurrences count appearances across presentations, not distinct mathematical points.

The saved fixed-order timings are 18.836 seconds for the previous engine and 18.972 seconds for the expansion. They share process caches, exclude independent reference construction and replay, and establish no speed advantage. The benefit measured here is coverage and reusable complete output. Independent industrial workload and competing solver comparisons remain future experiments.

For each of the 3,080 source quartics, the runner finds the global integer minimum and every tie. The reference independently scans a Cauchy bound for the forward difference, rather than consulting the returned candidate list. Every answer agrees. A separate sign predicate per quartic is checked at 101 integer coordinates, giving 311,080 agreements. Dedicated receipts retain the huge translated optimum, the degree-64 sign example and a two-sided nonlinear witness.

The focused test module covers randomized nonmonic decompositions, both Chebyshev component degrees, omitted integer-image branches, evidence tampering, budget exhaustion, repeated and closely spaced roots, Boolean domains, large coordinates, degree 64, disconnected optimization, all ties, empty and unbounded results, nonlinear witness fibres, and whole-query side conditions and model lifting. Full-suite logs are saved separately. Exact replay is a correctness check on the implementation's mathematical evidence; it is not kernel verification of Python execution.

## Connecting Gamma and polynomial capacity

Fixed-shift Gamma quotients, finite products, rising factorials and fixed-width binomials belong at the input boundary. Normalize them exactly into N(n)/D, retaining their natural-index domain and excluding Gamma poles according to the supplied expression. Then a power-value query becomes

$$
D y^d=N(n)\quad\Longleftrightarrow\quad (D y)^d=D^{d-1}N(n),
$$

with the indispensable condition D divides the transformed witness. Automatic decomposition now applies inside that polynomial backend as well. The added `gamma-domain` and `gamma-optimize` commands directly expose complete sign domains and global optima for the fixed normalized expressions. Their evidence retains the normalization, the natural-index constraint, the positive denominator, and the complete polynomial transcript. For sign domains and polynomial optimization, D is positive, so signs of a normalized rational expression can be decided from its numerator. A constant rational objective denominator scales the optimum value while preserving every optimizer.

The concurrent Gamma arithmetic expansion is preserved in this release; see `GAMMA_ARITHMETIC_MONOGRAPH.md`. Variable-width factorial ratios are a different representation: their useful engine uses prime valuations, stripped units and polynomial-coefficient recurrences. Turning a growing factorial into an expanded polynomial would discard the structure that makes the query tractable.

The most useful architecture therefore has exact normalization at the front, a shared domain-aware polynomial backend in the middle, and structured valuation or recurrence engines when the expression is not a fixed polynomial. A recurrence generating equation keeps its boundary term; an algebraic reduction keeps its integer image. These are the same discipline applied to different dynamics.

## Proof scope and formal handoff

No new Lean declarations are introduced by this polynomial expansion. Existing unconditional outer registries retain their theorem provenance; classical algebraic identities and complete Sturm transcripts are checked by exact Python replay. The result fields explicitly retain `execution_verified: false`. The concurrent Gamma push has its own narrower Lean proof map.

The existing project has checked integer-root trees for particular certification routes and signed Sturm-chain algebra. Its general classical real-root variation theorem remains a formalization obligation. This release does not silently promote arbitrary Sturm counting or the whole Python compiler to a verified kernel.

The reusable next Lean statements are normalized-component uniqueness, denominator-scaled pullback equivalence, coefficient-content divisibility, Boolean truth on root-free integer cells, and the forward-difference candidate theorem with all ties. Proving these once would let the same corpus receipts feed a generic certificate interpreter, rather than generating thousands of unrelated proofs. Full compiler correctness and arbitrary polynomial power-value completeness remain separate tasks.

## Reproduction

Run from a checkout with Python 3.10 or later. The computational core requires only the standard library. The monograph PDF renderer separately uses ReportLab and Matplotlib.

```sh
PYTHONPATH=python python -m unittest discover -s python/tests
PYTHONPATH=python python -m unittest discover -s python/tests -p test_polynomial_capacity.py
PYTHONPATH=python python python/develop_polynomial_capacity.py
```

The corpus command writes deterministic input and answer data plus environment-dependent timings under `receipts/polynomial_capacity/`. It also preserves source hashing and serialized examples. Its `--limit` option selects a smaller quartic subset for a quick local run; the full saved summary uses all 3,080 quartics.

```sh
PYTHONPATH=python python -m perfectpower polynomial-decompose --coeff '[-1,0,18,0,-48,0,32]'
PYTHONPATH=python python -m perfectpower polynomial-domain --predicate '{"poly":[-2,0,1],"relation":"<="}' --verify
PYTHONPATH=python python -m perfectpower polynomial-optimize --objective '[0,0,1,-2,1]' --verify
PYTHONPATH=python python -m perfectpower polynomial-relation --left '[-2,0,0,1]' --right '[25,0,-10,0,1]' --verify
```

```sh
PYTHONPATH=python python -m perfectpower gamma-domain --spec '{"kind":"binomial","width":2}' --relation '<=' --threshold 3 --verify
PYTHONPATH=python python -m perfectpower gamma-optimize --spec '{"kind":"binomial","width":2}' --verify
```

The Gamma domain example returns exactly [0,3]; the Gamma optimizer returns value zero at both indices 0 and 1. Thresholds accept exact rational strings; floating thresholds are rejected. The fixed Gamma quotient domain continues to exclude poles. Variable-width factorial ratios remain in the valuation engine.

The domain example returns exactly [-1,1]. The optimization example returns value zero with optimizers [0,1]. The relation example returns exactly (3,0). The decomposition example returns both proper component degrees.

## What to build next

The immediate high-value extensions are complete generator pullback through certified integer-image conditions, a generic Lean transcript interpreter for sign domains and discrete optimization, and independently sourced industrial queries that stress these exact reductions. General separated-polynomial classification needs a genuinely broader mathematical backend; additional catalogue entries alone are not enough.

For practical use, retain the new complete univariate domain object as a shared intermediate representation. It can drive exact count queries, optimizer queries, host-solver replacements and domain checks for normalized Gamma expressions. This turns an equation result into a reusable computational object while keeping its domain and proof scope visible.
