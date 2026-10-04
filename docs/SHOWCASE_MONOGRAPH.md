# Three complete answers instead of three endless searches

The purpose of these demonstrations is to make PerfectPower's practical value visible in a complete journey: an ordinary integer question enters, the program recognizes a supported mathematical structure, and a small, inspectable answer leaves. The examples are deliberately constructed to expose that structure; they are not presented as customer workloads or as a representative industrial benchmark. Their underlying complete families are already part of the repository. This push adds an automatic coordinate optimization, a fast counted and filtered query interface, whole-query finite projection, standalone programs and reproducible measurements.

## A nonlinear answer hidden near a huge coordinate

Let H=10³⁰. Ask for every integer pair (x,y) satisfying

\[y^2=\bigl(2(x-H)^3-2(x-H)\bigr)^2+25.\]

The result consists of exactly ten pairs. At x=H−2 and x=H+2, y is ±13. At x=H−1, H and H+1, y is ±5. There are no other integer pairs, including outside any chosen search window.

This is a degree-six equation after expansion. A coordinate scan starting at one would have to reach an enormous number before seeing even its first solution. But changing the origin does not change the integer problem: set t=x−H, solve the small centered equation, and translate every answer back. The core divisor identity is

\[(y-P(t))(y+P(t))=25.\]

There are only finitely many factor pairs. Their compatible values require P(t)=0 or P(t)=±12, where P(t)=2t³−2t. Complete integer root calculation gives t=−1,0,1 in the zero fibre and t=±2 in the nonzero fibres. This proves why five arguments and their two signed square roots exhaust the equation.

The important software change is that the user need not supply a centered presentation. `compile_constraint` recognizes square-plus-constant structure in the fully expanded polynomial, and `solve_centered` proposes an integer coordinate shift from its coefficients. Binomial expansion checks the coordinate identity in both directions. The shift is used automatically when it does not increase the constant-term magnitude; an explicitly requested shift remains available. Centering changes computational cost, not the equation or its domain. Difficult root or divisor work still respects the existing work limit.

For this instance the compiler chooses exactly H and solves the fibers with 12 divisor trials, rather than using the enormous original constant term as a trial-division bound. The tests also confirm that the uncentered solver exhausts a 1,000-trial budget while the centered solve succeeds. The coordinate itself is never scanned. Large coefficients still cost integer arithmetic; coordinate magnitude is not treated as an enumeration radius.

The packet includes the original generated search program and a standalone specialized program containing the complete five-argument answer. Both give the same empty result on the measured prefix through 100,000. That prefix comparison alone would not establish completeness. The specialized program also returns every answer through H+10 immediately, because its complete list was obtained from the finite arithmetic reduction. Generated square-test helpers now use the exact built-in integer square root, so this comparison does not penalize the baseline with a general-purpose binary root search.

`lean/HiddenNeedle.lean` emits an independent native solve of the centered equation and an integer-translation completeness statement for the original coefficients. The new emitted file has not been compiled in this run. The Python result is an exact replay of the existing divisor mathematics, with `execution_verified=false`; successful Python execution is not reported as acceptance of that Lean instance.

## Exact size planning under a 1,000-digit bound

The second question is: which positive integer sizes n have a triangular total n(n+1)/2 that is also a square? A square arrangement and a triangular arrangement can then hold the same total. Ask for every valid size up to 10¹⁰⁰⁰, while additionally requiring n≡1 modulo 97 and its nonnegative square root m≡1 modulo 5.

There are exactly 1,307 valid sizes under that bound before the additional filters, and exactly 28 afterward. The complete family is the existing square-triangular Pell orbit:

\[X_j+Y_j\sqrt8=(3+\sqrt8)^j,\qquad
 n_j=(X_j-1)/2,\quad m_j=Y_j,\quad j\ge1.\]

The first sizes are 1, 8, 49, 288 and 1,681, with square roots 1, 6, 35, 204 and 1,189. `PerfectPower.SquareTriangular.triIdx_iff` supplies the arithmetic correspondence and completeness of this family. The new query interface computes its integer coordinates, establishes an exact monotone boundary and counts the periodic admissible positions.

The last unfiltered index is j=1307. Its size is at most the requested bound, and the next orbit element exceeds the bound. Exact binary powering and monotone bisection find this boundary in 22 evaluations. No floating-point logarithm decides whether a point at the boundary is included. The full modular state has period 48, and both residue conditions hold exactly at orbit indices j≡1 modulo 48. Thus j=1,49,…,1297 gives the 28 accepted sizes. The next accepted orbit index is 1345, whose size exceeds the bound.

The factor of two in n=(X−1)/2 matters. The modular engine tracks X and Y modulo twice the least common multiple of the requested moduli. It does not divide a residue modulo 97 or 5 as though division by two always preserved the required information. The period is obtained by returning the complete state to its initial value under an invertible unit transition. A state budget failure produces no completed schedule or count.

`query` returns the count and exact boundary witnesses. `select` returns the requested zero-based member of the filtered positive family by periodic indexing and binary powering. These operations support arbitrary nonnegative integer bounds and congruence filters on the size or root. They operate within this proved square-triangular family; they do not solve an arbitrary nonlinear integer constraint. The specific new count computations remain Python evaluations rather than new Lean certificates.

## Remove a nonlinear arithmetic subsystem from a whole query

The third demonstration is a small collection of complete-family SMT queries. Each has four integer variables and combines a nonlinear arithmetic relation with further constraints. The source families are the existing complete lists for y²=x³+17 and y²=x³+22, together with the complete quartic y²=3x⁴+3x²+1. The source theorem files and point lists are recorded in the provenance packet.

The first family has 16 integer points. Its largest x-coordinate is 5,234, with square roots ±378,661. Therefore

\[y^2=(x-H)^3+17,\qquad x\ge H+5235\]

has no integer solution at all. This follows from a complete list, rather than from searching some number of x-values and failing to find a square.

A positive witness example adds x=H+5234, y≥0, z=x−H+y, w=2z+1 and w>100000. The finite arithmetic relation leaves the unique positive-root pair x=H+5234, y=378661, so the remaining task is simply z=383895 and w=767791. Changing the last condition to w≤1000 makes the whole query impossible. The constraints involving the extra variables are retained, not discarded when the curve is solved.

The integral-image example asks for y²=(6x+1)³+22. The complete source curve has only (3,±7), and 3 is not in the integer image of 6x+1. Thus the transformed relation is empty, despite having rational preimages. The quartic example adds w=xz and w≠0. The complete quartic list forces x=0, so w=0 for every possible z and the whole query is unsatisfiable.

The reusable operation is existential projection. If R(x,y) has a complete finite list L, then

\[\exists x,y\; R(x,y)\land C(x,y,z,w)
\quad\Longleftrightarrow\quad
\bigvee_{(a,b)\in L} C(a,b,z,w).\]

The earlier finite-formula adapter replaced R with a finite disjunction of point bindings while retaining x and y. The new `project_finite_query` takes the next step: it substitutes each complete point into every residual assertion, removes precisely the corresponding two declarations, keeps the other integer variables, and performs exact constant simplification. The existing sort-checked linear router promotes the result to QF_LIA only when the entire remaining expression is linear. Arbitrary nonlinear conditions on the remaining variables can persist as QF_NIA.

Completeness comes only from the supported theorem registry, never from a bounded point scan. Unsupported source families are rejected. A branch budget failure returns no projected query. The tests check the projected constraints against independent evaluation of the original formulas across remaining-variable assignments, including nonlinear residuals and alternative variable names. Every SAT model in the local timing experiment is lifted back to an actual original arithmetic point and substituted into the original query.

## The measured local result

The timing ledger runs six curated queries three times each, with fresh installed Z3 5.1.0 solvers, a two-second timeout per query and alternating variant order. Original queries give nine decisive answers in 18 trials, taking 18.371 seconds of summed solve time. The finite point-binding form answers all 18 in 0.043 seconds. The projected form also answers all 18 in 0.008 seconds. Every decisive answer agrees with the independently specified case result; unknown answers remain unknown in the ledger.

These numbers measure solver time for this small designed collection. Parsing time is reported separately. The packet records reduction and projection construction times; the solve totals exclude those costs and exclude Lean proof compilation. They do not overturn the repository's earlier industrial trial, which showed no overall industrial speedup. They do demonstrate the particular effect intended here: once a difficult complete arithmetic relation is available, a whole constraint problem can become a small linear problem rather than an unbounded nonlinear search.

## Running and extending the examples

From the repository root, `python python/run_showcase.py` rebuilds the result packets, standalone programs, six source queries, point-binding reductions, projected queries and emitted Lean files. This core run uses the standard library. Add `--benchmark` to repeat the local solver trial when the optional installed Z3 package is available. The complete repository ZIP contains every source and result; it does not require a separate sequence or curve download for these examples.

```sh
python python/run_showcase.py
python python/run_showcase.py --benchmark --timeout-ms 2000 --repeats 3
PYTHONPATH=python python -m perfectpower square-triangular-query --power-ten 1000 --filter index:97:1 --filter root:5:1
PYTHONPATH=python python -m perfectpower centered-divisor --coeff 0,-2,0,2 --k 25
PYTHONPATH=python python -m perfectpower finite-project receipts/showcase/queries/mordell_witness_with_extra_variables.smt2 --output /tmp/projected.smt2
PYTHONPATH=python python -m unittest discover -s python/tests -v
```

Windows users can run the first two commands directly from the extracted repository using their working Python executable. For the module commands, install the local package or set its Python directory on the module path using the shell's environment-variable syntax. The generated specialized program is independent of the package: importing it and calling `run(N)` returns the finite hits through N.

The final integrated base preserves the parallel native quartic push and its 420 complete curve lists. This batch adds the example interfaces and reductions on top of that work. Its validation packet records the final test counts, source hashes, exact results and emitted-proof status.

The final integrated Python suite runs 438 tests successfully with four skips in 43.260 seconds. All 25 focused showcase, divisor and finite-formula tests pass. A fresh extraction of the complete archive reproduces the three example results and all 18 query files byte-for-byte. Python compilation and whitespace checks pass.
