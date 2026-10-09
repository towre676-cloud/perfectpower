# Global nonlinear populations and exact Pell queries

This release extends the checked query route to every integer solution of y²=U(x)³−2 and y²=U(x)³−4 for a declared nonconstant integer polynomial U. It also supplies exact cutoff counts, restrictions, local rank/selection and bivariate minima for the nonnegative solutions of y²=2x²+1, together with selections at global recurrence ranks. The finite source curves and the infinite Pell orbit each have a rebuilt completeness proof.

## A proved bound for every polynomial fibre

Let H(U) be the sum of the absolute values of U's coefficients in ascending order. For a valid coefficient list with nonzero last coefficient and positive degree, PolynomialFibre proves that U(x)=s implies |x|≤H(U)+|s|+1. The proof uses integer Horner evaluation, induction on the coefficient list and the reverse triangle inequality. It does not assume a real root finder, numerical height estimate or external list of roots.

The fibre is the exact filter of the integer interval supplied by that theorem. Its membership theorem is equivalent to U(x)=s without any interval appearing in the conclusion. Flat-mapping these fibres over a globally complete source population yields a globally complete population in the original coordinates. This is a generic pullback theorem for any finite source predicate with an established completeness equivalence.

The source curve y²=s³−2 has precisely (3,−5) and (3,5). The source curve y²=s³−4 has precisely (2,−2), (2,2), (5,−11) and (5,11). The existing Gaussian-integer proof for the latter now lives in MordellMinus4Core; the original module retains its natural-input hit theorem and imports the core. No analytic population assumptions are introduced by this extraction.

For U(x)=x²+2, the minus-two population consists of x=−1 and x=1, with both signs of y=5. For U(x)=x⁴+3 the only input is x=0, again with both ordinate signs. For U(x)=x²+1, the minus-four population has x=±1 with y=±2 and x=±2 with y=±11. Repeated roots contribute one input each. Missing integral fibres return an empty complete population. Positive and nonnegative input domains are explicit predicates applied to these original coordinates.

## Infinite generation with an exact stopping certificate

PellPopulation starts at (x,y)=(0,1) and uses the recurrence (x,y)↦(3x+2y,4x+3y). A norm invariant proves y²=2x²+1. The existing elementary descent is rebuilt in a standalone module and proves that every solution with x≥0 and y≥0 lies on this orbit. The input coordinate strictly increases, which proves uniqueness of the global recurrence rank.

A cutoff population is a finite prefix with two checked facts: every prefix point has x≤N, and the next point has x>N. Global descent and monotonicity then prove that the prefix contains every nonnegative solution up to N. The generator jumps directly between solutions rather than testing each integer. The zero-input point (0,1) has global rank zero. The points (2,3), (12,17), (70,99) and (408,577) have ranks one through four.

Query minima and local selections refer to this cutoff population. A separate global selection returns a recurrence point and proves that no other recurrence index gives that point. This release covers D=2 and the nonnegative quadrant; signed Pell populations, arbitrary nonsquare D and unrestricted optimization over an infinite set are separate tasks.

## Query semantics and executable interfaces

Both routes reuse QueryNative and the existing query compiler. Expressions may refer to original x and y, use integer addition, multiplication and bounded powers, and appear in equality, inequality, modular and Boolean conditions. Counts are checked list lengths with independently checked absence of duplicates. The query membership theorem is equivalent to the original equation, the declared domain or cutoff and the query condition. Rank/selection inverse theorems and objective lower bounds refer to this same original predicate. All minimizing ties are checked exactly.

The nonlinear API is nonlinear_population_certificate(coefficients, queries, family='mordell_minus2', domain='integer', work_limit=4096), paired with check_nonlinear_population. The family may also be mordell_minus4. The CLI is checked-nonlinear-population, with --coeff, --queries, --family, --domain, --work-limit and --check. The isolated HTTP operation is checked_nonlinear_population with keyword arguments under args.

The Pell API is pell_population_certificate(cutoff, queries, global_ranks=None), paired with check_pell_population. The CLI is checked-pell-population, with --cutoff, --queries, --global-ranks and --check. The isolated HTTP operation is checked_pell_population. HTTP requests emit proposals; explicit local checking performs acceptance.

Nonlinear polynomials have degree 1 through 32 and coefficients at most 128 bits. The fibre work budget is the total size of distinct derived input intervals multiplied by the coefficient count, at most 65536. The API refuses excessive work rather than truncating any fibre. A nonzero leading coefficient and nonconstant polynomial are mandatory: a constant map can have an infinite input fibre and cannot be passed off as a finite list. Expanded coefficients of U³−k are constructed exactly, and a Lean ring identity ties them to the original equation.

Pell cutoffs are nonnegative integers of at most 128 bits. There are at most 64 requested global ranks, each between zero and 128. The common batch permits at most 64 queries, with the established AST, expression-bit and point-operation budgets. Mathematical rank order for the finite nonlinear pullback is its declared source/fibre enumeration order; Pell ranks use increasing input order. Neither route claims formal refinement of the Python interpreter.

## Acceptance and retained evidence

Acceptance reconstructs the entire packet from the specification, including points, exact polynomial expansion, results, scope and emitted source. Any changed field rejects before invoking Lean. The checker rebuilds every project dependency from its packaged source in a private directory, audits source completeness and compiles the reconstructed query. Existing project object files do not replace these rebuilds. Receipts hash the specification, emitted source and each rebuilt source library.

Lean is pinned to 4.20.0. The checker permits only propext, Classical.choice and Quot.sound in printed dependencies; sorryAx and ofReduceBool reject. Fourteen source and bridge theorems are audited by audit/ExtendedPopulation.lean. Proposed packets retain proof_status=emitted. Accepted receipts use kernel_checked. execution_verified remains false because the formal result checks the reconstructed mathematical answers rather than proving the Python runtime correct.

Independent original-equation scans cover randomized nonlinear inputs and Pell cutoff boundaries. Regression tests cover repeated roots, empty fibres, signs, domains, expansion identities, objective ties, rank overflow, packet mutation and resource refusal. The installed wheel includes all new source modules and retained receipts and exercises both public emitters outside the source checkout. Actual kernel replay results are recorded in receipts/extended_population_queries.json. Eight accepted packets cover both Mordell sources, a repeated quartic fibre, the degree-32 boundary, an empty fibre, a positive domain, a Pell cutoff with local and global selections, and a cutoff of 10³⁰ with global rank 128. The legacy MordellMinus4 hit theorem also compiled after extraction.

## What this closes and what remains

The reusable population interface now reaches two globally complete finite Mordell sources through arbitrary nonconstant polynomial inputs, and one globally complete infinite Pell generator through exact cutoff queries and global selections. These are concrete extensions of the original affine-only route. The polynomial fibre bound is global but intentionally conservative; sharper divisor or root-isolation methods may reduce the checking cost.

The 457 externally computed Mordell census curves still require their outstanding Lean saturation and coordinate-bound obligations. General Baker/Matveev premises, general Sturm correctness, arbitrary number-ring representative completeness, signed or general-D Pell generation, Python execution refinement and unbounded optimization remain outside this release. This is a focused verification of the changed routes, not a new verification of every historical module or a claim that the entire flaw ledger is closed.
