# A broad checked family engine: square differences, general Pell access and Mordell descent

Version 0.8.0 broadens the original-equation interface in three directions. A single factor-pair construction solves y²=U(x)²+k globally for every declared nonconstant integer polynomial U and nonzero k that fits the work budget. Divisor-based polynomial fibres connect five classical Mordell sources and a 1,026-offset descent atlas to the same query interface. General Pell generation supplies signed cutoff populations, count-only certificates, fast global selections, attained minima for nonnegative polynomial objectives and a proof of unboundedness for −x.

These are mathematical source completeness results with reconstructed kernel checks. They do not establish formal refinement of the Python interpreter, close the hard 457-curve rank and saturation census, or supply general Baker/Matveev or Sturm theorems.

## From a square difference to a complete finite population

Write s=U(x). The equation y²=s²+k is equivalent to (y−s)(y+s)=k. For k≠0 there are finitely many signed factor pairs (u,v) of k. Recover s=(v−u)/2 and y=(v+u)/2, requiring integrality. The source generator enumerates all signed factor pairs and filters the recovered values through the original square equation. DivisorPopulation.values_complete proves both directions. The explicit filter handles parity without assuming that truncated integer division recovers an admissible pair.

Each source value s is then pulled back through the exact integer fibre U(x)=s. The resulting theorem includes every original integer input and both ordinate signs. It contains no search interval or unproved height premise. Query restrictions become predicates on original x and y. Counts are checked lengths with absence of duplicates; local ranks invert selection; bivariate objective bounds and exact minimizing tie lists refer to the same original equation.

The new API is family_population_certificate(coefficients, queries, family='square_plus_constant', offset=1, domain='integer', work_limit=4096), with check_family_population for acceptance. Coefficients are ascending. The domain may be integer, nonnegative or positive and restricts the original input coordinate. The CLI checked-family-population provides --coeff, --queries, --family, --offset, --domain, --work-limit and --check. The HTTP operation checked_family_population uses these keyword arguments under args and emits a proposal in the existing isolated worker.

The finite interface requires positive polynomial degree and k≠0. When k=0, y=±U(x) describes an infinite family, so a finite source count would be inappropriate. Constant U likewise needs an infinite-input interface when its ordinate equation has solutions. Both cases are explicitly refused rather than truncated.

## Exact fibres without a coefficient-height scan

IntegerPolynomialFibres proves the integer-root divisibility method directly for the established Horner semantics. A root of a+x·V(x) divides a. For a nonzero constant coefficient, every possible integer root therefore appears in the proved signed-divisor set. Exact evaluation filters candidates. For a zero constant coefficient, the generator inserts zero and recurses on V; finite sets remove repeated roots. A nonzero constant polynomial has no roots. A linear polynomial a+bx is solved directly by checking b divides −a and recovering x=−a/b.

The fibre U(x)=s subtracts s from the constant coefficient and applies this complete root generator. Its theorem is globally equivalent to the original fibre equation. The pullback theorem applies to any finite source whose membership already has a complete predicate equivalence. A literal list is accepted only after the kernel checks equality with the complete computed finite set.

This improves the previous conservative coefficient-height route without changing its old packets. For U(x)=3+10³⁰x, the minus-two source fibre U(x)=3 recovers x=0 by one linear divisibility operation. For U(x)=3+10³⁰x³, zero stripping again recovers only x=0. Neither example scans an interval proportional to 10³⁰. A nonzero shifted constant in higher degree still uses square-root trial division and can exceed the work budget; arbitrary large factorization and a general real-root isolation theorem are not claimed.

FastDivisors retains its equality proofs against Mathlib's divisor and divisor-antidiagonal sets. Its imports are narrowed to the mathematical and tactic dependencies used by its proof. The new algorithms use this source rather than an unchecked factorization oracle.

## More proved Mordell sources

The finite interface accepts mordell_minus2, mordell_minus4, mordell_minus5, mordell_minus6 and mordell_minus13. Their complete source populations are respectively (3,±5); (2,±2) and (5,±11); empty; empty; and (17,±70). These conclusions hold over all integer coordinates.

ClassTwoCore contains the existing arithmetic class-number-two template without importing the unrelated analytic definitions. MordellMinus5Core, MordellMinus6Core and MordellMinus13Core retain the source proofs. The original modules remain wrappers with their original perfect-power hit theorems and namespaces. AdditionalMordellPopulations gives the list-membership equivalences needed by the common query engine. No rank or integral list from the computational registry substitutes for these proofs.

For U(x)=x²+16, the minus-thirteen population has x=±1 and y=±70. Empty source curves remain empty under every admitted nonlinear input polynomial. These sources broaden the globally complete route while retaining the original input domains and exact polynomial expansion identities.

## A reusable descent atlas with 1,026 empty source curves

The existing MordellDescent argument is now available as a small arithmetic core. It handles offsets k=c³−Db² with D equal to 1, 2 or −2. A prime-divisor certificate for b and a finite congruence certificate force any putative solution to produce a prime simultaneously in an allowed and forbidden residue class. Thus y²=x³+k has no integer solutions.

The producer searches integer parameter choices and emits a certificate containing D,c,b,M,j,b1,u. The factor certificate is b=2^j·b1 together with b1 dividing u²+D. The congruence proof checks a complete square-residue mask once for each admitted modulus, then checks the required parity and forbidden prime-residue condition for each possible input residue. A generic mask theorem recovers the original all-pairs congruence statement. Reusing the square masks avoids a repeated two-dimensional residue scan. The producer is not trusted: each instantiated theorem applies the general descent proof with kernel-checked arithmetic and congruence premises.

The retained atlas contains 1,026 distinct nonzero offsets in the interval −10000 through 10000. Its global emptiness theorems are compiled in 33 blocks of at most 32 declarations, keeping elaboration memory bounded. The atlas entry point exposes the general source theorem; the block files contain the individually audited declarations. The kernel audit records each declaration, allowed axiom dependencies and source hashes. The stored 20,000-curve census provides an independent comparison, and every corresponding stored integral x-list is empty.

Select this route with family='mordell_descent' and an offset from data/mordell_descent_sources.json. Each query acceptance rebuilds MordellDescentCore and checks that selected offset's certificate. It does not compile all 1,026 instantiated proofs for every request. Nonlinear pullbacks of any admitted empty source are globally empty.

The intersection with the hard 457-curve completion set is empty. Therefore this atlas establishes many global integral emptiness results but does not reduce those 457 rank, saturation or coordinate-bound obligations. Integral emptiness also does not imply the absence of rational points or a particular rational Mordell–Weil rank. These claims remain separate in the ledger.

## General Pell generation from a checked fundamental seed

The public Pell equation is y²=D·x²+1. The nonnegative orbit starts at (0,1). If (B,A) is a fundamental solution, multiplication by A+B√D sends (x,y) to (Ax+By, DBx+Ay). Mathlib's Pell theory proves that every nonnegative solution is a nonnegative power of this seed and that its input coordinate strictly increases. PellFamily connects those results to the original coordinate order used by the query language.

A continued-fraction producer proposes A and B. Acceptance does not trust its steps or a flag saying fundamental. It checks A²−DB²=1, A>1 and B>0. For every integer input n between one and B−1, the packet supplies q=floor(sqrt(Dn²+1)) and checks q²<Dn²+1<(q+1)². The adjacent-square theorem excludes every integer square root, including negative roots. A comparison of norms proves that any positive-root solution smaller than A would have absolute input smaller than B, contradicting those certificates. This establishes the required fundamental-seed proposition.

The mathematical bridge is general in D. The executable interface admits positive nonsquare D between 2 and 1,000,000, subject to seed_budget. The budget counts the finite minimality certificate and may be at most 65,536, with default 4,096. Some D, including 61 at the default budget, have a much larger fundamental input and are refused. This is a resource limit, not a counterexample to Pell generation. A compact formally proved continued-fraction minimality theorem would remove that particular bottleneck; it remains future work.

## Binary powering and exact count-only access

PellFamily.fastPower squares a half-exponent result and multiplies by the seed for odd exponents. A fuel theorem proves equality with the mathematical seed power whenever k<2^fuel. Thus every selected coordinate is checked through logarithmically many multiplications. The global rank theorem proves that no other nonnegative recurrence index gives the selected point.

The producer finds the first rank L whose input exceeds a cutoff N by exponential bracketing followed by binary search. The kernel checks just the last included input, x_(L−1)≤N, and the next input, N<x_L. Strict monotonicity proves x_k≤N if and only if k<L. A finite-set image theorem establishes that the complete nonnegative cutoff population has exactly L elements.

When queries are absent, the API returns this count and any requested global selections without materializing source_points. The count theorem still covers every solution, using generation and injectivity. With queries supplied, the exact prefix feeds the shared finite query interface. Count-only results have source_points=null, and global ranks always index the nonnegative orbit independently of a cutoff.

The accepted large example uses D=2, cutoff 10³⁰ and global rank 1,000. The cutoff has 40 nonnegative solutions. The selected rank is outside that cutoff and has more than 2,000 bits in its input; its proof uses binary powering. This demonstrates exact access rather than a benchmark claim about an external workload.

The public function is pell_family_certificate(D, cutoff, queries=None, domain='nonnegative', global_ranks=None, global_objective=None, seed_budget=4096), paired with check_pell_family. The CLI checked-pell-family supplies --D, --cutoff, --queries, --domain, --global-ranks, --global-objective, --seed-budget and --check. The HTTP operation is checked_pell_family. Cutoffs have at most 128 bits. At most 64 global ranks in 0..1,000,000 are admitted, and resulting coordinates must fit 4,096 bits.

## All sign branches and domain meaning

The integer domain includes all solutions with |x|≤N and either ordinate sign. Each nonzero nonnegative orbit point yields four sign variants. The zero-input point yields only (0,1) and (0,−1), avoiding duplicate zero branches. The signed completeness theorem recovers any original solution through its absolute coordinates and proves membership in the corresponding sign variants.

For the Pell API, nonnegative means both coordinates are nonnegative. Positive means both are positive, excluding the seed identity point. Integer means both coordinates may have either sign. This differs from the finite-family input domain, which restricts only original x. Packet predicates and the documentation make that distinction explicit. Signed cutoff queries can use the established Boolean, congruence and bivariate polynomial conditions and objectives.

## Optimization without a cutoff

Nonnegative polynomial expressions in x and y are monotone on the nonnegative quadrant. Every nonnegative Pell solution has x≥0 and y≥1, so any admitted expression has value at least its value at (0,1). The global minimum theorem covers every nonnegative solution, without a cutoff. The packet checks the attaining witness and its original equation. Constants, addition, multiplication and nonnegative integer powers are supported, with nonnegative integer constants throughout the expression.

The interface deliberately distinguishes this global minimum from cutoff minima. A constant objective, or one that is identically constant after multiplication by zero, can have infinitely many tied minimizers. The global result reports an attained value and witness and describes ties through the original equation and objective equality; it does not claim a finite exhaustive tie list. Finite cutoff and finite source queries retain their exact all-ties lists.

The objective −x is proved unbounded below. The input grows at least as fast as its natural rank, so for every integer bound there is a nonnegative Pell solution with −x below that bound. The API reports unbounded_below, not a sampled minimum. Other objectives with negative coefficients are refused by the unbounded-domain interface unless they are this supported expression. General infinite-family optimization remains unfinished.

## Acceptance, evidence and reproducibility

Every checker reconstructs the full packet, rejects changes before execution, and privately rebuilds every project source dependency used by the selected route. The external pinned Mathlib is part of the formal environment; previously built project objects do not replace private rebuilds. Source and specification hashes bind receipts to the checked mathematics. Printed axiom dependencies must be confined to propext, Classical.choice and Quot.sound. Emitted packets remain proposals until accepted by Lean 4.20.0. execution_verified remains false because the Python runtime itself has not been formally refined.

The source gate audits 25 new family theorems. The descent gate compiles and audits all 1,026 instantiated declarations in bounded-memory blocks. Replayed packets cover positive and negative square offsets, large linear coefficients, zero stripping with a large leading coefficient, the minus-thirteen source, empty classical and descent sources, signed D=3 queries, a D=13 global minimum, the large D=2 count and rank example, and D=7 unboundedness. Independent original-equation scans cover randomized square-difference equations and a range of nonsquare Pell parameters. Mutation and resource-limit checks accompany those mathematical comparisons.

The installed wheel includes the new sources, descent atlas data and accepted receipts. Its checks run outside the source checkout and exercise both new HTTP operations. The old nonlinear and Pell interfaces remain available with their prior packet formats. Focused legacy module builds and query regressions check that source extraction preserves the established theorems.

Run scripts/check_family_population.sh for the source and packet gate, scripts/check_mordell_descent_atlas.sh for the full descent atlas, and python/record_family_population.py under the pinned Lean environment to regenerate packet acceptance receipts. The complete release archives contain every tracked repository file and the checked wheel; extracting all parts into one directory reconstructs the release.

## Remaining mathematical work

The next efficiency improvements are compact certified fundamental seeds for very large Pell units and complete factorization certificates that avoid square-root trial division for large polynomial constants. General Sturm correctness and certified real-root isolation are not supplied by the divisor method. The 457 hard Mordell completion curves still require their rational rank, saturation and global integral bounds. General number-ring representative completeness, Baker/Matveev bounds, arbitrary infinite objectives, certified general surface geometry and Python execution refinement remain open. This release advances the proposed family, access and optimization fronts substantially while retaining those exact distinctions.
