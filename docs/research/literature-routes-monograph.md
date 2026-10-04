# From literature to checked arithmetic

## The value to an outsider

PerfectPower turns an equation with infinitely many possible integer inputs into a finite, inspectable answer, and proves that the answer leaves nothing out. An ordinary search can tell you that it found four solutions. This project can tell you why there cannot be a fifth, with that reasoning checked by Lean. The practical ambition is reusable machinery: a new equation should require a small arithmetic certificate rather than a new handwritten completeness proof.

This push adds one finished infinite-to-finite example and two reusable bridges toward harder cases. The finished example is an established mathematical benchmark, not a claim of a new solution to a previously open equation. The advance is its checked implementation and the reusable projection machinery. The harder bridges have explicit remaining hypotheses. Their presence does not mean that general rank-two Thue equations or general Mordell equations have been solved.

## A complete mixed equation

Consider

    y^4 + 2y^3 - 9x^2 y^2 + 2xy - 15x - 7 = 0.

Beukers and Tengely discuss this example in section 5 of “An implementation of Runge's method for Diophantine equations,” https://arxiv.org/html/math/0512418v1. Their work supplies a useful target for evaluating machinery on a genuinely mixed equation. Here the implementation uses an elementary quadratic projection followed by consecutive-square bounds rather than reproducing their full branch-expansion algorithm.

Treating the equation as quadratic in x gives coefficients a=-9y², b=2y-15, c=y⁴+2y³-7. Every solution satisfies

    (18y²x - 2y + 15)² = 36y⁶ + 72y⁵ - 248y² - 60y + 225.

This projection is proved algebraically. Let D be the polynomial on the right and P=6y³+6y²-3y+3. For y≥24, the proof places D strictly between (P-1)² and P². For y≤-26, it places D strictly between (-P-1)² and (-P)². In each tail, the smaller square has a nonnegative square root. An integer square cannot lie strictly between consecutive such squares.

The inequalities are certified through polynomial identities after setting t=y-24 or t=-y-26. The coefficient expansions are strictly positive for t≥0. This avoids a numerical approximation to a root and avoids assuming that a picture of the asymptotic branches captures every exceptional point.

Every solution consequently has -25≤y≤23: exactly 49 fibres. For each fibre the existing NativePolynomialRoots machinery enumerates all integer x roots, including the y=0 linear degeneration. The new MixedRunge.complete theorem proves equivalence between the original equation and membership in this finite set. A further kernel evaluation proves that the set is exactly

    {(-1,-4), (-1,-1), (-1,1), (-1,2)}.

The audit's mixed_explicit theorem states the answer directly: x=-1 and y is one of -4,-1,1,2. Both the global exclusion and the last enumeration are Lean proofs. No native_decide shortcut, trusted external search result, or extra arithmetic axiom enters these declarations.

The Python implementation reaches the same answer through exact integer square roots of discriminants and divisibility checks. It examines 49 fibres, not a rectangle in x and y. It can reconstruct a repeated root of size 10^40 immediately. Its result remains marked execution_verified=false: agreement with a proved mathematical specification does not itself establish a verified Python execution or a formal refinement theorem for the implementation.

## Quadratic projection as reusable machinery

QuadraticProjection.lean proves the identity

    (2ax+b)² - (b²-4ac) = 4a(ax²+bx+c).

For a≠0, an integer root exists exactly when there is an integer w with w²=b²-4ac and 2a dividing w-b. The divisibility condition matters: a square discriminant alone does not guarantee an integer root. The module proves both directions. It is a small general tool for other mixed equations quadratic in one variable, and is independent of the particular degree-six discriminant above.

The current generic theorem excludes a=0 explicitly. The Python helper separately handles linear fibres, inconsistent constant fibres, and the zero polynomial, whose integer-root set is infinite. The mixed example's Lean coefficient selection also handles the linear fibre separately. Nothing is inferred by dividing by a quantity that could vanish.

## Two signed unit exponents

The difficult rank-two norm problems involve expressions of the form A^e B^f, with e and f arbitrary integers, acting on a norm representative. The existing Python orbit machinery computes finite modular periods and allowed exponent residues. This push proves the mathematical principle underlying that reduction for both exponents, including negative ones.

For group elements A and B with certified positive periods M and N, respectively,

    A^e B^f = A^(e mod M) B^(f mod N).

RankTwoSieve.signed_residue_iff gives an exact equivalence between any predicate on that group product and membership in a finite allowed-residue set. It does not need A and B to commute. A receiver can multiply the product by a nonunit norm representative and inspect any chosen coordinate; the representative itself need not be inverted. An additional theorem permits independent necessary conditions to be intersected without losing a genuine solution.

The regression tests use the cubic order z³=9z+6, units (-1,-3,1) and (-1,0,2), their exact inverses (-1,-3,-1) and (-289,-24,34), and norm representative (-3,-3,1). They certify the inverse multiplication identities and compare residues against independently evaluated signed powers over 625 exponent pairs for each of five moduli. They also reject a deliberately truncated period calculation. These are implementation tests, not a Lean certificate of each concrete period table.

For moduli 3,6,9,15,21 the period pairs are (6,6),(6,6),(18,18),(186,186),(48,48). The allowed counts are 36/36,18/36,108/324,6696/34596,288/2304. The condition is that the middle coordinate vanish modulo the modulus and the first coordinate be divisible by 3. In particular, modulus 3 eliminates nothing here. These figures describe periodic local filters; they do not bound e or f.

The rank-two Matveev lower-bound premise remains unresolved. Tzanakis and de Weger, “On the practical solution of the Thue equation,” https://math.deweger.net/papers/%5B6%5DTzdW-Thue-JNumTh%5B1989%5D.pdf, explains the classical architecture of an initial logarithmic bound followed by lattice reduction. A finite residue sieve is useful downstream, but cannot replace the theorem that makes the exponent domain finite. The present work strengthens that downstream component and keeps the upstream premise visible.

## An independent cubic-to-Mordell bridge

For F=au³+bu²v+cuv²+dv³, define the standard discriminant

    Δ=b²c²-4ac³-4b³d-27a²d²+18abcd,

H=(b²-3ac)u²+(bc-9ad)uv+(c²-3bd)v², and G=F_u H_v-F_v H_u. CubicCovariants.syzygy proves the universal identity

    4H³-G²=27ΔF².

There is no factor of 1/3 in this definition of G. Consequently F=m maps to the integral Mordell point X=4H, Y=4G satisfying

    Y²=X³-432Δm².

The discriminant convention is written out to prevent a sign mismatch when comparing with references that choose the opposite convention. The proof is a polynomial identity, independent of logarithmic lower bounds or unit generation.

The module also proves a lower bound for a reduced positive quadratic form: if 1≤A, |B|≤A≤C, then u²+v²≤2(Au²+Buv+Cv²). Applied to a reduced Hessian, an explicitly supplied upper bound X≤L for all relevant Mordell points bounds both source coordinates. complete_of_mordell_bound turns this into a complete finite Thue enumeration. The coordinate bound is deliberately coarse; correctness precedes optimization.

The reduced-Hessian assumptions are genuine. The audit demonstrates that the unreduced Hessian for (-1,0,9,6) fails one of them. To use this bridge for that source, one must supply and verify a change of variables reducing the quadratic form, or prove a different positive-definite bound. Likewise, the Mordell bound remains an input; this module does not prove modularity, compute a Mordell-Weil basis, or certify a general integral-point height theorem.

Von Känel and Matschke, “Solving S-unit, Mordell, Thue, Thue-Mahler and generalized Ramanujan-Nagell equations via the Shimura-Taniyama conjecture,” https://arxiv.org/pdf/1605.06079, supplies the relevant independent literature route. Its effective global arithmetic is precisely the part that cannot be replaced by the elementary syzygy alone. This push establishes a checked entry point for such results, with a concrete finite-search conclusion once their hypotheses and bound have been certified.

A further theorem proves sixth-power normalization over the rationals: from Y²=X³+s⁶k, s≠0, it follows that (Y/s³)²=(X/s²)³+k. This does not preserve integrality automatically. The normalized point may require denominators involving s. Any future census or solver that identifies two normalized equations must preserve those denominator conditions, or work with the appropriate S-integral point problem. Counting the same rational curve does not justify treating its integral-point problems as identical.

## Verification and next arithmetic obligations

scripts/check_literature_routes.sh compiles the four new Lean modules, checks the two audit files, validates fourteen theorem axiom reports against the standard permitted set, and runs the nine targeted Python tests. The mixed finite set is evaluated by the Lean kernel. Audit reports reject any extra axiom, including sorryAx. Existing historical modules are not represented as freshly rebuilt by these targeted checks.

The most substantial finished result is the complete mixed equation. The useful general additions are integer quadratic projection, the universal cubic covariant identity, a conditional finite Thue reconstruction, rational sixth-power transport, and exact two-exponent modular reduction. The next substantial arithmetic milestone is to discharge a global bound for a concrete rank-two source, or independently certify the necessary Mordell point bound and reconstruct its Thue fibres. The current interfaces expose those obligations rather than hiding them inside an apparently complete solver.
