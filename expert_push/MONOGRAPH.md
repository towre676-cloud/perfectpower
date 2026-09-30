# Effective Arithmetic Beyond the First Orbit

This companion turns the five requested targets into executable reductions and precise proof obligations. It does not replace the existing reader. Baseline statements about 404 declarations, 13 proved OEIS entries, 23 unproved candidates, 155 unresolved curves and 98 published nonempty leads are supplied-report facts, not independently reproduced results.

## Effective enumeration outside the certified cases

A proof of finiteness does not necessarily provide an effective upper bound. For y²=x³+k with k≠0, a useful missing premise is a proved integer U such that all integral solutions have x≤U. The lower bound is elementary: x³≥−k, so L=ceil(cuberoot(−k)). Given U, put M=U³+k. If M<0 no solutions exist; otherwise |y|≤floor(sqrt(M)). Exhaustively checking this rectangle then proves completeness. The Lean draft states the general bound-to-enumeration bridge with an explicit rectangle-bound hypothesis. It does not manufacture that hypothesis from observed search exhaustion.

The Python kernel scans every allowed x from the exact lower bound through the upper bound inclusive, uses integer square roots, records both signs and counts y=0 once. Square-residue filters modulo 16,27,5,7,13 reduce work without rejecting actual solutions. Tests independently compare to unsieved scans. The full receipt covers every nonzero signed k with |k|≤100 through x=100000, not just the unseen 155 unresolved cases. Point membership is exact; completeness beyond that interval remains open.

A practical effective route is a complete Mordell-Weil basis, saturation, explicit elliptic-logarithm bounds, lattice reduction and a final exhaustive region. Rank≥2 expands the dimension and cost, rather than invalidating the method. A rank match and independent points do not prove index one. The Sage adapter uses the original integral model, both signs and proof settings, but it is unexecuted here and emits external algorithm evidence. Formal replay must expose full group generation, saturation, numerical error bounds and residual exhaustion. If using a minimal model, transport integrality back exactly; integral points are model dependent.

## Class-group and unit branches in descent

For k=−D factor y²+D=x³ in an appropriate quadratic order. The factors can share primes above 2D and the conductor. A coprime factorization may yield (alpha)=a³; then [a] is in class-group 3-torsion. If this torsion vanishes a is principal. Otherwise enumerate the relevant torsion classes and ideal representatives, obtain a³=(gamma), and derive gamma-twisted cube equations. Exceptional valuations, denominators and integral back-mapping remain mandatory parts of the branch theorem.

The kernel enumerates primitive positive definite reduced binary forms of discriminant −4D, giving the class number of that quadratic order. It does not implement form composition, ideal arithmetic or explicit torsion generators. Divisibility of the class number by 3 detects nontrivial 3-torsion via Cauchy's theorem, but does not enumerate the needed branches. Maximal-order discriminants may differ from −4D. Nonmaximal orders need conductor and invertibility conditions; order class numbers cannot be swapped into maximal-order arguments without justification.

For finite cyclic units of order w, the cube quotient has gcd(w,3) classes. Gaussian units have w=4, so every unit is a cube: i=(-i)³. Therefore a noncube Gaussian unit cannot be the obstruction in y²=x³−1. Inspect the existing certificate before assigning the true cause. Maximal Eisenstein units have order 6, giving three cube classes. In real quadratic orders the free rank-one unit component gives a mod-3 exponent branch, with torsion handled separately. Positive k requires this real arithmetic or another descent route. Square k, singular curves and reducible factorizations need distinct dispatch.

The expansion (a+b√−D)³=(a³−3Dab²)+(3a²b−Db³)√−D gives binary cubic coefficient equations. Twists by gamma and units change those equations. A complete branch compiler proves that every original solution reaches a branch, then proves that branch outputs map back integrally. Solving the resulting Thue equations still needs an effective bound or a complete external solver certificate. A finite list of twists alone does not enumerate their solutions.

## A concrete quartic bridge

For v²=a u⁴+b u²+c, a≠0, define X=a u² and Y=a u v. Algebra gives Y²=X³+bX²+acX. This is a degree-two map, not a general birational equivalence. Nondegeneracy requires a c≠0 and b²−4ac≠0. The source equation can have no rational point; the map still exists, but the target Jacobian information alone does not solve that torsor problem.

For an integral cubic point with X≠0, lifting requires X/a to be a nonnegative integer square. For each integer u with u²=X/a require a u to divide Y, set v=Y/(a u) and verify the quartic. For X=0, u=0 and v²=c; handle this fibre separately even though both signs map to the same cubic point. The implementation tests these conditions for positive and negative a and exceptional zero fibres. A complete integral enumeration of the target cubic implies a complete integral enumeration of the quartic through this lift filter, because every source integral point maps to an integral target point.

General quartics with odd coefficients need their own model transformation, exceptional points, denominators and rational-base-point or torsor treatment. An unsuccessful base-point search proves nothing about absence. Rank≥2 work should first establish a complete basis and explicit coefficient region; a coefficient box around chosen generators is only a search until generation and the bound are proved.

## Reusable definitions for the remaining sqrt(2) entries

The orbit recurrence is A(n+1)=A(n)+2B(n), B(n+1)=A(n)+B(n), so each coordinate satisfies z(n+2)=2z(n+1)+z(n). Its ordinary generating function is (z0+(z1−2z0)t)/(1−2t−t²). Prove this coefficientwise in formal power series, using uniqueness of division by a series with invertible constant coefficient. No convergence assumption is needed. A recurrence equality follows from equal initial values and induction. The exact rational-series kernel demonstrates B's coefficients for numerator t and denominator 1−2t−t².

For sqrt(2)=[1;2,2,...], the convergent indexed j from zero has numerator A(j+1) and denominator B(j+1). Continuants start p(-2)=0,p(-1)=1,q(-2)=1,q(-1)=0, followed by coefficient 1 then repeated 2. Reducedness follows from the norm identity: a common divisor of A and B divides 1. Equality with convergents does not automatically prove best-approximation properties; formalize those if the source definition requires them. The exact receipt checks the coordinate correspondence for 100 convergents.

Euclid's triples are (m²−n²,2mn,m²+n²). The engine tests the identity; primitive completeness remains a formal theorem requiring coprimality, opposite parity, ordering and leg-swapping conventions. For consecutive legs, m²−n²−2mn=±1 becomes (m−n)²−2n²=±1. This is a direct Pell bridge. Conversely, prove that recovered m,n satisfy the Euclid conditions and that observations have correct offsets and no collisions. Source definitions decide the exact domains. The absent 23-entry ledger is deliberately not reconstructed from guesses.

## A Bilu–Tichy counting sequel

Bilu–Tichy classifies polynomial equations f(x)=g(y) with infinitely many rational solutions sharing a bounded denominator through common compositions and standard pairs with the required infinitude condition. It does not automatically provide effective bounds in finite cases or counting constants. Retrieve the original theorem and all hypotheses before implementing a complete classifier. The original PDF body could not be opened here; full standard-pair classification is not implemented.

For positive solutions x^a=y^b put d=gcd(a,b), a'=a/d,b'=b/d. Unique factorization implies x=t^b', y=t^a'. In the positive box x,y≤N the exact count is floor(N^(1/max(a',b'))). Root extraction must be integer-exact. The engine implements the parameterization and compares to exhaustive boxes for exponents 1 through 5. Signed domains add parity branches and zero requires its own convention. This is a tractable first formal sequel with exact counts, distinct from the harder general classification.

For an exponential observation z_n, effective bounds c_minus lambda^(d n)≤z_n≤c_plus lambda^(d n) and accepted residues R modulo p give |R|/(p d log(lambda)) log N+O(1), after finite exceptions and appropriate monotonicity/distinctness conditions. Explicit constants give explicit cutoffs. The exact number of accepted indices in [L,U] is sum over r in R of floor((U−r)/p)−floor((L−1−r)/p). The tested kernel supports negative cutoffs and repeated residues. Counts of distinct values require collision control; multiple seed orbits require intersection handling.

A common outer polynomial cannot generally be cancelled. For phi(t)=t², phi(F)=phi(G) has branches F=G and F=−G. Factor phi(U)−phi(V) and account for all arithmetic components. Separate arithmetic-power growth, Pell exponential growth, effective finite cases and ineffective finite cases. Genus information and infinitude classification should never silently become an explicit count formula.

## Concrete integration priorities

First compile the finite bound bridge, correct the Gaussian-unit diagnosis and prove the quartic lifting theorem. Then formalize formal-series and convergent equivalences and instantiate the actual entries. Consume the real obstruction ledger and prioritize repairs by cases unlocked. Sage evidence sits between leads and formal completeness. This package asserts no newly closed unresolved Mordell case and no new compiled Lean declarations.

## Sources

SageMath official reference, inspected 2026-09-30: https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/ell_rational_field.html . The integral_points documentation specifies the full-basis requirement and both_signs option. The supplied adapter was not executed.

Bilu and Tichy, The Diophantine equation f(x)=g(y), Acta Arithmetica 95 (2000): https://matwbn.icm.edu.pl/ksiazki/aa/aa95/aa9534.pdf . Search metadata retrieved; body unavailable here. Consult the original before encoding the full classification.
