# Literature into executable curve structure

## What this release adds

PerfectPower now connects actual algebraic curve maps, formal differential lifting, integral marked cycles, superelliptic cohomology, rational constant terms, rigorous ordinary continuation and prime-field Frobenius computations. Each connection has an executable example and a receipt containing its precise scope. The value is the ability to ask several different mathematical questions of the same polynomial and replay the identities connecting the answers. These constructions draw on established mathematics; this release does not establish worldwide novelty or solve general Jacobian decomposition.

All eleven literature directions have concrete implementations. The implementation contains no optional runtime dependencies. Three additional persistent object kinds bring the catalogue to eighteen kinds: differential_module, superelliptic_family and binomial_sum. Fourteen standalone research operations supplement their methods. Rebuild the twenty-two example receipts with python python/literature_curve_corpus.py. The full corpus is in docs/literature_receipts, and the combined tests are in python/tests/test_literature_curve_execution.py.

The existing several-parameter flat connections, full projective deformation quotient, algebraic local charts and finite-action quotient compiler remain available. This release builds on those objects; it does not equate them with numerical mesh Hodge matrices or finite graph models.

## Every literature direction and its delivered object

| Direction and primary literature | Executable capacity | Direct research use and exact boundary |
|---|---|---|
| Milne, Fields and Galois Theory; matrix Hilbert 90 | involution_descent constructs a full invariant rational frame for a declared semilinear parameter involution and descends its differential connection to u=t² | Re-express a system over a smaller coefficient field while retaining the connection and chain rule. The cocycle and horizontal compatibility must hold; arbitrary Galois descent discovery is not supplied. |
| Kani–Rosen quotient decompositions and their generalizations | genus_three_elliptic_tower composes actual genus-three to genus-two to elliptic covers, with complete differential pullbacks | Replace one rank-six period system with three rank-two systems over a recorded quartic base change. This is an actual degree-32 Jacobian isogeny in this family, not a factorization inferred from a projector. |
| Costa, Mascot, Sijsling and Voight, formal endomorphism certification | elliptic_two_isogeny integrates formal logarithms, inverts the target logarithm, reconstructs rational functions from jets and verifies the resulting map | Turns a normalized tangent map between specified elliptic models into an exact rational map. The whole smooth rational 2-torsion class is supported; higher-genus correspondence reconstruction remains open. |
| Richelot correspondences and explicit isogeny kernels | richelot_correspondence constructs a genus-two target, a two-variable correspondence and explicit Weierstrass divisor kernel; reflection_kernel constructs marked torus kernel generators in an actual real cover family | Study genuine degree-four isogenies and their kernels in two complementary coordinate descriptions. Singular Richelot splittings require a separate product construction; general integral cycle maps of arbitrary correspondences are not supplied. |
| Griffiths–Dwork reduction and Lairez's period algorithms | SuperellipticFamily reduces poles on y^d=f and retains exact primitives, character blocks, holomorphic basis indices and a Gauss–Manin connection | Derive polynomial period equations beyond hyperelliptic curves, including a trigonal genus-three example. Degrees are coprime, the model is monic and smooth generically, and the state dimension is at most 32; general hypersurfaces are not claimed. |
| Bostan, Lairez and Salvy, multiple binomial sums | BinomialSum compiles a bounded affine-binomial class into a rational constant term; three named families have exact telescoping certificates | Connect sequence execution to periods through a proved rational representation. The Apéry zeta(2) sum is checked against an independently derived elliptic curve operator. A general multivariate creative telescoper is not supplied. |
| Sertöz and Mezzarobba, marked periods and rigorous ODE execution | certified_transport provides rational complex matrix centers and proved error bounds; marked_legendre adds certified integral-cycle seeds | Execute an exact period equation with analytic enclosures along a certified ordinary polygon. Pole disks and propagation errors are explicit. Singular-endpoint numerical execution and automatic integer recognition are not claimed. |
| Dokchitser, Dokchitser, Maistret and Morgan, hyperelliptic clusters | root_clusters constructs exact split-root cluster trees and geometric semistable double-cover graphs; simultaneous_nodes resolves several transverse quadratic collisions | Read component genera and graph cycles directly from root distances, or resolve a multi-node family after t=r². Odd residue characteristic and rational split roots are required; component twists, Frobenius on components and minimal regular models remain separate. |
| Kedlaya and Tuitman, p-adic cohomology and precision | frobenius computes a genuine cohomological Frobenius matrix using exact pole reduction and a proved binomial-tail precision bound | Study good prime-field fibres with an actual arithmetic operator. Exact enumeration independently checks its Weil polynomial. Supported odd degrees are 3,5,7, with degree<p<=19 and precision at most four; this is not an optimized arbitrary-field backend. |
| Lauder, deformation of Frobenius | frobenius_deformation transports a certified base Frobenius into formal parameter jets, with factorial precision loss; tower_frobenius transports three smaller arithmetic blocks through actual covers | Reuse structural decomposition and differential motion in arithmetic computation. The rank-six tower result is checked against independent genus-three counts. General p-adic continuation across parameter boundaries is not claimed. |
| Differential Galois/Tannakian methods and Lairez–Vanhove Feynman periods | DifferentialModule builds tensors, duals, Hom, symmetric and exterior powers, bounded horizontal sections and filtered polarized endomorphisms; sunrise derives an exact relative telescope and augmented amplitude system | Search representations for structural invariants, then distinguish absolute periods from a boundary-driven relative integral. No full differential Galois group or general Feynman integral solver is inferred. |

The last row joins two applications of differential algebra, but both have separate algorithms and examples. The taxonomy is an organizational choice, not a theorem that their structures are identical.

## A genus-three family with three actual elliptic factors

Start from the entire family

$$
C_t:\quad y^2=x^7+t x^5+t x^3+x.
$$

Its smooth locus excludes t=-1 and t=3. The first reciprocal cover uses u=x+1/x. Its two sheet lifts produce the elliptic curve E0 and the genus-two curve D:

$$
E_0:\quad v^2=u^3+(t-3)u,\qquad v=y/x^2.
$$

$$
D:\quad w^2=u^5+(t-7)u^3-4(t-3)u,\qquad w=y(x^2-1)/x^3.
$$

Adjoin delta with delta^4=-4(t-3), and use the rationalized parameter t=3-delta^4/4. The second involution sends u to delta²/u and w to delta³w/u³. Its two lifts give

$$
z=u+\delta^2/u,\qquad r_\pm=w(u\pm\delta)/u^2.
$$

$$
E_\pm:\quad r_\pm^2=(z\pm2\delta)(z^2+t-7-2\delta^2).
$$

The code verifies both stages of the defining polynomial identities independently. It reduces differential pullbacks at each stage, retains their exact primitives and composes the matrices. This staged calculation avoids unnecessary rational-expression growth in a direct fourfold map reduction. The complete pullback has rank six, and the three holomorphic pullback rows have rank three.

If A is the source connection, B a target connection and T its differential pullback, each stage and each composite satisfy

$$
T'+T A=B T.
$$

The first pair of actual degree-two covers induces a Jacobian isogeny of degree 2³=8. The paired covers of D induce one of degree 2²=4. Their composition therefore has degree 32 and kernel annihilated by four. The composed curve-map degrees are two, four and four. These statements are over Q(delta), and do not assert a direct elliptic product over Q(t). Explicit generators of this composite kernel are not calculated here.

At delta=1 and p=7 the program computes the three elliptic Frobenius matrices to precision 7², combines them through the invertible differential pullback and checks the result against independent enumeration over F7, F49 and F343. The common characteristic polynomial is

$$
X^6+5X^4+35X^2+343.
$$

This is a concrete fusion of geometric decomposition, differential reduction and arithmetic execution: a six-dimensional arithmetic matrix is assembled from three two-dimensional computations using maps already proved on the curve.

## Matrix descent, rather than only scalar descent

Let sigma(t)=-t. A supplied rational matrix S must satisfy the cocycle S(-t)S(t)=I and the connection intertwining equation between A(t) and -A(-t). The compiler forms invariant rows from I+S and t(I-S), selects a full independent frame H, and checks H(-t)S(t)=H(t).

The gauge-transformed connection C=(H'+H A)H^-1 is odd in t. Its quotient C/(2t) is even, so it can be expressed rationally in u=t². That division is the coordinate Jacobian required for the descended equation. It is not sufficient to make the entries invariant without changing the differential variable.

For A with rows (0,1) and (t²,0), the cocycle diag(1,-1) gives an invariant frame with one factor of t. The descended connection has rows (0,1/(2u)) and (u/2,1/(2u)). The receipt includes the full frame, cocycle check and intertwining check. The singularity of the descended frame is visible at u=0.

## Formal differential lifting to a rational isogeny

For E:y²=x³+a x²+b x, assume b(a²-4b) is nonzero. The target is E':v²=u³-2a u²+(a²-4b)u. The source has rational 2-torsion (0,0). Use the infinity parameter z=-x/y and write X=z²x. The defining equation becomes

$$
X^2+(a z^2-1)X+b z^4=0,\qquad X(0)=1.
$$

Its coefficients are determined recursively over Q. From dx/(2y), construct the source and target formal logarithms. A normalized tangent multiplier one gives the formal equation log_E'(w)=log_E(z). Since both logarithms have linear coefficient one, formal inversion determines w coefficient by coefficient.

The program then reconstructs u(x) and v(x)/y from those jets by rational-function ansätze of bidegrees (2,1) and (2,2). It demands a one-dimensional reconstruction kernel. Finally it verifies the target equation and the differential identity exactly, on the whole source function field. For every supported input it recovers

$$
u=x+a+b/x,\qquad v=y(1-b/x^2),\qquad du/v=dx/y.
$$

The map is therefore more than a finite formal approximation: the verified rational functions define the actual degree-two isogeny, with kernel generated by (0,0). The algorithm is specialized to this entire 2-isogeny class. Specifying a target and a tangent map is not an automatic discovery of all endomorphisms.

## Richelot correspondence and two descriptions of a kernel

Write the genus-two source as y²=F1(x)F2(x)F3(x), with three quadratic factors and nonsingular product. Let Delta be the determinant of their constant-first coefficient rows, and form cyclic brackets Gi=Fj' Fk-Fj Fk'. For nonzero Delta and smooth genus-two target, the target is

$$
v^2=G_1(z)G_2(z)G_3(z)/\Delta.
$$

The actual correspondence is specified by

$$
F_1(x)G_1(z)+F_2(x)G_2(z)=0,\qquad yv=F_1(x)G_1(z)(x-z).
$$

The code reduces the squared second equation modulo the first over Q(t)(x), checking the target relation exactly. The kernel is generated by the degree-zero divisors associated with the first two branch pairs, subtracting the two points at infinity. Twice each divisor is principal, and the third pair supplies their sum. The resulting maximal isotropic 2-torsion kernel has invariant factors (2,2) and order four. The receipt records the branch-pair polynomials rather than pretending that all branch coordinates are rational.

For the separate real reflection family y²=(x²-a²)(x²-b²)(x²-c²), 0<a<b<c, the program obtains an integral marked description. The half-rotation reverses the six real branch points; its declared braid is the Garside half twist. Each braid generator is represented by a Picard–Lefschetz transvection on the standard symplectic lattice. All braid relations and symplectic identities are replayed.

The involution's positive and negative saturated invariant lattices are obtained by Smith reduction. Their restricted polarizations are twice principal. They are therefore the transfer lattices for the two actual reflection covers u=x²,v=y and u=x²,v=xy. Duality supplies the integral norm maps. The combined maps satisfy GF=FG=2I; the norm has Smith factors (1,1,2,2). Its Smith certificate yields two explicit order-two source-torus kernel generators. This result depends on the supplied real branch marking, not an arbitrary choice of integral matrices compatible with a differential projector.

## Superelliptic pole reduction and Hodge information

The new curve class is y^d=f(x,t), with monic squarefree f of degree m, gcd(d,m)=1, and degrees between two and eight. The state dimension (d-1)(m-1) is capped at 32. The one-point-at-infinity condition avoids additional residue coordinates. A basis consists of x^i dx/y^j, with 1<=j<d and 0<=i<m-1. A basis form is holomorphic precisely when mj>d(i+1).

For a numerator h and pole f^r, write h=A f+B f' using the inverse of f' modulo f. Then

$$
\frac{h}{f^r}\frac{dx}{y^j}\equiv
\frac{A+\frac{d}{j+d(r-1)}B'}{f^{r-1}}\frac{dx}{y^j}.
$$

The discarded term is the exact derivative of -d B/((j+d(r-1))f^(r-1)y^j). High polynomial degrees are reduced using derivatives of x^k y^(d-j). The accumulated primitive is retained with a known power-of-f denominator; the implementation replays a cleared polynomial identity, avoiding expensive generic rational-function normalization.

Parameter differentiation has numerator -(j/d)x^i f_t with pole order one. Reducing it produces the connection in each character sector. The trigonal family y³=x⁴+x+t has genus three, six state coordinates and three holomorphic forms. Its two rank-three character sectors remain visible to invariant searches. These sectors are de Rham character blocks; the receipt does not assert a rational integral splitting of its Jacobian.

## Tensor invariants and filtered horizontal algebra

DifferentialModule uses the convention Y'=A Y. Its tensor connection is A tensor I+I tensor B; the dual is -A transpose. Hom uses T'=B T-T A. Symmetric powers act on monomials, and exterior powers act on signed wedges. Parameter pullback substitutes the rational parameter map and multiplies by its derivative. An invertible gauge is checked through its intertwining identity.

A rational horizontal section is sought with a supplied polynomial denominator and bounded numerator degree. Clearing all coefficient denominators turns the differential identity into a rational constant linear system. Its full kernel supplies the complete section space within that ansatz. Replay substitutes every returned section into v'=A v. The word complete applies to the ansatz, not all rational functions of unbounded degree.

The same machinery searches horizontal endomorphisms. It can impose preservation of specified holomorphic basis indices and self-adjointness for a supplied, independently checked horizontal alternating pairing. The full resulting linear space is returned. Only its basis elements are tested for idempotence. General nonlinear idempotent enumeration, conjugate Hodge filtration, rational Betti descent and differential Galois group classification remain distinct questions.

## Binomial sums become polynomial period equations

For products of binomial coefficients with upper argument a n+b k+c and lower argument d n+e k+f, summed over 0<=k<=n, introduce one constant-term variable per factor. Collect the n, k and constant exponents into Laurent rational functions A, B and C. The generating function is exactly

$$
\operatorname{CT}_{z}\frac{C}{(1-tA)(1-tAB)}.
$$

Expanding the two geometric series enumerates n>=k>=0, so this identity holds for the entire supported affine-binomial class. It is a compiler identity, not a recurrence fitted to finitely many terms.

The Vandermonde sum, Apéry zeta(2) sum and Apéry zeta(3) sum have exact telescoping certificates. Their certificates reduce the shift identity to a polynomial equation D(k)P(k+1)-k^r P(k)=D(k)L(T)/T, and their factorial-cancelled boundary terms vanish at k=0 and k=n+2. Tests include the upper boundary k=n+1, where the original summand is zero but its shifted summand need not be.

For the zeta(2) sum a_n=sum_k binom(n,k)² binom(n+k,k), the recurrence is

$$
(n+1)^2a_{n+1}-(11n^2+11n+3)a_n-n^2a_{n-1}=0.
$$

The generating-function operator is theta²-t(11theta²+11theta+3)-t²(theta+1)². Independently, the program derives the period operator of

$$
y^2=x^3+(t^2+6t+1)x^2+8t(t+1)x+16t^2.
$$

The two monic operators agree exactly. Their normalized analytic solution at t=0 has the same initial coefficient a0=1 and is fixed by the recurrence. This creates a direct sequence-to-curve bridge. The general constant-term compiler does not promise an equally short telescoper or an elliptic interpretation for every input.

## Rigorous ordinary transport and marked periods

The continuation engine computes Taylor coefficients over Gaussian rationals. At each center c it certifies a disk of radius R by bounding each denominator away from zero. The constant denominator coefficient contributes a lower bound max(abs(real),abs(imag)); all remaining centered coefficients contribute subtracted upper bounds. A failed disk causes step subdivision; failure to obtain a disk or exhausting the step budget returns no certified continuation.

If M bounds the connection's induced row norm on the disk, the fundamental matrix obeys a Gronwall bound exp(MR). Cauchy's estimate then bounds the tail of the Taylor polynomial of degree N at displacement h. With rho bounded by abs(h)/R,

$$
\|\text{tail}\|_\infty\leq
n\exp(MR)\frac{\rho^{N+1}}{1-\rho}.
$$

All quantities are bounded rationally, including the exponential, using (1-x/q)^(-q) for an integer q>x. Matrix multiplication propagates both the centers and row-norm errors. This is a rigorous ordinary analytic enclosure, though deliberately conservative. Small error bounds may require shorter steps or higher Taylor order.

Marked Legendre execution supplies certified seeds at t=1/2 for the standard a and b cycles. Periods of dx/y are divided by 2pi. The seed columns use F(t)=2K(t)/pi and iF(1-t), with their derivatives. The central-binomial series supplies rational centers; bounding each coefficient by one supplies explicit geometric and differentiated-geometric tails. The seed error is propagated through the certified matrix. General singular-endpoint continuation and automatic extraction of integral monodromy from numerical balls remain open.

## Clusters, local roots and geometric semistable graphs

For rational split branch roots over an odd p-adic field, the cluster tree is built from exact valuations of pairwise differences. Every internal node has depth equal to the smallest difference valuation in that cluster; deeper congruence classes become its children. Negative depths are allowed and remain explicit.

The double-cover graph counts odd branch flags on each cluster component, including the parent flag and infinity. A component with 2r odd flags lifts to a connected component of genus r-1. A component with no odd flags lifts to two rational components. An odd edge has one lift with half the base length; an even edge has two lifts with the full length. The returned graph is checked for connectedness and satisfies genus=sum(component genera)+graph cycle rank.

For three even pairs of roots [0,3], [1,4], [2,5] at p=3, the graph cycle rank is two and the total genus is two. The graph is geometric and marked before contractions. Twists of components, arithmetic Frobenius actions and minimal regular models are not derived. Separately, the family product((x-a)²-t) has exact simultaneous root branches a±r after t=r²; its contact matrix resolves several nodes in one parameter chart.

## Actual Frobenius matrices and checked precision

For a monic odd-degree good-reduction model over the prime field, lift x to x^p and expand the inverse square root of the Frobenius defect Delta=f(x^p)-f(x)^p. A basis form x^i dx/y is sent to

$$
p x^{p(i+1)-1}\sum_{k\geq0}
\binom{-1/2}{k}\frac{\Delta^k}{f^{pk+(p-1)/2}}\frac{dx}{y}.
$$

The defect is divisible by p. Every retained term is reduced exactly over Q using vertical pole reduction and horizontal polynomial reduction. This avoids ambiguous division in an insufficient-precision residue ring. Only the final rational matrix is reduced modulo p^N.

The omitted terms are certified using Kedlaya's pole-reduction denominator bounds. Expanding a numerator in powers of the monic f gives integral remainders of degree at most 2g. Negative and positive y-power reductions lose at most the corresponding floor(log_p(abs(exponent))) digits. The implementation deliberately adds conservative loss bounds for both directions. For term k the retained precision is bounded below by

$$
k+1-\lfloor\log_p(2pk+p)\rfloor
-\lfloor\log_p(2p\deg(f)+1)\rfloor.
$$

For k>=1 this lower bound is nondecreasing and tends to infinity. The truncation begins its omitted tail only when the bound reaches the requested precision. Agreement between two truncations is tested as an extra check, not used as the justification for precision.

An independent finite-field enumerator counts points in extensions of degrees one through genus. For degrees two and three, it finds an irreducible monic modulus by checking that it has no base-field root. Newton identities and the curve functional equation reconstruct the exact Weil polynomial. This independent route checks the cohomological matrix and the three-factor tower. Enumeration is useful at these bounded primes, not a substitute for scalable arithmetic cohomology.

Frobenius deformation uses the same connection with the lift sigma(t)=t^p. In the row cohomology convention its equation is

$$
F'=p t^{p-1}A(t^p)F-F A(t).
$$

An independently certified base matrix determines successive formal coefficients. Integrality and analyticity of the connection on the p-adic unit disk are checked. The base precision is increased by v_p(order!), and every jet records its own factorial precision loss and scaling. The receipt supplies formal jets; it does not claim evaluation across a nonconvergent parameter boundary.

## The sunrise integral: a boundary becomes a state

For the equal-mass two-dimensional sunrise integral, use the affine Symanzik polynomial

$$
F(x,y,t)=(x+y+1)(xy+x+y)-txy.
$$

Completing the square in y produces the elliptic quartic with constant-first coefficients (1,2-2t,t²-6t+3,2-2t,1). Independent de Rham reduction gives the absolute period operator

$$
L=t(t-1)(t-9)\partial_t^2+(3t^2-20t+9)\partial_t+(t-3).
$$

The relative integral I(t)=integral over the positive affine quadrant dx dy/F has boundary terms. The compiler solves an exact bivariate polynomial linear system for U,V such that

$$
L(1/F)=\partial_x(U/F^2)+\partial_y(V/F^2).
$$

It imposes U(0,y)=3y² and V(x,0)=3x². On the Euclidean nonsingular domain the infinity contributions vanish, and the two finite-axis contributions integrate to -3 each. Consequently LI=-6. The complete divergence identity is replayed; the right side is not added merely because it is known from the literature.

The augmented state (I,I',1) has rank three and is homogeneous as a matrix differential system. The absolute elliptic period system has rank two. Both arise from the same defining polynomial, but the amplitude requires the extra boundary state. This is the concrete relative-cohomology distinction that a polynomial-only homogeneous period calculation can miss.

## Reproducibility and remaining boundaries

Run PYTHONPATH=python python -m unittest discover -s python/tests -p test_literature_curve_execution.py to check the focused suite. Run make test for the existing combined suite. Function-based physics tests have separate direct entry points and remain separate mathematical evidence. Run python python/literature_curve_corpus.py to regenerate every receipt, then render this source through the monograph renderer's literature edition.

All newly built capacities are bounded and include their inputs and conventions. Important unresolved generalizations include automatic higher-genus formal correspondences, integral cycle maps for arbitrary quotient towers, singular Richelot product targets, general Puiseux/cluster arithmetic with nonsplit roots, optimized arbitrary-field Frobenius, singular-endpoint certified analytic continuation and complete differential Galois groups. A differential projector alone still does not prove an algebraic correspondence or Jacobian decomposition. The actual-cover examples prove their specific decompositions through verified maps.

Singular Richelot product targets and cluster arithmetic with quadratic (including ramified) roots are now treated in the [singular Richelot and cluster monograph](SINGULAR_RICHELOT_AND_CLUSTERS_MONOGRAPH.md). That treatment covers component twists through the inertia action and the conductor exponent; it constructs neither minimal regular models nor Frobenius on components.

## Primary literature

J. S. Milne, Fields and Galois Theory: https://www.jmilne.org/math/CourseNotes/FT.pdf. J. S. Milne, Tannakian Categories: https://www.jmilne.org/math/xnotes/tc.pdf.

E. Kani and M. Rosen, Idempotent relations and factors of Jacobians, Mathematische Annalen 284 (1989), 307–327. S. Reyes-Carocca and R. E. Rodríguez, A generalisation of Kani–Rosen decomposition theorem: https://arxiv.org/abs/1702.00484.

E. Costa, N. Mascot, J. Sijsling and J. Voight, Rigorous computation of the endomorphism ring of a Jacobian: https://arxiv.org/abs/1705.09248. N. Bruin and K. Doerksen, The arithmetic of genus two curves with (4,4)-split Jacobians: https://arxiv.org/abs/0902.3480.

P. Griffiths, On the periods of certain rational integrals, Annals of Mathematics 90 (1969). P. Lairez, Computing periods of rational integrals: https://arxiv.org/abs/1404.5069. A. Bostan, P. Lairez and B. Salvy, Multiple binomial sums: https://arxiv.org/abs/1510.07487.

E. C. Sertöz, Computing periods of hypersurfaces: https://arxiv.org/abs/1803.08068. M. Mezzarobba, Rigorous Multiple-Precision Evaluation of D-Finite Functions in SageMath: https://arxiv.org/abs/1607.01967.

T. Dokchitser, V. Dokchitser, C. Maistret and A. Morgan, Arithmetic of hyperelliptic curves over local fields: https://arxiv.org/abs/1808.02936.

K. S. Kedlaya, Counting Points on Hyperelliptic Curves using Monsky–Washnitzer Cohomology, especially Lemmas 2 and 3: https://arxiv.org/abs/math/0105031. K. S. Kedlaya and J. Tuitman, Effective convergence bounds for Frobenius structures on connections: https://arxiv.org/abs/1111.0136. A. G. B. Lauder, Deformation theory and the computation of zeta functions: https://people.maths.ox.ac.uk/lauder/papers/dtczDec6.pdf.

P. Lairez and P. Vanhove, Algorithms for minimal Picard–Fuchs operators of Feynman integrals: https://arxiv.org/abs/2209.10962. S. Bloch and P. Vanhove, The elliptic dilogarithm for the sunset graph, equation (5.1): https://arxiv.org/abs/1309.5865.
