# Branch degenerations, positive geometry, and exact monodromy witnesses

## Reader's orientation

This release extends PerfectPower's exact branching module in three directions. It follows labelled roots through collisions, builds the associahedral face structures of ordered real branch configurations, and converts cyclic connection Laplacians into explicit polytopes of minimal monodromy witnesses. A fourth direction provides genuine arithmetic examples: Descartes circle reflections generate polynomial curvature sequences, and the existing integer-root and recurrence engines inspect their perfect-power values. A fifth direction supplies the finite linear-algebra contract that removes a meromorphic differential's holomorphic ambiguity by prescribing periods.

The implementation is standard-library Python. Its arithmetic uses integers, rational numbers and exact cyclotomic quotient coordinates. It includes eight console routes, a deterministic corpus builder, mathematical differential tests, a source-linked index over the committed quartic atlas, and a machine-readable handoff for separate Lean formalization. No new Lean files are introduced by this release. Existing results in PerfectPower/BranchedGeometry.lean belong to the preceding branching push, and their status is not transferred automatically to this extension.

The central design decision is to keep different spaces distinct. The compact normalized algebraic curve is the geometric object attached to an equation. The ordered configuration space of its branch points is a parameter space. A graph of analytic-continuation paths is a finite transport model. The polytope of full-rank graph bases is a fourth object. Their relations are exact where stated, but these objects have different dimensions, different boundaries and different meanings for Euler characteristic.

## 1. From a perfect-power equation to a normalized cover

For an integer polynomial P and an exponent d at least two, the equation y^d=P(x) asks whether the polynomial's value at an integer input is a perfect power. Over the complex numbers, the same equation gives a cyclic branched cover of the x-line. Its compact normalization is a disjoint union of smooth compact Riemann surfaces. Root multiplicities determine the number of components and their ramification, independently of the nonzero scalar multiplying P.

Suppose the distinct roots have positive multiplicities r_1,...,r_s. Put c=gcd(d,r_1,...,r_s), e=d/c and a_i=r_i/c. The normalization has c components, each giving a connected cover of degree e. In the absence of roots, use c=d and e=1; a nonzero constant equation splits into d copies of the projective x-line over the complex numbers.

```math
chi_component = 2e - sum_i(e-gcd(e,a_i)) - (e-gcd(e,sum_i a_i)).
g_component = (2-chi_component)/2.
chi_total = c*chi_component = 2c-2*c*g_component.
```

At a finite root with reduced multiplicity a_i, there are gcd(e,a_i) points above that root and their total ramification contribution is e-gcd(e,a_i). Infinity has reduced pole order equal to the sum of the a_i and contributes e-gcd(e,sum_i a_i). Subtracting these contributions from twice the cover degree is precisely Riemann-Hurwitz. The code checks parity and the resulting genus, and replays every representative collision pattern through the preceding module's independently computed squarefree polynomial decomposition.

For a squarefree polynomial of degree m, this reduces to the familiar formula with delta=gcd(d,m): twice the genus is (d-1)(m-1)-delta+1. Repeated roots require the general formula. Replacing a polynomial by its squarefree part without preserving multiplicities would lose both component information and the sheet transport.

The arithmetic scalar remains separate. Root multiplicities divisible by d imply a complex polynomial root, because every nonzero complex constant has a d-th root. An integer polynomial root additionally needs the signed integer content to be a d-th power. The committed branching profile carries that information. The new collision records describe complex normalized topology and do not silently infer integer polynomial roots.

## 2. Euler polyhedra and Descartes angular defect

For a closed triangulated metric surface, the vertex defect is two pi minus the sum of incident triangle angles. Since every Euclidean triangle has angle sum pi and every edge belongs to two triangles, the sum of defects is two pi times V-E+F. For several components with total genus G, it is four pi times c-G.

```math
sum_v kappa_v = 2*pi*(V-E+F) = 4*pi*(c-G).
```

The release supplies explicit equilateral quotient metrics on the topological cell models already constructed by the branching module, for genera zero through seven. The sphere uses an octahedron. Higher genera use the standard identified commutator polygon triangulation. Every triangle has angle pi/3, so vertex defects can be stored exactly as rational multiples of pi. These metrics are mathematically defined on the quotient cell surface. They are not a claim to have recovered the original algebraic curve's conformal metric or an embedding in Euclidean three-space.

For the spherical octahedron, six vertices each receive four triangle corners and each has defect 2*pi/3. Their total is 4*pi. The one-vertex genus-two quotient has eighteen corners, so its sole defect is -4*pi. The dual cellulation is trivalent. Its combinatorial face charge, obtained by summing six minus each face's side count, is six times the Euler characteristic. This is a combinatorial identity, not an assertion that side counts alone specify pointwise geometric curvature.

The equilateral metric packets include vertex, edge and face counts, corner counts, individual defects, total defect, dual face charge and harmonic dimensions. Each of these quantities is replayed rather than filled from a descriptive label. The recorded harmonic dimensions are the finite cell model's dimensions; analytic periods of the original curve are not inferred from its topology alone.

## 3. Labelled collision strata

The collision atlas enumerates every set partition of a labelled root set. A block represents roots that acquire a common limiting location. Its limiting multiplicity is the sum of the original multiplicities in that block, and its sheet voltage is that sum modulo d. Applying the normalized-cover formula to all blocks computes the topology of the normalization of the resulting collision polynomial.

Partitions are generated in restricted-growth order. At step i, the next label is appended to one existing block or creates one new final block. This gives each labelled partition exactly once. Tests reproduce Bell numbers through eight labels and check that every partition covers its root set without repetition. Enumeration is bounded at eight labels because Bell numbers grow rapidly.

The release corpus uses exponents two through eight and squarefree root counts two through six. There are thirty-five families and 1,939 labelled strata. For example, five squarefree roots have fifty-two possible labelled collision partitions. Sorting the resulting multiplicity blocks produces 196 distinct exponent/multiplicity patterns across the corpus; these representatives are each checked against an explicit polynomial with integer-labelled distinct roots.

These records do not describe a general stable admissible-cover construction. A collapsed polynomial, its singular curve, its normalization and the stable limit of a chosen family are different objects. The release exposes this distinction explicitly in the Legendre family rather than assigning a fictitious stable curve to every abstract partition. Nested collision directions require more data than the final merged multiplicities.

## 4. Ordered branch configurations and associahedra

Consider N labelled real points on the projective line in a fixed cyclic order. Modding out by projective transformations leaves N-3 parameters. The standard stable compactification of that ordered chamber is associahedral. Its faces are indexed by compatible splits, equivalently by noncrossing diagonals of an N-gon.

The implementation enumerates all sets of mutually noncrossing diagonals. A set containing k diagonals has codimension k. The empty set labels the full polytope. Maximal sets label its vertices, which correspond to triangulations of the polygon. Each face records its dimension, its diagonals, its additional boundary diagonals and the associated partitions of the marked labels.

The f-vector is stored in increasing dimension and includes the full polytope. For N=4 it is (2,1); for N=5 it is (5,5,1); for N=6 it is (14,21,9,1). The corpus continues through N=9, where the vector is (429,1287,1485,825,225,27,1). Across these six associahedra the corpus contains 5,438 faces. The alternating face count of the full polytope is one. The boundary has Euler characteristic one plus (-1) to the power dimension minus one.

The associahedron is the configuration chamber, not the covering curve. For example, a smooth elliptic covering curve has Euler characteristic zero while its four-marked-point parameter chamber is an interval whose closed Euler characteristic is one. This difference is expected and is part of the data contract.

## 5. Canonical forms and collision residues

Fix marked points at zero, one and infinity. Write the remaining ordered points as 0<z_1<...<z_r<1. The gauge-fixed canonical worldsheet form has coefficient equal to the reciprocal of the product of consecutive gaps.

```math
Omega = dz_1 wedge ... wedge dz_r /
        [z_1*(z_2-z_1)*...*(z_r-z_(r-1))*(1-z_r)].
```

In the open coordinate chart this region looks like a simplex. Its stable compactification exposes additional collision divisors by blowups. This is why a two-dimensional ordered chamber produces a pentagon even though the inequalities 0<x<y<1 describe an open triangle in the elementary coordinate plane.

For the five-marked-point case, make the collision substitution x=t*u and y=t. Then dx wedge dy equals t du wedge dt. The canonical form factors as a logarithmic transverse factor and the lower-dimensional boundary form.

```math
Omega_5 = du wedge dt/[u*(1-u)*t*(1-t)].
Boundary residue at t=0, up to orientation: du/[u*(1-u)].
```

The code evaluates this identity exactly at rational chart coordinates and exports the formula and boundary convention. This is an implemented residue calculation, not merely an associahedral face count. It gives the first concrete contract for recursive collision charts: the transverse logarithmic pole should reproduce the canonical form of the boundary configuration.

For intervals, the canonical form is (b-a)dx/[(x-a)(b-x)]. Subdividing at an interior point c gives an exact identity of rational forms: the form for [a,b] is the sum of the forms for [a,c] and [c,b]. The artificial poles at c cancel. The tests evaluate that identity away from all endpoints, both inside and outside the interval, since it is an algebraic identity rather than an identity restricted to an integration domain.

## 6. The Legendre family and its two monodromies

The Legendre family is y^2=x(x-1)(x-lambda). For lambda different from zero and one, it is a smooth elliptic curve after compactification. The branch-polynomial discriminant is lambda^2*(1-lambda)^2 and the usual elliptic discriminant is sixteen times this expression. The positive chamber is 0<lambda<1; its canonical form is dlambda/[lambda*(1-lambda)].

At lambda=0, the affine equation is y^2=x^2(x-1). Its normalization map is x=v^2+1 and y=x*v. The two preimages of the node are v=+i and v=-i. At lambda=1, the map is x=v^2 and y=(x-1)*v; the node preimages are v=+1 and v=-1. Both special cubics are irreducible nodal curves with arithmetic genus one and singular Euler characteristic one, while their normalizations have genus zero and Euler characteristic two. The dual graph has one vertex and one loop, retaining the arithmetic genus contribution lost by normalization.

The normalized period series about lambda=0 has coefficients a_n=binomial(2n,n)^2/16^n. Its coefficient recurrence is exact and implies the Picard-Fuchs equation on the formal series.

```math
(n+1)^2*a_(n+1) = (n+1/2)^2*a_n.
lambda*(1-lambda)*Pi'' + (1-2*lambda)*Pi' - Pi/4 = 0.
```

The builder stores sixty-four coefficients at each Legendre parameter packet. These coefficients define the same formal series centered at zero; storing them in an endpoint packet does not mean the series has been evaluated at a singular endpoint. The general function supports a stated finite coefficient budget. It supplies no approximation to a complex analytic period.

Fibre monodromy moves x around a branch root and acts by finite cyclic sheet changes. Parameter monodromy moves lambda around a collision and acts on homology and periods. For the standard marked Legendre period convention, the matrices around zero and one are [[1,2],[0,1]] and [[1,0],[-2,1]]. These analytic conventions are recorded as source-backed data. They are not identified with the finite sheet voltage, and this release does not formalize their analytic derivation.

## 7. Why residues need periods on positive-genus curves

On a compact connected curve, a meromorphic differential with only specified simple poles must have residues summing to zero. When that compatibility condition holds, prescribing the poles and residues leaves an affine space of solutions whose difference space is the g-dimensional space of holomorphic differentials. The geometry therefore needs a period marking to select one differential when g is positive.

Choose holomorphic differentials eta_j normalized on chosen a-cycles by integral_(a_i) eta_j=delta_ij. The difference of any two candidate differentials with the same simple poles and residues is determined by its a-periods: it equals the sum of those periods times eta_j. This is the exact place where the branching module's harmonic dimensions and the period-normalization contract interact.

The finite API accepts a square invertible rational matrix M of supplied basis periods, a vector p of candidate periods and a desired vector t. It returns c=M^(-1)(t-p), checking M*c=t-p and p+M*c=t. The resulting statement is exact for the supplied finite data. Real analytic periods are generally not rational; this API neither generates them nor replaces them by rational surrogates. It is a contract for the finite algebra that a future analytic period producer must feed.

A singular period matrix is rejected, because the supplied period conditions then fail to determine a unique correction. A nonzero residue sum is recorded as an existence obstruction before any normalization is attempted. The genus-zero case has no holomorphic ambiguity and needs no period correction.

## 8. Cyclic connections and exact support rank

A voltage edge (u,v,r) represents the equation f_v=zeta^r*f_u, with zeta a primitive d-th root of unity. The incidence row has coefficient -zeta^r at u and coefficient one at v. Loops and parallel edges are supported. A loop becomes the row coefficient one minus zeta^r; it can itself carry a nontrivial obstruction.

The coefficient ring is the standard cyclotomic quotient Q[z]/Phi_d(z). Cyclotomic polynomials are produced recursively by exact division of z^d-1 by the polynomials for proper divisors. Conjugation substitutes z^(d-1) for z. Matrix operations stay in these exact coordinates; there is no numerical spectral threshold.

Tree potentials transport values along a spanning tree. Every remaining edge gives a residual voltage modulo d. A connected component is balanced exactly when every residual vanishes. A balanced component contributes one dimension to the character kernel; an unbalanced component contributes none. Isolated vertices are balanced components and are counted. Therefore the incidence rank is the number of vertices minus the number of balanced components.

For each component, the number of connected components in the d-sheet lift is gcd(d,all residual voltages). Across the graph these counts add. Summing kernel dimensions across all d characters reproduces that lift component count. The tests check this character decomposition against normalized-cover component counts on root-channel graphs.

The root-channel graph uses two vertices and parallel paths with cumulative voltages zero,r_1,r_1+r_2,... . Adjacent paths enclose one labelled root each; a loop across several paths detects the sum of the enclosed multiplicities. This finite transport model captures all root generators. It is not an intrinsic Voronoi tessellation of the original complex curve.

## 9. Forest determinants and Newton polytopes

Give the graph nonnegative rational edge weights and form L=B^*WB. Cauchy-Binet expands its determinant into squared maximal minors times squarefree edge-weight monomials. The independent forest formula states that a contributing n-edge set, where n is the number of vertices, must have one unbalanced cycle in every connected component. Its coefficient is the product of two minus h minus h inverse over those cycles.

```math
det L = sum_(|I|=n) conjugate(det B_I)*det B_I*prod_(e in I) w_e.
Cycle coefficient = 2-h-h^(-1) = |1-h|^2.
```

The implementation computes every coefficient twice: once as a squared determinant of an incidence minor, and once as a forest product extracted from tree residuals. It then evaluates the resulting polynomial at supplied weights and checks it against an independent determinant of the Gram matrix. Random tests also expand the cyclotomic matrix into a rational multiplication-block matrix and compare its rational rank with the support-rank certificate.

Taking the convex hull of the nonzero monomial exponent vectors gives the base polytope of the represented linear matroid. Its vertices are full-rank minimal edge sets. A positive determinant means that the positive-weight support retains full rank. The graph may become disconnected after channels are removed; every surviving component must remain unbalanced for full rank. A single unbalanced component cannot protect isolated balanced vertices elsewhere.

The basis polynomial yields edge marginals. The logarithmic derivative w_e*(partial Q/partial w_e)/Q is the probability that edge e belongs to a basis under the determinant-weighted basis distribution. Their sum is n. The packet computes these quantities in exact cyclotomic coordinates. If Q=0, the marginal vector is undefined and is stored as null. It is not interpreted as a vector of zero importance.

These are graph-information probabilities, not probabilities of an integer solution and not physical scattering amplitudes. Nonnegative squared minors also do not imply that the original complex incidence matrix is totally positive. The object is a genuine representable-matroid Newton polytope; a further amplituhedron identification would require additional structure.

## 10. The three-edge triangle and its logarithmic form

For two vertices and transports one, minus one and i, give the three edges weights a,b,c. The Laplacian has diagonal a+b+c and an off-diagonal transport sum a-b+i*c, up to the chosen conjugation convention. Its determinant is four a*b plus two a*c plus two b*c. Every pair of edges is a full-rank basis.

```math
Q = 4ab+2ac+2bc.
q_1=2bc/Q, q_2=2ac/Q, q_3=4ab/Q.
q_1+q_2+q_3=1.
```

The q_i are probabilities of the three bases, indexed by the missing edge. Hence the edge marginals are one minus q_i. At unit conductances the determinant is eight, the basis probabilities are one quarter, one quarter and one half, and the edge marginals are three quarters, three quarters and one half.

Fix c, leaving two independent conductance ratios. The Jacobian of (a,b) to (q_1,q_2) equals 16*a*b*c^2/Q^3. The product q_1*q_2*q_3 equals 16*a^2*b^2*c^2/Q^3. Their ratio is exactly 1/(a*b), proving that the simplex canonical form pulls back to da wedge db divided by a*b. The implementation checks the identity with exact rational values, and the handoff states its polynomial numerator identity for a direct Lean ring proof.

This example connects a monodromy graph, a nonnegative determinant expansion, a convex polytope and a canonical logarithmic form without inventing a physics interpretation. The next generalization is to canonical forms of the larger basis polytopes, using established Newton-polytope and positive-geometry techniques. Only the triangle and ordered-branch forms are computed here; a general polytope canonical-form solver remains future work.

## 11. Minimum-cost witnesses without enumerating every basis

The number of maximal minors grows combinatorially. The explicit determinant packet therefore has a subset budget and a twelve-vertex matrix budget. A request exceeding that budget is rejected before enumeration. This is separate from the minimum-cost API, which uses the represented matroid's greedy property.

Order edges by nonnegative exact cost, with their index breaking ties. Add an edge precisely when it raises the support rank. The selected set is a minimum-cost basis when full rank is achievable, and a minimum-cost maximum-rank independent set otherwise. The report includes every accepted rank increment and the total cost. It does not assert full-rank feasibility when the graph remains deficient.

Tests enumerate all bases of many small random graphs and compare their minimum cost with the greedy result. The value of this route is practical: after a large graph's analytic continuation paths have been assigned costs, a minimal sufficient collection can be selected without listing all full-rank subsets. The objective protects graph monodromy information; it is not a new Diophantine height bound.

## 12. Descartes circle reflections and polynomial arithmetic

Four mutually tangent circles with signed curvatures b_i satisfy the Descartes quadratic equation. Holding three curvatures fixed gives a quadratic in the fourth. The sum of its two roots is twice the sum of the three fixed curvatures, yielding the reflection formula b_i'=2*sum_(j!=i)b_j-b_i. This reflection preserves the quadratic equation, preserves integrality and is an involution.

Fix two circle indices and alternate reflections of the remaining two. Let their starting curvatures be u,v and the sum of the fixed curvatures be s. Successive moving curvatures obey b_(n+2)=2*b_(n+1)-b_n+2s. Solving by constant second differences gives a polynomial valid at every nonnegative index.

```math
b_n = u+(v-u-s)*n+s*n^2.
(E-1)^3 b = 0.
```

The existing recurrence engine accepts the homogeneous recurrence coefficients (1,-3,3) and the initial terms (u,v,2s+2v-u). The new orbit API independently executes the actual Descartes reflections at every scanned index and checks agreement with the polynomial. This is a definition-based sequence, not a polynomial guessed from a finite prefix.

For the seed (-1,2,2,3), fixing the first two circles gives s=1,u=2,v=3 and b_n=n^2+2. The sequence begins 2,3,6,11,18,27,38,51,66,83. Its cube hit at index five is 27=3^3, corresponding to n^2=t^3-2. Thus a geometric circle-packing orbit enters the same Mordell equation family used by the arithmetic project.

The release scans twenty-four distinct polynomial orbit families, chosen deterministically from reflections of the seed, for indices zero through 9,999 and exponents two through six. This gives 240,000 checked curvatures and 1,200,000 bounded power tests, with twenty-six recorded hits. Those hit sets are bounded observations. They are not promoted to complete classifications. Algebraic signed-curvature orbits are also kept separate from a proof that every selected seed and reflection word represents a chosen admissible geometric packing.

For the principal n^2+2 family, the absence of square hits does have a short independent proof: at n=0 the value is two, while for n>=1 it lies strictly between n^2 and (n+1)^2. The bounded cube hit does not by itself prove the completeness of the cube list. A separate existing Mordell certificate or theorem must be used for such a claim.

## 13. Descartes signs as a real-branch tool

For a rational open interval (a,b), substitute x=(a+b*t)/(1+t) and multiply by (1+t)^degree. Positive t corresponds exactly to the open interval. Descartes' sign variations bound the number of roots there, counting multiplicities, and the difference between the bound and the true count is even. Zero and one variations therefore give exact counts of zero and one respectively. Larger variation counts are reported only as upper bounds.

Endpoint roots are excluded. Zero transformed coefficients are omitted from the sign sequence. The zero polynomial is rejected. This is a real-root branch and chamber tool, not an integer-solution solver. Repeated roots are allowed in the count, although efficient recursive isolation ordinarily begins by squarefree decomposition.

The corpus includes interval sign records for a polynomial with rational branch roots. A later extension can recursively subdivide intervals, track algebraic branch coordinates, and expose real discriminant chambers of one-parameter polynomial families. This release implements the exact interval predicate and its endpoint semantics, not a general multivariate discriminant decomposition.

## 14. The corpus and its integration

The committed predecessor contains 12,320 topology rows for 3,080 quartics and exponents two, three, four and six. The new corpus groups them into twelve monodromy patterns, assigns an exact root-channel connection polytope to each pattern, and retains every source curve index. The source file's SHA-256 is recorded. This provides an actual integration with the existing results rather than only detached small examples.

The new corpus includes collision strata, connection polytopes, associahedral faces, canonical branch forms, equilateral polyhedral defects, Legendre degeneration packets, Descartes orbit scans, period contracts, real-root sign predicates and a machine-readable Lean handoff. The deterministic builder writes a manifest with hashes and byte counts of its generated files. Validation logs are written separately so that rerunning the mathematical builder does not turn machine timing into a mathematical invariant.

The focused tests cover gauge changes, edge reversals, loops, parallel edges, missing channels, exact weights, matrix ranks, minimum-cost bases, root partitions, associahedral counts, normalization maps, formal period recurrences, canonical-form pullbacks, residue compatibility, reflection involutions, all choices of fixed circle pair, and the console routes. Existing package tests are also run. Work limits and malformed-input checks are part of the executable API.

## 15. Reproduction and Lean handoff

Run commands from the repository root. Set PYTHONPATH to python when invoking the uninstalled package. Installing the repository with pip install . makes the perfectpower command available. All runtime code in this extension uses the Python standard library; PDF generation is only a packaging dependency.

```sh
PYTHONPATH=python python -m perfectpower collision-atlas --multiplicities '[1,1,1,1,1]' --d 2
PYTHONPATH=python python -m perfectpower associahedron --marks 6
PYTHONPATH=python python -m perfectpower legendre --parameter 1/2
PYTHONPATH=python python -m perfectpower connection-polytope --vertices 2 --edges '[[0,1,0],[0,1,2],[0,1,1]]' --d 4
PYTHONPATH=python python -m perfectpower descartes-orbit --stop 10000
PYTHONPATH=python python -m perfectpower period-normalize --matrix '[[2,1],[1,1]]' --periods '[3,-2]' --target '[1,4]'
PYTHONPATH=python python -m perfectpower branch-signs --coeff=-1,1 --left 0 --right 2
PYTHONPATH=python python -m perfectpower branch-form --collision-chart '["2/5","3/7"]'
PYTHONPATH=python python python/build_positive_geometry.py
```

For Windows PowerShell, set $env:PYTHONPATH='python' before the commands and invoke the installed Python executable. The Python module entry point and corpus builder do not require bash. The shell check script is an optional convenience for Unix environments.

The recommended first Lean targets are polynomial reflection preservation and involution, the quadratic orbit identity, the formal hypergeometric coefficient recurrence, the theta determinant, the canonical Jacobian numerator, the pentagon collision-chart identity, and the equilateral defect sum. These are finite algebraic statements with explicit fixtures. The period correction follows from the existing exact matrix conventions. The general forest expansion, support-rank theorem and greedy optimality require more structural formalization.

Analytic Riemann-Hurwitz, meromorphic residue existence, analytic period equations and the associahedral compactification remain separate theorem targets. Finite algebraic identities should not be presented as proofs of those analytic statements. The supplied handoff records coefficient order, voltage orientation, period convention, face-vector convention, exclusive scan endpoints and the distinction between new Python results and already-compiled Lean results.

## 16. What this release makes possible next

The implementation now connects root-collision topology to ordered boundary configurations, exact graph obstructions and polynomial orbit arithmetic. The natural next mathematical extension is to attach stable admissible-cover and vanishing-cycle data to nested associahedral strata, rather than only to final collision multiplicities. A second extension is to construct canonical forms for general connection basis polytopes and prove their boundary recursions. A third is to supply analytic or certified numerical period data to the finite normalization contract.

The arithmetic direction is to classify perfect-power curvatures in the Descartes polynomial families using the project's existing complete solvers, retaining inverse maps to the circle orbit. Each direction has a concrete input and an executable intermediate representation. None requires declaring all these objects identical. Their value comes from preserving the relationships between them precisely.

## References

Pascal Molin and Christian Neurohr, Computing period matrices and the Abel-Jacobi map of superelliptic curves, arXiv:1707.07249. https://arxiv.org/abs/1707.07249

Keenan Crane, Discrete Differential Geometry: An Applied Introduction. https://www.cs.cmu.edu/~kmcrane/Projects/DDG/

Nima Arkani-Hamed, Yuntao Bai and Thomas Lam, Positive Geometries and Canonical Forms, arXiv:1703.04541. https://arxiv.org/abs/1703.04541

Nima Arkani-Hamed, Yuntao Bai, Song He and Gongwang Yan, Scattering Forms and the Positive Geometry of Kinematics, Color and the Worldsheet, arXiv:1711.09102. https://arxiv.org/abs/1711.09102

Francis Brown and Clement Dupont, Positive geometries and canonical forms via mixed Hodge theory, arXiv:2501.03202. https://arxiv.org/abs/2501.03202

Richard Kenyon, Spanning forests and the vector bundle Laplacian, arXiv:1001.4028. https://arxiv.org/abs/1001.4028

Ronald Graham, Jeffrey Lagarias, Colin Mallows, Allan Wilks and Catherine Yan, Apollonian Packings: Number Theory, arXiv:math/0009113. https://arxiv.org/abs/math/0009113

NIST Digital Library of Mathematical Functions, Section 15.10, Hypergeometric Differential Equation. https://dlmf.nist.gov/15.10

Alkiviadis Akritas and George Collins, Polynomial real root isolation using Descartes' rule of signs, Proceedings of SYMSAC 1976. https://doi.org/10.1145/800205.806346
