# Algebraic curve execution

## Purpose and mathematical position

This release turns algebraic coefficient fields, local degeneration geometry and finite curve symmetries into cooperating executable objects. Its central question is concrete: how much of a curve's geometry can be recovered, explained and executed while retaining its defining polynomial? The answer includes conjugate root motion without radical choices, local branch expansions at algebraic singular parameters, logarithmic differential jets through positive resonances, complete quotients of supplied finite actions, and specific Jacobian isogenies induced by paired double covers.

The result is an extension of the existing polynomial-family compiler, projective deformation quotient, continuous de Rham pairing, multi-parameter connections and integral simplicial homology machinery. The new operations reuse those objects but add independent reduction engines and replayable identities. No identification between an arbitrary finite Hodge matrix, a numerical mesh and continuous curve cohomology is introduced.

Milne's Fields and Galois Theory provides useful organizing principles: retain finite étale algebras instead of pretending every squarefree quotient is a field; calculate fixed algebras under actual automorphisms; use primitive elements to expose a complete finite algebra; construct rational fixed fields through invariant coordinates; and check cyclotomic conjugacy before interpreting a differential splitting arithmetically. These are established mathematical principles. The contribution here is their exact integration with polynomial curve execution, not a claim of worldwide priority.

## Exact differential algebra

Let K be Q(t), or the repository's rational-function tower Q(t1,...,tr), with one through three parameters. For a monic squarefree polynomial m(Z), form A=K[Z]/m. A is finite étale; it may be a product of fields. Every element retains its coefficient vector and defining algebra. Equality, multiplication, inverse, trace, norm, characteristic polynomial and minimal polynomial are exact.

If an attempted divisor is a nonunit, polynomial Euclid returns a proper factor of m. That witness permits a caller to split the algebra rather than treating a zero divisor as a field element. This distinction is essential when a discriminant polynomial represents several conjugate or rational degeneration parameters at once.

For every parameter derivation, squarefreeness makes m_Z invertible in A and forces the generator derivative:

$$
\partial_j Z=-\frac{\partial_j m(Z)}{m_Z(Z)}.
$$

This determines the unique derivation extending the base derivation. Differentiating the defining relation replays to zero. Commutators of two extended derivations are derivations that vanish on the base; uniqueness makes them zero. The corpus verifies all three mixed pairs for a three-parameter quadratic extension. Trace differentiation and logarithmic norm differentiation are also checked directly from exact multiplication matrices.

An automorphism is specified by the image of Z. The compiler evaluates the unreduced defining polynomial at that image and checks that the induced multiplication-basis map is invertible. It then closes supplied generators to a finite group within a declared limit. The fixed algebra is the simultaneous kernel of sigma-I, with a complete basis and replayed multiplication table. It is not merely a list of guessed invariant elements.

The scalar Hilbert–90 operation requires a cyclic Galois étale torsor: the cyclic order equals the algebra degree and the fixed algebra has dimension one over the base. For a unit a, its group norm must equal one. The compiler solves a sigma(b)=b and searches its exact kernel for an invertible b. Success supplies a=b/sigma(b); norm failure supplies an obstruction; exhausted unit search reports the finite budget. This is scalar descent. It does not descend arbitrary vector bundles, projective objects or algebraic correspondences.

## Primitive models retain the full tensor product

Combining two algebraic values can silently discard conjugate branches if a program chooses a common embedding too early. The new tensor operation instead retains A tensor B in its complete product dimension. Nested étale arithmetic supplies the multiplication algebra. The compiler searches gamma=a+c b, computes its powers in a flattened basis, and accepts a candidate only if those powers form a full basis. It then recovers both original generators as polynomials in gamma and replays both defining relations.

For sqrt(2) and sqrt(3), gamma=a+b has polynomial Z^4-10Z^2+1. For two copies of sqrt(2), the complete tensor still has dimension four, although a+b does not generate it. The candidate a+2b succeeds with polynomial Z^4-20Z^2+36. This latter algebra retains both relative signs; calling it a degree-two compositum would lose information.

The supported tensor dimension is at most 16. Primitive-element search is finite and explicit. A successful full-rank certificate proves the returned model; an exhausted search does not prove that no primitive element exists. Irreducibility of the resulting polynomial is neither assumed nor asserted.

## Algebraic degeneration charts and infinity

CurveFamily supplies monic odd-degree families of degrees 3, 5 and 7. Its new local operations accept rational parameters, parameter infinity, or a squarefree rational algebra specifying an algebraic parameter alpha. Local coordinates are t=alpha+s^e and t=s^(-e), respectively. The connection is pulled back with the coordinate Jacobian, not simply substituted entry by entry.

The compiler returns exact Laurent valuations, the primitive special fibre, root-multiplicity layers, branching at infinity, discriminant valuation, a supported diagonal Fuchsian shear, residue and finite analytic coefficient jets. The shear is found by integer difference constraints with bounded weights. A curve may require a different gauge or a more general stable model; the algorithm does not claim universal Fuchsian normalization.

algebraic_degenerations starts with the squarefree support of the discriminant, so repeated roots of the discriminant are covered as locations even when the singular fibre is more complicated than a simple node. It splits on nonunits when component behaviours differ and records the number of covered algebraic parameter roots. The corpus covers four roots for y²=x⁵-x+t and the two finite Legendre degenerations. Infinity is a separate chart and is not counted among those six finite roots.

Several algebraic parameter values may remain in a single étale component when the needed identities and orders agree. A nonunit leading discriminant coefficient forces splitting before a uniform valuation is reported. This gives a reproducible algebraic description without selecting approximate complex roots.

## Logarithmic execution through resonances

After a supported local gauge, write the equation as Y'=(R/s+sum Aj s^j)Y. A Frobenius ansatz combines an algebraic exponent rho, a finite power series and divided logarithmic powers. Its coefficients satisfy a coupled recurrence:

$$
((\rho+k)I-R)v_{k,l}+v_{k,l+1}
=\sum_{j=0}^{k-1} A_j v_{k-1-j,l}.
$$

Solving each log level separately can stop at a positive resonance because the coefficient matrix becomes singular. The new engine solves the entire log block at each power simultaneously. It searches a declared finite log-degree range, fixes free coordinates deterministically, records the resolved resonance orders, and replays every coefficient of the differential equation through the requested truncation.

At Legendre infinity, exponent -1/2 with seed (0,1) encounters a positive resonance at power one. The previous nonresonant recursion reported the obstruction. The new block recursion completes order 12 with a logarithmic term and records resonance order one. A forced log-degree-zero request remains incomplete; the compiler does not hide the missing term.

Algebraic coefficient algebras are retained throughout the recurrence. These results are finite formal identities. They do not supply an analytic remainder estimate, a convergent continuation algorithm, or a marked integral monodromy matrix. Initial eigenvectors, gauge, exponent and requested precision remain part of the mathematical input and result.

## Conjugate branches at ordinary nodes

For an ordinary double root a at t=alpha, require P(a,alpha)=P_x(a,alpha)=0 and both P_xx and P_t to be units. The collision is transverse in the parameter direction. After t=alpha+r², adjoining kappa with kappa²=-2P_t/P_xx gives the two initial branch slopes. Exact Hensel recursion determines successive coefficients:

$$
x_\pm(r)=a\pm\kappa r+\sum_{k\geq2} b_{\pm,k}r^k.
$$

The implementation first identifies the unique double root through a linear gcd. It retains alpha in its algebra, adds the slope algebra, derives one branch and obtains the other by slope conjugation. The substituted defining polynomial vanishes through the recorded order. Multiple colliding pairs, tangential discriminant contact and higher singularities require further methods.

For P=x⁵-x+t, the degeneration parameter satisfies 3125alpha⁴-256=0 and the collision coordinate is a=5alpha/4. The four algebraic nodes are handled together. Their second branch coefficient is exactly 1/4 on both slopes; the corpus executes through branch order eight. This links the collision equation to actual local polynomial roots rather than merely recording a discriminant zero.

## Verified ramified smooth models

A centered binomial family y²=(x-h(t))^m+c(t), with m=3,5,7, admits a particularly transparent local normalization. Let v be the order of c in the selected finite or infinite parameter chart. Choose e so both ev/m and ev/2 are integers. Substituting x=h+s^(ev/m)u and y=s^(ev/2)w gives w²=u^m+c/s^(ev). The remaining coefficient is a unit, so the central fibre is smooth in characteristic zero.

The implementation chooses the least e satisfying these integrality conditions, replays the full polynomial substitution and independently derives the normalized connection. It checks that connection against the unit's logarithmic derivative and verifies regularity with zero residue. Minimality refers to this scaling construction, not all possible stable-reduction models.

For x⁵+t at zero, e=10 and the powers of x and y are 2 and 5. At parameter infinity they are -2 and -5. For x⁵+t², e=5 suffices. The corpus also constructs the smooth chart for x⁵+t²+1 at the algebraic roots of alpha²+1, with e=10. More general collisions and stable models remain separate work.

## Actual finite symmetries and quotient function fields

SymmetryCurve accepts a smooth hyperelliptic polynomial P of degree 3 through 8, rational parameter coefficients, and optionally a squarefree algebraic coefficient extension. A generator consists of a nonsingular Möbius matrix and a y multiplier. For source genus g, its action is x'=(ax+b)/(cx+d), y'=lambda y/(cx+d)^(g+1). The program verifies the exact curve identity before accepting the action and closes the supplied group.

This is verification and execution of supplied symmetries, not classification of every automorphism. The complete group is closed within an explicit limit. Coefficient fields may include cyclotomic roots, so an order-five action is checked in its actual algebra rather than rounded complex numbers.

For the faithful action H on x, the compiler searches an orbit trace or orbit norm u. It requires invariance and deg(u)=|H|. Since [K(x):K(u)]=deg(u), and Artin's fixed-field degree is |H|, this proves K(x)^H=K(u). No arbitrary ansatz is accepted merely because it looks symmetric.

If the full curve group contains the hyperelliptic involution, its fixed field is K(u) and the quotient has genus zero. Otherwise a weighted orbit trace supplies an invariant anti-sheet coordinate v=y h(x). The compiler reconstructs v² as a rational function of u, removes square factors, and checks the normalized quotient equation w²=q(u) directly on the source. The full fixed curve field follows from the two sheet conjugates over the verified fixed x field.

Polynomial reconstruction is attempted first. A rational fixed-field reduction supplies the rational case over rational parameter coefficients; a bounded exact rational reconstruction is retained over algebraic coefficients. Successful identities are exact. A reconstruction-budget failure is not evidence that a quotient does not exist.

## Independent de Rham engines and executable quotient systems

The new PolynomialCurve engine handles odd and even degrees 3 through 8, including nonmonic leading coefficients. For even degree it removes residues at the two points at infinity, producing a compact-curve de Rham basis rather than a punctured-curve basis. It independently reduces differentials modulo d(R/y), derives the connection and computes the continuous residue pairing. Regression tests compare it to the earlier odd and even engines.

Pulling back each quotient differential gives a rational differential on the source. The compiler returns its exact cohomology coordinates and primitive term, checks full rank, and verifies the parameter-dependent intertwining identity. With row conventions for pulled-back bases, that identity is:

$$
T'+TA=BT.
$$

Here A is the source connection and B the independently derived quotient connection. The invariant projector's image equals the pullback image. A selected quotient observable can then receive its own minimal universal differential operator. Minimal means the first exact dependence of derivative rows on the complete period module; a particular cycle can satisfy a smaller equation.

The corpus verifies eight quotients: both lifts of a reciprocal genus-two family; genus-one and genus-two quotients of a reciprocal genus-three family; reflection of an even sextic; an order-three Möbius example; an order-five cyclotomic example; and reciprocal symmetry conjugated by a translated coordinate. Genus-zero cases have no first de Rham period system. The genus-three elliptic quotient has a first-order selected observable in the recorded family, while the other nonzero examples have order two. Those orders describe the selected observable, not the whole quotient dimension.

## Geometric projectors and paired-cover Jacobian isogenies

Each verified curve automorphism induces an exact de Rham action by differential pullback and reduction. Averaging the complete group gives its invariant projector. The compiler checks idempotence, horizontality, preservation of holomorphic differentials and self-adjointness for the continuous pairing. These projectors have actual geometric origins, unlike an arbitrary solution of a differential endomorphism equation.

For one non-hyperelliptic involution sigma, also construct its other lift iota sigma, where iota is the hyperelliptic involution. Their quotients C+ and C- come with actual double-cover maps pi+ and pi-. The compiler checks complementary orthogonal projectors, full cohomological pullback rank and complete holomorphic rank. The quotient genera sum to the source genus g.

Define F from Jac(C) to Jac(C+) times Jac(C-) by the two norm maps; define G in the reverse direction by the sum of pullbacks. The standard degree-two norm identity gives pi* pi_*=1+deck. Since iota acts as -1 on Jac(C), the two terms add to multiplication by two. Cross terms vanish: their source sector is anti-invariant under the other involution, so the cross homomorphism equals its negative; homomorphisms of abelian varieties are torsion free. Thus:

$$
GF=[2],\qquad FG=[2].
$$

The actual quotient maps induce algebraic homomorphisms, and full holomorphic rank makes them isogenies. Under the canonical principal polarizations, norm and pullback are dual. Consequently deg(F)=deg(G), while their product is deg([2])=2^(2g). Both isogenies have degree 2^g, and their kernels are annihilated by two.

The corpus certifies degree four for the genus-two pair and degree eight for the genus-three pair. This is a specific Jacobian decomposition proved from verified covers, ranks and standard norm identities. It is not a factorization inferred from a differential projector alone. Explicit torsion coordinates, integral kernel generators, automatically marked cycle matrices and a general Jacobian-factorization algorithm are not supplied.

## A useful arithmetic obstruction to false splitting

For the centered binomial curve y²=x^m+c, x->zeta_m x is an actual curve automorphism. The centered de Rham basis has the distinct nontrivial cyclic characters. A rational Betti projector commuting with this integral action must select complete rational Galois orbits of characters. Equivalently, the characteristic polynomial of the action on its image must have rational coefficients.

The compiler moves a candidate differential projector to the centered frame, verifies commutation, extracts its selected characters, and computes their characteristic polynomial in the exact cyclotomic algebra. A nonrational coefficient is an explicit obstruction. For y²=x⁵+t, the two rank-two filtered horizontal projectors select characters {1,4} and {2,3}. Neither set is closed under the Galois units modulo five, whose nonzero orbit is {1,2,3,4}. Both return RATIONAL_BETTI_OBSTRUCTION.

The identity projector is compatible with this necessary check. Compatibility does not prove an algebraic correspondence exists. A noncommuting projector remains unresolved by this test. Families without the supported cyclic symmetry return the explicit unsupported status. In particular, the calculation does not classify all rational Hodge substructures or prove general Jacobian simplicity.

## Persistent objects, replay and reproducibility

The catalogue now has fifteen persistent kinds. differential_extension stores an immutable algebra definition; symmetry_curve stores the polynomial and supplied action. Both recompile from a cold SQLite database. CurveFamily exposes the new local, nodal, smooth-model and arithmetic-obstruction queries. The JSONL service exposes their allowlisted operations and the standalone tensor_primitive request. Malformed requests are isolated without terminating subsequent service operations.

Run the development script from the repository root:

```sh
PYTHONPATH=python python python/develop_algebraic_curve_extensions.py
PYTHONPATH=python python -m unittest discover -s python/tests \
  -p test_algebraic_curve_extensions.py
PYTHONPATH=python python -m perfectpower service \
  --database /tmp/pp-algebraic.sqlite \
  < receipts/algebraic_curve_extensions/service_requests.jsonl
```

The corpus contains exact field witnesses, two full tensor models, six finite algebraic degeneration locations, nodal branches through order eight, the Legendre infinity jet through order twelve, three smooth ramified models, eight finite-action quotients, two paired-cover Jacobian isogenies, two rational Betti obstructions, and a twenty-three-request service replay. summary.json gives machine-readable scope and counts. timings.json records this machine's observations rather than a general performance claim. The interactive workbench displays the computed packets and the exact cyclotomic orbit obstruction; it performs no unrecorded numerical geometry.

The focused tests include field and split étale Hilbert–90, invalid automorphism rejection, nonunit splitting, shared-generator tensor products, algebraic collision residues, positive resonance, both node branches, independent old/new de Rham comparisons, even-degree infinity residues, genus-three quotient maps, cyclotomic coefficients, paired-cover ranks and service persistence. The separate validation receipt records the complete regression outcome and skips. The mathematical identities are exact Python calculations; this release adds no newly compiled Lean theorem.

## Research targets enabled by this release

An algebraic-curve researcher can now study a degeneration at all conjugate parameter values in one calculation, trace its branch separation into a differential residue, and execute the formal system without choosing approximate roots. A symmetry researcher can start from a verified Möbius action, obtain its quotient polynomial, inspect the exact pullback sector, and execute the smaller observable system. A researcher investigating apparent differential decompositions can distinguish geometric group-average projectors from splittings blocked by cyclotomic rationality.

The next substantial targets are broader stable models with several simultaneous collisions, general finite-action quotient composition, explicit integral kernel and cycle marking for the paired covers, and descent tests beyond scalar Hilbert–90. The existing multi-parameter family engine and the three-derivation algebra layer provide the pieces for algebraic local charts with several deformation directions; this release does not yet fuse all those pieces into a universal multi-parameter degeneration compiler. Rigorous numerical continuation needs independent analytic bounds. These are concrete extensions of executable objects rather than claims that the remaining geometry has already been solved.

## Sources and mathematical provenance

J. S. Milne, Fields and Galois Theory, https://www.jmilne.org/math/CourseNotes/FT.pdf, especially cyclic Hilbert–90 and Kummer theory, finite étale algebras and the fixed-field/rational-function perspective. The full source is linked for reference; the algebraic formulas and implementation explanations here are our own derivations.

Keith Conrad, Separability II, https://kconrad.math.uconn.edu/blurbs/galoistheory/separable2.pdf, Appendix B on unique extension of derivations to separable algebraic extensions.

J. S. Milne, Jacobian Varieties, https://www.jmilne.org/math/xnotes/JVs.pdf, for the Abel–Jacobi construction and canonical principal polarizations. The paired-cover norm calculation and degree argument are presented explicitly above.

E. Kani and M. Rosen, Idempotent relations and factors of Jacobians, Mathematische Annalen 284 (1989), 307–327, https://eudml.org/doc/164555; and S. Reyes-Carocca and R. E. Rodríguez, A generalisation of Kani–Rosen decomposition theorem for Jacobian varieties, https://arxiv.org/abs/1702.00484. Actual finite covers are the geometric prerequisite for these decomposition principles.

The preceding repository monographs CURVE_FAMILIES_MONOGRAPH.md, CURVE_STRUCTURE_MONOGRAPH.md and CURVE_RESEARCH_MONOGRAPH.md supply the established family connections, deformation charts, continuous pairing, local gauges and marked simplicial interfaces extended here. Source files and receipts are included in the complete repository archive.
