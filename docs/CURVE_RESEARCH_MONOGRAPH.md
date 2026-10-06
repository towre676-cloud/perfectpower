# Projective curve research and exact local execution

## A connected research program

This extension joins six previously separate questions: what a polynomial family changes geometrically, how its differential system executes near a degeneration, whether a rational quotient explains a smaller system, which horizontal endomorphisms preserve its holomorphic filtration and polarization, how an explicitly marked surface map acts on integral cycles, and how all of this changes when several parameters move simultaneously. The core uses exact standard-library arithmetic. One polynomial definition supplies multiple explanations; a numerical mesh is not substituted for continuous de Rham cohomology.

The delivered interfaces are projective_deformation, CurveFamily.local_analysis, CurveFamily.frobenius_jet, CurveFamily.de_rham_pairing, CurveFamily.horizontal_projectors, discover_rational_quotients, verify_rational_quotient, simplicial_cycle_map and the persistent MultiCurveFamily object. The catalogue now has thirteen kinds. Existing one-parameter definitions and period execution remain compatible. New exact computations retain explicit degree, coefficient-size and algebra-work budgets.

The contribution is executable integration of established constructions. A projective tangent chart is not a global moduli classification, a formal jet is not a rigorous numerical enclosure, an algebraic filtration test is not a rational Hodge structure, and a simplicial map must still be matched to the intended algebraic curve map. Those distinctions determine what another researcher can actually use.

## Full projective motion of the branch polynomial

An odd-degree affine model distinguishes a branch point at infinity. To permit that point to move, homogenize the branch polynomial to even degree d=2g+2. Write F(X,Z)=Z^d P(X/Z). Binary forms of degrees four, six and eight are supported, including affine degree d-1 with a single branch at infinity. Generic repeated roots are rejected. The four orbit directions comprise the three projective coordinate generators and overall form scaling. In the affine x chart they are

```text
P_x,   2 x P_x-d P,   d x P-x^2 P_x,   P.
```

The compiler chooses four independent coefficient rows, solves for the coordinate-flow coefficients and subtracts their orbit contribution from the parameter derivative. Its residual vanishes at those pivot rows and has d-3 independent chart coordinates. Every coefficient identity is exact. The quotient is the full PGL(2) tangent quotient of the binary branch form, including the form scaling that can be absorbed in a local change of y.

For F=X^4+(Z+tX)^4 the defining polynomial has a varying leading coefficient and a genuinely moving projective chart. The essential tangent is zero because the family is obtained by the substitution Z to Z+tX. For x^4+x+t it is nonzero. This example exercises a projective direction absent from a monic affine translation-and-scaling interface. On the older odd-degree chart, the projective quotient restricts consistently to its affine quotient: insisting that infinity remain a branch point removes that extra chart direction.

A nonzero pivot minor defines the chosen tangent chart. Its zeros are not automatically singular fibres. Coordinate-only motion describes a local integrated projective flow; no global rational trivialization, exhaustive automorphism classification or integer-coordinate preservation follows from that packet.

## Exact connections in several parameters

MultiCurveFamily accepts one through three named parameters and monic x degrees three, five and seven. Input coefficients are exact rationals or sparse parameter polynomials, with each monomial of total degree at most eight; explicitly represented ratios of those inputs are also supported. The coefficient field is Q(t_1,...,t_r), implemented as an iterated rational-function tower. Polynomial Euclidean gcd over the preceding field normalizes each layer. This supplies cancellation and mixed derivatives without an optional symbolic algebra package or expression evaluation.

For each parameter t_a the compiler solves the simultaneous polynomial reductions

```text
-x^i P_(t_a)/2 = sum_j A_(a,ij) x^j P
                  + R_(a,i)' P - R_(a,i) P_x/2.
```

All right-hand sides share one elimination. Sparse systems use field Gaussian elimination; denser systems use fraction-free Bareiss elimination followed by back substitution. Keeping polynomial minors until the final dense solve limits avoidable intermediate denominators, although the tower arithmetic can still be expensive. Every identity is replayed. The resulting period system is partial_a Pi=A_a Pi. For each pair of parameters the compiler then verifies the exact flatness identity

```text
partial_b A_a - partial_a A_b + A_a A_b - A_b A_a = 0.
```

Thus simultaneous parameter motion is compatible at the level of the continuous differential module. No inference about path independence around the discriminant is made; flat local connections can have nontrivial global monodromy.

For y^2=x^3+a x+b, with Delta=-4a^3-27b^2, the independently checked matrices are

```text
A_a = (1/Delta) [[a^2, -9b/2], [-3ab/2, -a^2]],
A_b = (1/Delta) [[9b/2, 3a], [a^2, -9b/2]].
```

Specialization at rational parameter tuples retains the exact discriminant and rejects singular fibres. Before evaluation, Gauss's lemma clears coefficient denominators and removes primitive polynomial contents throughout the tower. A pole of an intermediate coefficient is therefore not mistaken for a pole of the complete rational function; actual poles and indeterminate specializations remain rejected. A directional observable compiles its minimum universal scalar order while the other parameters are held fixed. Partial root velocities are obtained by the same polynomial inverse of P_x modulo P. The deformation query computes all projective tangent directions and their generic rank together, distinguishing the number of named inputs from the number of essential shape directions. The binomial families x^5+a+b and x^3+a+b+c also exercise multiple parameters with a shared coordinate-only shape change.

The implementation has algebraic budgets rather than a promise that every symbolic family finishes quickly. Generic multivariate elimination can create large intermediate coefficients. Compilation failure returns no completed family; the retained input and explicit limits permit a larger or more structured subsequent calculation. Numerical transport in several parameters is separate work.

## Multiple-root fibres and parameter infinity

The previous collision compiler covered only simple finite discriminant roots. local_analysis instead specializes at any supplied rational parameter, including fibres with repeated discriminant roots, or uses the parameter-infinity chart s=1/t. It transforms the full connection one-form: at infinity the new matrix is -A(1/s)/s^2. Exact Laurent division gives entry valuations and coefficient jets. The local discriminant order is computed independently.

The branch polynomial is also transformed. Removing its common lowest coefficient valuation gives a primitive coefficient limit. The packet distinguishes the raw discriminant valuation from that of the normalized binary form: removing a common valuation v subtracts (2d-2)v from the binary discriminant order. Exact squarefree decomposition reports every finite-root multiplicity, and the declared binary degree records the branch multiplicity at x infinity. This is the coefficient limit in the recorded x chart; a stable model can require further coordinate changes, base changes or blowups. The program does not call every such limit a completed stable reduction.

If the current connection has higher poles, integral diagonal shears are sought by difference constraints. For G=diag(s^w_i), the transformed entry is s^(w_i-w_j) A_ij and the diagonal gains w_i/s. The conditions valuation(A_ij)+w_i-w_j >= -1 are solved by a finite shortest-path relaxation. A negative cycle or a diagonal pole of order greater than one blocks this class of gauge. A rejected diagonal search does not prove that the underlying geometric connection is irregular: a more general meromorphic gauge may still be Fuchsian.

The Legendre family y^2=x(x-1)(x-t) has repeated discriminant roots at zero and one. Both local charts have rank-one square-zero residues. At parameter infinity the compiler records a primitive coefficient limit with branch multiplicity two at x infinity and residue characteristic polynomial lambda^2-1/4 in its supplied frame. The family x^5+t at zero has a fivefold polynomial root and diagonal fractional exponents; its first differential has exponent -3/10. These cases make local execution available beyond transverse ordinary nodes.

## Executing logarithmic Frobenius jets

In a supported Fuchsian frame write A(s)=R/s+sum_k A_k s^k. A seed in a generalized eigenspace of R supplies a logarithmic leading term. The representation uses factorial-normalized powers of log(s):

```text
Y_new = s^rho sum_n s^n sum_l v_(n,l) log(s)^l/l!.
```

At order zero, v_(0,l)=(R-rho I)^l seed, and the final vector must terminate within the declared logarithmic bound. For n positive the exact recurrence is

```text
((rho+n) I-R) v_(n,l) + v_(n,l+1)
    = sum_(k=0)^(n-1) A_k v_(n-1-k,l).
```

The engine solves from the highest logarithmic degree downward whenever the coefficient matrix is invertible. All computed coefficients are replayed against this recurrence. A positive resonance is reported with its order and the completed prefix; it is never silently divided away or presented as a complete requested jet. Resolving arbitrary resonances, ramified algebraic parameters and convergent error enclosures remains separate work.

For the Legendre analytic seed (1,0) at zero, the first coordinate's coefficients agree exactly through order twelve with binomial(2n,n)^2/16^n. The other seed (0,1) produces a nonzero logarithmic leading coefficient. At infinity a seed with exponent 1/2 executes successfully, while the exponent -1/2 example explicitly reports resonance at order one. These are finite formal solutions of the derived continuous period system. Selecting the combination corresponding to a particular marked period still requires its initialization data.

## Rational quotient maps beyond translated reflection

The general map certificate accepts u=N(x)/D(x) and v=y S(x)/T(x), with coefficients in Q(t). For a declared target degree it solves for the target polynomial coefficients q_j by clearing denominators in

```text
P S^2 D^degree = T^2 sum_j q_j N^j D^(degree-j).
```

The coordinate u must be nonconstant, the target must have smaller positive genus, and both source and target must be generically smooth. All coefficients of the map identity are checked exactly. The packet records its rational-map degree, exceptional affine denominators and holomorphic differential pullbacks. A finite supplied candidate list is searched completely within its budgets; that is not a classification of all rational covers.

Automatic discovery now includes reciprocal involutions of palindromic sextics, in addition to the translated reflection template. For

```text
P=x^6+x^5+2x^4+(3+t)x^3+2x^2+x+1,
u=x+1/x,
```

one has P/x^3=Q(u), where Q=u^3+u^2-u+1+t. The two maps v=y(x+1)/x^2 and v=y(x-1)/x^2 give

```text
v^2=(u+2) Q(u),   v^2=(u-2) Q(u).
```

Each is a degree-two map to an elliptic curve, arising from reciprocal symmetry rather than an affine reflection label. The rational branch at u=-2 or u=2 gives a cubic chart. With a=q'(e), set X=a/(u-e) and Y=a v/(u-e)^2. The resulting monic cubic has coefficients a^2 q_4, a q_3, q_2 and 1 after expansion around e. When these coefficients fit the polynomial family backend, the compiler derives and executes its elliptic connection and selected differential operator. Both demonstrated sectors have order two.

This produces actual quotient maps, unlike a differential projector alone. It does not automatically identify every exceptional point, search arbitrary rational-map coefficients, transfer an arbitrary original cycle marking, or infer a general Jacobian decomposition. The prior translated-even quotient class retains its independently checked four-dimensional connection splitting.

## The continuous de Rham pairing and filtered projectors

For a monic odd-degree hyperelliptic curve, the power basis has poles only at infinity and has no residues. Use the local coordinate x=z^-2 and y=z^-m sqrt(W(z)), with m=2g+1. Then omega_i=-2 z^(m-2i-3) W(z)^(-1/2) dz. A finite exact expansion supplies every term needed for the residue of a local primitive of omega_i multiplied by omega_j. This constructs the alternating, nondegenerate de Rham pairing J in the same basis as the connection.

The compiler checks both alternation and nondegeneracy, and verifies J'=A J+J A-transpose exactly. This is a continuous algebraic de Rham polarization calculation; no finite mesh Hodge matrix is identified with it. For genus one the chosen residue normalization gives J_01=4. Higher-genus entries can depend on the polynomial coefficients.

A bounded shared-denominator ansatz P(t)=sum_(k=0)^d P_k t^k/D(t), with d at most two, is searched for endomorphisms satisfying

```text
P' + P A-A P=0,   P(F^1) subset F^1,   P J=J P-transpose.
```

The first condition is horizontality. The second uses the actual holomorphic basis rows, not a supplied finite Hodge matrix. The third is self-adjointness for the residue pairing. Clearing denominators turns these into a rational linear system; its returned basis is complete within that ansatz. A recorded finite list of basis elements, complements and pair sums is then checked for nontrivial idempotents. The linear space is exhaustive within its declared bounds; the nonlinear idempotent search is only the declared candidate list.

For x^5+t the constant ansatz has a two-dimensional filtered polarized horizontal space and returns two complementary rank-two projectors. For x^5-x+t the same ansatz contains only scalar multiples of identity. The former result is deliberately not advertised as a split Jacobian: preservation of the holomorphic algebraic filtration and this pairing does not establish a rational Betti lattice or compatibility with complex conjugation. Differential projectors are candidates for further geometric explanation, and explicit quotient maps are stronger evidence when available.

## Exact integral maps on declared surface markings

simplicial_cycle_map accepts two oriented closed triangulations and an explicit target vertex for every source vertex. It constructs the maps on vertices, edges and faces, respecting orientations and collapsed simplices. A nonsimplicial image is rejected. Both chain identities are checked exactly.

Smith reductions of the vertex-edge and edge-face boundary matrices construct integral H1 bases and coordinate projections. Surface homology is checked to be torsion-free with rank twice the genus. The induced matrix comes from applying the actual edge chain map to each source basis cycle, then projecting into target homology. For each image, an integral two-chain witnesses the difference from its target basis expansion. The fundamental two-cycle supplies the map's signed degree.

A periodic 6-by-3 torus triangulation covering a 3-by-3 triangulation gives degree two and an integral H1 matrix with determinant two. Identity and orientation-reversing maps provide independent checks. This supplies actual integral topology once a simplicial marking is declared. The Smith basis is not claimed symplectic. A curve quotient still needs a compatible triangulation map before this certificate can identify its analytic periods; the program does not infer that map from a differential projector or a numerical nearest-vertex match.

## Reproduction and remaining mathematical work

Run the exact development corpus and the focused tests from the repository checkout:

```sh
PYTHONPATH=python python python/develop_curve_research.py
PYTHONPATH=python python -m unittest python.tests.test_curve_research
python -m perfectpower service --database /tmp/pp-research.sqlite \
  < receipts/curve_research/service_requests.jsonl
```

The receipts retain full projective identity packets, multivariate reductions and curvature matrices, local Laurent data and formal jets, rational quotient identities and elliptic operators, de Rham pairing and projector spaces, and integral simplicial maps with Smith and boundary witnesses. The README describes these as current capacities with their precise scopes.

Remaining work includes stable reduction at general algebraic degeneration parameters, arbitrary positive-resonance execution, non-diagonal Fuchsian reduction, integral markings for automatically discovered curve quotients, rational Betti and conjugate-filtration constraints on projectors, broader unconstrained map discovery, new kernel proofs and rigorous numerical continuation. The delivered mathematical objects make those obligations concrete; they do not erase them by naming a differential reduction or a mesh.

Background sources include Köck and Tait, On the de-Rham cohomology of hyperelliptic curves, Research in Number Theory (2018), https://doi.org/10.1007/s40993-018-0111-4; and Ramses van der Toorn, Tandem Recurrence Relations for Coefficients of Logarithmic Frobenius Series Solutions about Regular Singular Points, Axioms 12(1), 32 (2023), https://doi.org/10.3390/axioms12010032. The implementation's displayed binary-form, residue and quotient identities are derived and replayed directly from its defining polynomials.
