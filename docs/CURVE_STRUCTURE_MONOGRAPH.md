# Explaining polynomial structure through curve geometry

## A research object with several interpretations

PerfectPower now connects coefficient deformations, simultaneous root velocities, nodal residues and explicit elliptic quotient maps. The defining polynomial remains attached to every construction. The goal is to explain which changes alter a curve, which change its coordinates, which roots participate in a degeneration, and why a higher-genus period system can reduce to simpler systems.

Three new queries on CurveFamily produce deformation, root_motion and collisions packets. A twelfth catalogue kind, elliptic_quotient, compiles a translated-even sextic into two elliptic quotient systems and an independently derived four-dimensional genus-two connection. Discovery and construction are also service operations. All exact core operations use the Python standard library. Numerical roots and period execution remain optional NumPy/SciPy operations.

The work joins established mathematics: deformation quotients, algebraic de Rham reduction, Gauss-Manin connections, Picard-Lefschetz degenerations and elliptic covers of genus-two curves. The delivered contribution is their executable integration in PerfectPower, with exact explanation packets and explicit original-coordinate arithmetic. No worldwide priority claim is established.

## Coordinate motion versus shape motion

For a monic polynomial P of degree m, an infinitesimal translation of x generates P_x. An infinitesimal scaling, with the y scaling needed to keep P monic, generates x P_x-m P. The deformation query works over Q(t), selects two coefficient rows with a nonzero orbit minor, and projects P_t modulo these two directions:

```text
P_t = a(t) P_x + b(t) (x P_x-m P) + E(x,t).
```

The essential tangent E has zero coefficients in the two selected pivot rows. Every polynomial identity is checked exactly. Its remaining m-2 coordinates describe the tangent class in this affine chart. A zero essential tangent means the family is locally trivial under an integrated affine coordinate flow. It does not produce a global rational isomorphism, identify every projective equivalence, or preserve integer coordinates.

The packet records the pivot minor. A pole of this particular coefficient chart is not automatically a degeneration of the curve. The analysis distinguishes the chart's domain from the family discriminant. In the odd-degree model, the branch point at infinity is distinguished; full projective branch-coordinate changes require a binary-form extension.

For P=x^5+t the exact identity is 5t P_t+x P_x-5P=0. For P=x^5-x+t, P_t has a nonzero class modulo the affine orbit. These two families therefore have different geometric interpretations despite both varying only their constant term.

## Scaling explains a differential reduction

The compiler recognizes P=(x-h(t))^m+c(t). It retains the exact center and constant, the change of differential basis, and the local substitution

```text
x=h(t)+c(t)^(1/m) u,  y=c(t)^(1/2) v,  v^2=u^m+1.
```

The centered differential (x-h)^i dx/y has scaling weight (i+1)/m-1/2. Its connection is diagonal with that weight times c'/c. The compiler checks the full basis identity T'+T A = A_centered T, rather than merely comparing one observed scalar order. Fractional powers need local branch choices; finite marking monodromy can remain even though the shape is fixed.

For x^5+t the four weights are -3/10,-1/10,1/10,3/10. The first observable satisfies 10t F'+3F=0. The same explanation is recovered from an expanded translated quintic (x-t)^5+1+t. A first-order observable does not reduce the genus of the underlying curve.

## One polynomial encodes every simple-root velocity

On a smooth fibre P_x is invertible in Q(t)[x]/P. Extended Euclidean polynomial arithmetic constructs that inverse and the unique degree-less-than-m representative V=-P_t/P_x modulo P. The packet includes the inverse and the replay identity:

```text
P_t+P_x V = Q(x,t) P.
```

Every simple root r(t) consequently satisfies r'=V(r,t). The construction needs no radical expressions or numerical root ordering. It gives simultaneous polynomial root motion, not a certified braid computation.

For x^5-x+t, the result is

```text
V=(625 t^3 x+500 t^2 x^2+400 t x^3+320 x^4-256)
  /(3125 t^4-256).
```

The denominator is the same discriminant factor that controls the period connection. This supplies an explicit common algebraic source for root motion and period response. The workbench evaluates V at approximate roots, while keeping the exact identity separately available.

## A collision coordinate appears inside the connection residue

The collisions query covers every simple finite discriminant root. It removes repeated discriminant factors and reports those omitted factors explicitly. The remaining squarefree polynomial represents the parameters simultaneously in a finite Q-algebra. This algebra can be a product of fields. A failed division by a nonunit yields a factor witness, and the calculation splits the modulus before continuing. A reducible squarefree polynomial is never silently treated as a field.

On each component, an exact polynomial gcd of P and P_x gives the common root a. The calculation checks P(a)=P_x(a)=0 and invertibility of P_xx(a) and P_t(a), identifying a transverse ordinary node. Multiplication by the component modulus cancels the simple connection poles; evaluation and division by the modulus derivative produces the residue. Matrix rank, its square and the collision evaluation vector are calculated in the same exact algebra.

For x^5-x+t, a^4=1/5 and t_c=4a/5. The connection residue factors as

```text
N = column(1,a,a^2,a^3)
    row(-3/40,-a^3/8,a^2/8,3a/8).
rank(N)=1, N^2=0.
```

The residue image is exactly the evaluation line at the colliding root. This relates the polynomial collision location to a specific direction in de Rham period space. It explains local unipotent behavior of a simple nodal degeneration. Converting this description into an exact integral homology monodromy matrix still requires a marked integral cycle basis. A shrinking homology cycle need not have a period tending to zero when its differential develops a pole in the singular limit.

The example P=(x^2-t)(x^3-x+t-2) forces an actual quotient-algebra split. Its three simple discriminant roots separate into a rational component and a quadratic component, each with rank-one square-zero residue. Repeated discriminant roots from intersections of the polynomial factors remain visible in the omitted factor. The Legendre family's repeated discriminant roots are likewise reported as requiring separate local analysis; they are not mislabeled smooth.

## Discovering a hidden reflection

For a monic sextic, a translated reflection must be centered at h=-coefficient(x^5)/6. Substitution x=z+h therefore gives a complete test for this kind of symmetry: the coefficients of z,z^3,z^5 must vanish. discover_elliptic_quotients returns these exact conditions, whether they hold identically, and the common polynomial describing possible isolated symmetry specializations.

For x^6+t x^3+1 the reflection occurs only at t=0. For x^6+x+1 there is no finite parameter locus to recover. Expanded translated-even models are recognized without being supplied a symmetry label. This is a complete translated-reflection test, not a complete classification of all genus-two automorphisms or elliptic covers.

## Two elliptic curves inside one sextic

For the supported model

```text
y^2=z^6+A(t) z^4+B(t) z^2+C(t),  z=x-h(t),
Q(u)=u^3+A u^2+B u+C,
```

the two quotient maps are explicit:

```text
E1: v^2=Q(u),                 u=z^2, v=y.
E2: w^2=u Q(u),               u=z^2, w=z y.
E2 cubic: Y^2=X^3+B X^2+A C X+C^2,
          X=C/z^2, Y=C y/z^3, z!=0.
```

Generic smoothness requires C nonzero and disc(Q) nonzero. The exact discriminant identities are disc(P)=-64 C disc(Q)^2 and disc(E2 cubic)=C^2 disc(Q). A zero of disc(Q) generally produces paired collisions in the original sextic, while both elliptic sectors expose their own degenerations. Multiple and intersecting loci still need the appropriate local analysis.

The construction operation accepts a desired first cubic quotient Q and a polynomial center h, then returns the expanded sextic specification. Registering that specification checks generic smoothness and builds the geometry and differential systems. The second quotient is determined by this construction; arbitrary pairs of elliptic curves are not asserted compatible.

## The residue-free genus-two connection

The naive even-degree power basis contains residue-bearing forms at its two points at infinity. The quotient compiler instead uses

```text
eta_0=dz/y, eta_1=z dz/y, eta_2=z^3 dz/y,
eta_3=(z^4+A z^2/2) dz/y.
```

The A z^2/2 term cancels the residue of z^4 dz/y. The form z^2 dz/y is not used as an independent residue-free class. The second elliptic pullback has the explicit exact correction

```text
d(y/z)=(2z^4+A z^2-C/z^2) dz/y,
X dX/Y = -4 eta_3 + 2 d(y/z).
```

The four elliptic pullbacks, modulo that exact differential, are chi=(2 eta_1,2 eta_2,-2 eta_0,-4 eta_3). The compiler independently solves four polynomial de Rham reduction identities in the eta basis, including parameter derivatives of the basis itself when A varies. It then checks T A_eta = blockdiag(A_E1,A_E2) T exactly. Thus the two elliptic blocks are explained by actual maps and differential pullbacks.

Each sector can compile its selected scalar observable and execute a marked period path using the previous family engine. The demonstrated sectors each have order two. A quotient period is not automatically the period of an arbitrarily selected original genus-two cycle; transferring a particular mark requires the corresponding cycle map.

## Rational lifts retain arithmetic information

point_image checks a supplied rational sextic point and returns both quotient images. At z=0 the reciprocal cubic map is recorded as a point at infinity rather than divided by zero. rational_lifts gives every rational point over one declared affine E1 point or E2 quartic point. It checks whether u has a rational square root, handles the exceptional u=0 fibre separately, and retains integrality in the original x,y coordinates.

A quotient point can have an empty rational fibre because u is nonsquare. A rational lift can have nonintegral x because the recovered center has a denominator. These exact fibre calculations are useful arithmetic restrictions; they are not a global rational-point or integer-point census.

## Executable research interface and visual inspection

The JSONL service adds deformation, root_motion and collisions to curve_family. The elliptic_quotient kind exposes summary, evidence, specialize, observable, collisions by sector, root_motion, period_path by sector, point_image and rational_lifts. discover_quotients and construct_quotient are service operations. Private reduction methods remain outside the query interface. Definitions survive SQLite restart.

The offline structure_workbench.html displays 183 recorded root samples across the genuine quintic deformation, the scaling quintic and a translated sextic. Shape coordinates freeze the isotrivial root configuration or expose the sextic reflection. The generic quintic displays its collision locations alongside the exact residue explanation. Root locations, velocities and plotted collision markers are numerical approximations; the explanation packets are exact. The controls select recorded data and do not run a new symbolic computation.

The development script additionally records 42 elliptic-sector period samples. Matrix continuation, scalar continuation and direct endpoint contour integration are compared independently. Their numerical differences are consistency measurements with no certified error bound.

## Reproduction and remaining research

```sh
export PYTHONPATH=python
python python/develop_curve_structure.py --output /tmp/pp-structure
python -m unittest discover -s python/tests -p test_curve_structure.py
node scripts/check_structure_workbench.cjs
python -m perfectpower service --database /tmp/structure.sqlite \
  < receipts/curve_structure/service_requests.jsonl
make test
```

The focused tests replay known root velocities and residues, compare reductions against independent rational linear systems after specialization, exercise nonunit splitting, test symmetry loci and inverse construction, and check rational lifts, persistence and nontrivial numerical period execution. CurveFamily's public parameter degree cap is now eight. Quotient transformations can raise parameter degree internally, subject to the same declared degree, bit and work budgets. Budget exhaustion returns an error rather than a partial mathematical answer.

The subsequent [projective research extension](CURVE_RESEARCH_MONOGRAPH.md) implements full binary-form projective tangent quotients, exact local Laurent charts and finite Frobenius execution at rational multiple-root fibres and infinity, integral homology maps of explicitly supplied simplicial maps, reciprocal rational quotient discovery, filtered polarized horizontal-projector searches and connections in up to three simultaneous parameters. These constructions retain their declared scopes: general stable reduction, positive-resonance resolution, automatic algebraic cycle markings and rational Betti constraints remain open. The finite Hodge matrices and numerical smooth meshes elsewhere in the repository are not identified with this continuous de Rham structure. A general algebraic correspondence or Jacobian decomposition cannot be inferred from a differential projector alone. New kernel proofs and rigorous numerical continuation also remain separate work.

## Mathematical precedents

Hossein Movasati, Calculation of mixed Hodge structures, Gauss-Manin connections and Picard-Fuchs equations, https://arxiv.org/abs/math/0412235.

Pierre Lairez, Computing periods of rational integrals, https://arxiv.org/abs/1404.5069.

Pierre Lairez, Eric Pichon-Pharabod and Pierre Vanhove, Effective homology and periods of complex projective hypersurfaces, https://arxiv.org/abs/2306.05263.

Pascal Molin and Christian Neurohr, Computing period matrices and the Abel-Jacobi map of superelliptic curves, https://arxiv.org/abs/1707.07249.

Nils Bruin and Kevin Doerksen, The arithmetic of genus two curves with (4,4)-split Jacobians, https://arxiv.org/abs/0902.3480. Its discussion of elliptic covers and (2,2)-splittings provides background for the two quotient maps used here.
