# One exact certificate language for curve geometry and integer systems

This push connects two previously separate PerfectPower fronts. Exact bivariate
polynomial certificates now support both local smooth-curve metric bounds and
arithmetic constraint simplification. The same rational tensor representation
can prove that a chart metric stays between two prescribed scales, that a
polynomial combination of equations cannot vanish on a region, or that every
zero lies on specified coordinate faces. Selected packets are exported as actual
Lean data and checked by the kernel. A structural theorem supplies a local
metric envelope for an infinite family at every positive genus, avoiding a
prohibitively large dense polynomial expansion.

The new machinery is a repository capability, not a claim that Bernstein
polynomials, hyperelliptic charts, geometric-series bounds or ideal identities
are new mathematical discoveries. Its useful combination is that the geometry
and arithmetic layers now share a certificate representation, while strict
exclusion, necessary residual domains, exact zero strata and complete integer
models remain distinct outcomes.

## What has been closed, and at what scope

The earlier release had rational polyhedral Voronoi packets whose mathematical
witnesses were checked in Python. This release adds a native Lean checker for
explicit mesh, field, path and patch data. Three complete tetrahedron packets
are checked, including one with 64 leaves and 13 strict classifications. The
checker also has kernel-checked rejection examples for false radii and invalid
field gradients. These are concrete exported Python packets, not just hand
proofs of a patch inequality.

The smooth-curve layer now has exact local comparisons for the explicit
holomorphic-basis metric, including branch and infinity charts. There is a
parameterized Lean envelope for all curves y²=x^(2g+1)−x, g≥1, on a specified
small chart disk. Literal genus-one branch and finite-chart bounds are checked
through the tensor compiler. Larger-genus packets are replayed in exact Python
arithmetic, and the family theorem supplies their structural mathematical
counterpart without enumerating a genus-sized coefficient table.

This is not a global certified Voronoi solver for an arbitrary smooth curve.
Global atlas identification, compatible chart transitions, comparison of every
mesh face with the intended smooth geometry, and a Lean construction of the
actual polyhedral quotient length metric remain open. The native packet theorem
asserts acceptance by the explicit checker. Theorems extract its checked fields,
leaves, coverage and gradient inequalities; a complete semantic proof from this
JSON encoding to the surface's global length metric has not been supplied.
Period-normalized Bergman metrics and validated analytic periods are also
separate from the metric certified here.

## The common polynomial representation

A polynomial is encoded as a finite list of rational triples (i,j,c), representing
c x^i y^j. Duplicate monomials are combined exactly. The current implementation
limits individual coordinate degrees to 32, uses bounded coefficient and
endpoint sizes, and places explicit budgets on subdivision and compiler routes.
Reaching a work limit does not produce a false completeness claim.

For a rational rectangle [a,b]×[c,d], write

\[
x=a+(b-a)s,\qquad y=c+(d-c)t,\qquad 0\le s,t\le1.
\]

The normalized polynomial has the tensor representation

\[
F(x,y)=\sum_{i=0}^m\sum_{j=0}^n
c_{ij}s^i(1-s)^{m-i}t^j(1-t)^{n-j}.
\]

The stored coefficients include the usual binomial factors; the displayed basis
is intentionally unnormalized. If every coefficient is strictly positive, the
polynomial is strictly positive throughout the closed rectangle. At a boundary
point some basis functions vanish, but at least one survives in each coordinate.
Lean proves this fact rather than assuming that all basis functions are positive
at the boundary.

The producer computes the coefficients using rational binomial transforms. The
independent replay expands the supplied basis and compares the result with the
normalized original polynomial. It does not trust the producer's discovery
choices. Adaptive subdivision is represented by a complete binary tree of
rectangles. Supplied splits are checked explicitly and every unresolved leaf
is retained. Generated Lean proofs establish each positive leaf's literal
polynomial identity with `ring`, check the rational coefficient inequalities
with kernel reduction, and assemble coverage by cases on the split coordinate.
They use neither a supplied analytic premise nor `native_decide`.

## From individual equations to ideal separators

For simultaneous equations F₁=…=Fₖ=0, every polynomial combination

\[
S(x,y)=\sum_i W_i(x,y)F_i(x,y)
\]

also vanishes at every common solution. A positive or negative certificate for
S on a rectangle therefore excludes common solutions there. The multipliers
are polynomials, not merely constant weights. Replay checks the complete ideal
identity and the supplied box certificate. It never mistakes a positive witness
for S for a sufficient witness of an original equation.

The first automatic reduction divides a polynomial F by a relation
G=A y+B(x), with nonzero constant rational A. It obtains the exact identity

\[
F=QG+R(x).
\]

This substitutes the affine relation into the nonlinear equation while keeping
the original equations available for model recovery. Integer outputs still
require y=−B(x)/A to be integral; a denominator is not cancelled as an integer
image restriction.

For example, take F=y²−x³ and G=y−x−1. Exact division gives

\[
F-(y+x+1)G=1+2x+x^2-x^3.
\]

The remainder is strictly positive for 0≤x≤1. A kernel-checked certificate
therefore excludes the system on that interval with −10^100≤y≤10^100, without
searching y. The scale demonstrates independence from enumeration in the
eliminated coordinate; it is not an industrial benchmark or a speedup claim
against a surrounding SMT solver.

`compile_system` tries bounded affine-elimination, individual-equation and
leading-cancellation routes. It returns a proved exclusion when available,
otherwise necessary residual boxes. The route portfolio is a bounded heuristic;
it does not claim optimal separator discovery or general polynomial-system
completeness. The residual boxes are themselves checked against the certificate
leaves, so callers cannot silently replace them with a smaller unverified region.

## Exact zero strata from weak signs

Strict coefficient positivity is not the only useful outcome. If all tensor
coefficients are nonnegative, the sum is zero exactly when every active term is
zero. A coefficient is active in the open coordinate interval whenever its
basis function is positive; at a lower endpoint only index zero is active, and
at an upper endpoint only the final index is active. A weakly nonpositive tensor
has the same zero classification after negation.

The algorithm classifies nine coordinate strata: lower endpoint, open interior
and upper endpoint in each coordinate. It records exactly those strata whose
active coefficients are all zero. This is a complete real zero locus when the
tensor has one weak sign. A mixed-sign tensor remains unresolved. Open interiors
are explicit in the representation; they are never confused with closed boxes.
Lean's `tensor_zero_iff` proves the nonnegative-sum implication, and positive
support excludes the interior even when some coefficients are zero.

Combining this zero-face description with affine elimination yields complete
bounded integer models whenever the residual's zeros are confined to the two
x endpoints. The endpoint must be an integer, its unique affine y fibre must be
an integer, and every original equation is checked. The compiler retains all
models and declares unresolved cases explicitly. Its corpus has 144 power/affine
systems: 108 close by this route, while 36 remain unresolved. Independent
original-equation checks cover 1,440 bounded integer pairs. These counts are
coverage evidence for the constructed corpus, not estimates of application-wide
coverage.

For y²=x³ together with y=x, the only models are (0,0) and (1,1). The corresponding
complete equivalence over both the reals and integers is checked in Lean. The
coefficient-bearing relation 2y=x keeps its integer-image condition; a half-
integer endpoint fibre is not returned as an integer model.

## The smooth chart metric

The metric here is

\[
 ds^2=\sum_{j=0}^{g-1}|x^j dx/y|^2
\]

on a smooth squarefree hyperelliptic curve y²=P(x) of positive genus. It uses the
explicit algebraic differential basis. It is the metric already used by the
repository's unnormalized analytic component layer, rather than a canonical
period-normalized Bergman metric.

In a finite chart, its density is

\[
\rho(x)=\frac{\sum_{j=0}^{g-1}|x|^{2j}}{|P(x)|}.
\]

At a simple rational root b, divide P(x)=(x−b)Q(x) exactly and use x=b+t²,
y=t h(t), h(t)²=Q(b+t²). The density becomes

\[
\rho_b(t)=\frac{4\sum_{j=0}^{g-1}|b+t^2|^{2j}}{|Q(b+t^2)|}.
\]

This regularizes the apparent finite-chart pole. The compiler checks that b is
an actual simple root and certifies the remaining denominator on the entire
box, including t=0. Existence and analytic identification of a local square-root
branch are standard chart facts used in the mathematical interpretation;
`branch_equation` checks the equation transport algebraically. This release does
not formalize the full complex analytic chart construction in Lean.

For odd degree 2g+1, infinity uses x=t⁻² and the reversed polynomial evaluated at
t². The numerator is 4∑|t|^(4k), k=0,…,g−1. For even degree 2g+2, x=t⁻¹ gives
numerator ∑|t|^(2k). These formulae include the regular chart center at infinity.
The packet retains its exact coefficient and chart conventions.

Each density is N/sqrt(D), where N is a real bivariate polynomial and D is the
squared complex modulus of the denominator. The compiler certifies N>0, D>0
and the two polynomial gaps

\[
N^2-l^4r^2D>0,\qquad u^4r^2D-N^2>0.
\]

Lean then proves l²r<ρ<u²r. These are pointwise tangent comparisons against
constant reference density r. A tangent-speed theorem takes square roots, and
an interval-integral theorem transfers integrable speed bounds to whole
contained paths. Neither theorem replaces chart-contained paths with
unrestricted global geodesics.

`MetricBoxSpace` validates once and provides exact outward density brackets at
rational points, together with squared length bounds for straight segments
whose endpoints lie in the certified rectangle. Convexity keeps each segment
inside the box. The API labels those as path-length bounds, not global distance
bounds. Its integer square-root rounding can be refined without changing the
underlying chart certificate.

## A structural envelope for every positive genus

For P(x)=x^(2g+1)−x, the branch chart at zero and the infinity chart have the same
metric density:

\[
\rho_g(t)=\frac{4\sum_{k=0}^{g-1}|t|^{4k}}{|1-t^{4g}|}.
\]

The equality comes from the explicit branch/infinity formulae and reversal of
the differential basis. The reciprocal curve map uses a square root of −1;
`reciprocal_family` proves its algebraic equation transport over any field with
that square root. It does not confuse this symmetry with cancellation of a
noninjective polynomial outer map in integer arithmetic.

For g≥1 and |t|⁴≤r<1, geometric-series and triangle inequalities give

\[
\frac4{1+r}\le\rho_g(t)\le\frac4{(1-r)^2}.
\]

Consequently |t|²≤1/8 implies

\[
4(99/100)^2<\rho_g(t)<4(103/100)^2
\]

for every positive genus. The quarter-coordinate square lies inside that disk.
The theorem remains symbolic in g; it does not enumerate the differential basis
or expand the degree-dependent monomial. A checked specialization at g=10^100
exercises that property without constructing an astronomical coefficient list.
This is a parameterized local geometric theorem, not an integer-point
classification for those curves.

An initial dense genus-two tensor proof exceeded the local Lean memory budget.
The structural theorem replaces that expensive formalization route. General
metric packets remain available in Python, and the literal genus-one examples
show the general tensor proof compiler. The release does not present the
uncompiled dense genus-two expansion as a kernel proof.

## Native Voronoi packet replay

`RationalVoronoiPacket` stores explicit meshes, signed face orientations,
rational fields, paths and addressed leaves. Its native checker validates
positive Gram determinants, opposing edge incidences, connected vertex links,
connectivity, field-gradient inequalities, path endpoints and edges, dimensions,
corner-radius inequalities, site upper/lower witnesses, strict classifications,
coverage and absence of overlapping ancestor leaves. Patch vertices are
reconstructed from addresses, and corresponding area fractions are derived.
There is no shortest-path optimizer or heat solver in this checker.

The native checker uses squared root inequalities rather than requiring the
producer's particular square-root rounding. It can therefore accept valid
bounds that differ from the Python checker's preferred numerical witnesses.
Its theorem is about this native checker and the explicit exported data, not a
claim that the two implementations have been proved extensionally identical.
Kernel reduction checks acceptance; no `ofReduceBool` axiom is admitted.

The three saved packets have 84 leaves in total, with 13 strict winner leaves.
Their native input contains every mathematical witness field. Derived cached
barycentric coordinates and areas are reconstructed, and the original packet
is validated before export. The raw JSON parser and exporter are not formally
verified; the retained literal Lean source and source hashes make the checked
object concrete. Native acceptance, the extracted rational obligations and the
previous geometric enclosure laws are substantial pieces of the eventual full
semantic bridge, but do not by themselves construct the metric quotient.

## Reproduction and interfaces

Run `PYTHONPATH=python python python/develop_metric_boxes.py` to regenerate the
metric cases, point checks, arithmetic corpus, native packets and selected Lean
sources. `scripts/check_metric_boxes.sh` compiles the three foundational modules,
checks the literal metric/arithmetic packets and native Voronoi packets, audits
standard axioms and runs the focused tests. It is wired into the Lean workflow.
The historical heavy library is not rebuilt by this focused script.

The new commands are `metric-box`, `box-exclude` and `box-faces`. Inputs use JSON
polynomial triples and rational endpoint strings. `voronoi-check --lean-out`
exports a supplied accepted packet as literal data and a native Lean acceptance
theorem. Large exported packets can still exceed local compilation resources;
export is not a promise that all sizes compile within the current budget.

The generated corpus checks branch and infinity boxes in genera one through
four and 200 rational point-density queries. The strict examples, adaptive tree,
ideal separator, native acceptances, rejection cases, complete arithmetic
example and all-genus theorem are checked separately. Exact logs and source
hashes accompany the release. Practical solver benchmarks, general global
smooth metric identification, full compiler proof emission and classical Sturm
variation remain separate fronts.

## Checked release outcome

The focused Lean run checked 52 declarations using only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` (or subsets). It includes three
native packet acceptance proofs and two corrupted-packet rejection proofs.
The full Python regression run executed 940 tests: 936 passed and four optional
Lean integration tests were skipped. The 16 focused tests also passed separately.
The historical full Lean library was not rebuilt in this environment. Saved
logs, the literal-source manifest and SHA-256 hashes are under
`receipts/metric_boxes/`.
