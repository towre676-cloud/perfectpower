# Exact division fibres in Lean and the repository frontier

This push supplies a reusable Lean foundation for the recently published rational elliptic interface. `PerfectPower/EllipticDivision.lean` proves division-fibre structure in every additive commutative group, generalized Weierstrass square completion, the precise nonexceptional halving quartic, short-form translation, and complete rational-root transport from a monic integral scaling. The group result is instantiated on Mathlib's actual generalized Weierstrass point group in `audit/EllipticDivision.lean`. These are mathematical theorems; the Python parser, interpreter, Sturm search and independence certificates are not thereby verified.

## Division is a kernel coset

For an integer n and a point P, choose any H satisfying nH=P. Then nQ=P if and only if n(Q-H)=0, equivalently Q=H+T for a point T in the multiplication kernel. The module constructs an actual equivalence between the fibre and the kernel. No assumption of finite rank, a torsion classification, a finite field or a generic position is needed. Consequently a complete kernel list gives a complete fibre list by translation, and distinct kernel elements give distinct outputs. An additive isomorphism transports the complete multiplication equation in both directions.

For n=2 this is the structural completeness argument used by the halving producer. It includes infinity and branch points. The infinity fibre is the two-torsion subgroup itself. It also extends immediately to other multiplication fibres once a complete n-torsion list and an anchor are available; it does not discover either of those inputs. The audit includes a nontrivial doubling fibre in Z/8Z and an instance for the actual elliptic point type.

## Coordinate algebra with explicit exceptional conditions

Write Y²=x³+Ax²+Bx+C. A nonbranch tangent has slope (3x²+2Ax+B)/(2Y), so its doubled x-coordinate is the square of that slope minus A minus 2x. The module proves that equality with a target u is equivalent to vanishing of

```text
x⁴-4u x³+(-2B-4uA)x²+(-8C-4uB)x+B²-4AC-4uC.
```

The denominator condition is exactly 2Y≠0. The raw polynomial identity needs no characteristic restriction; the rational-function equivalence explicitly excludes the exceptional denominator. The algebra does not by itself distinguish a target from its negative, since both have the same x-coordinate. The producer must still lift a root to a point and check the full doubling equation. The audit retains the example (3,5) on Y²=x³-2, whose double has x-coordinate 129/100.

Generalized square completion is proved without denominators first: the squared expression 2y+a1x+a3 differs from its completed cubic by four times the original residual. Equation equivalence explicitly requires 4≠0. Translation by A/3 gives the short coefficients B-A²/3 and C-AB/3+2A³/27, with 3≠0 retained. These identities match the coordinate conventions in the public rational interface.

## Complete rational roots through integer scaling

Let f be a rational polynomial and g a monic integer polynomial whose rational coefficient image is `f.scaleRoots D`. The latter has coefficients f_i D^(deg(f)-i). Every rational root r of f makes Dr a root of g. Mathlib's integral-root theorem then gives an actual integer z=Dr. When D≠0, every complete integer root list L for g gives exactly the rational list [z/D : z in L]. The proof checks both implications through polynomial evaluation and cancellation of D^deg(f).

The monicity and coefficient-map equality are explicit hypotheses, not facts borrowed from a producer's Boolean label. This closes the mathematical scaling bridge. Constructing the integer coefficients, validating their map identity, interpreting the integer root transcript and parsing the packet remain the next interpreter obligations. A complete integer list is still a premise of the generic theorem.

## Reproduction and evidence

Run `make elliptic-division-lean` with the pinned Lean 4.20.0 and Mathlib revision in `lake-manifest.json`. The focused audit instantiates the group theorem, checks rational coordinate examples, prints all seventeen public declaration axiom lists, and lints the namespace. The module is imported by `PerfectPower.lean`, the main axiom entry point and the main lint entry point. The [focused validation receipt](../receipts/elliptic_division_lean/summary.json) and [Lean output](../receipts/elliptic_division_lean/lean.log) record the actual check scope; they do not assert that the entire historic Lean census was rebuilt. The existing Python elliptic suite and repository Python regression targets are separate execution checks.

## Current global arithmetic fronts

The main global arithmetic gap remains effective completeness beyond the supported native routes. Square-plus-constant polynomial equations, effective Runge recognizers, Pell families and many small Mordell curves already have complete results. The committed summary lists 73 unconditional positive-k curves for 1≤k≤100 and 24 conditional theorem entries, including the residual statement. The negative-k unit reductions still need their explicit Matveev lower-bound premises discharged; a rational independent-witness lower bound supplies neither that logarithmic bound nor an integral-point height bound. The highest-value independent route is a certified global Mordell bound feeding `CubicCovariants` and the reduced-Hessian reconstruction. Native maximal-order certificates, basis-independent nonmonic reduction, recentered Skolem arguments and remaining larger slabs are other concrete avenues. k=94 remains a larger named slab target in the checkpoint. Old positive-k totals and historical order-cost rankings must be recomputed before selecting a new expensive instance.

The foundational density theorem still lacks a general Lean proof of the nonrigid density-zero branch through Boshernitzan or Siegel. The geometric normalization and Riemann-Hurwitz half of the all-exponent classification remains a structural target. Broader Runge/Baker/Chabauty backends require their own hypotheses and effective constants; Chabauty needs rank below genus. Hall, Pillai and abc remain research questions rather than consequences of the existing census.

## Compiler, population and sequence fronts

The Python compiler already carries signed and coefficient-bearing power charts, modular and Boolean domains, recurrent state periods, original-coordinate fibres, huge populations, exact rank/selection and supported symbolic joins. Generic Lean semantics for the whole transcript remain missing: general Sturm variation, root-cell truth, noncoprime chart construction, rank-selection correctness, forward-difference optimizer assembly and source-to-theorem transport. The most reusable next proof investment is a small typed interpreter covering these operators, rather than additional isolated example theorems. General nonlinear global images and nonmonotone higher-degree collision classification need additional mathematics. Domain preservation remains essential when Gamma poles, denominators or inverse coordinate restrictions occur.

Gamma/factorial arithmetic has exact fixed-shift polynomial normalization, valuation and stripped-unit execution, and hypergeometric recurrence transport. General variable-width factorial-ratio perfect-power classification is not supplied. OEIS remains a discovery corpus; more English definitions need reviewed encodings and actual equivalence proofs. Larger-unit continued-fraction characterization, broader recurrence languages, analytic transform endpoints and Tauberian converses remain useful avenues. Monomial-solver global completeness extends beyond the historical checked exponent systems.

## Curves, periods and smooth geometry fronts

The curve engine now includes several-parameter de Rham connections, algebraic local charts, resolved logarithmic resonances, actual finite quotients, elliptic towers, formal two-isogeny reconstruction, Richelot correspondences, tensor modules, ansatz-bounded horizontal searches, marked ordinary analytic continuation and selected Frobenius computations. The remaining targets are general higher-genus correspondence reconstruction, arbitrary integral cycle and kernel transport, singular Richelot targets, nonsplit stable reduction, general Puiseux and cluster arithmetic, optimized arbitrary-field Frobenius and p-adic continuation across parameter boundaries. Differential projectors do not alone identify algebraic correspondences. Full differential Galois groups, nonlinear idempotent enumeration, conjugate Hodge filtration and rational Betti descent remain distinct structural tasks.

Certified ordinary period continuation is implemented; the frontier is singular-endpoint certification and reliable extraction of integral monodromy from balls. Holomorphic local-parameter normalization, basis completeness and Euler-integral identification still need general foundational proofs. The Voronoi side has interval enclosure laws, local smooth metric bounds, exact chart transitions and selected native packets. A global smooth atlas, construction of the polyhedral quotient length metric, semantic identification of the surface packet, period-normalized metrics and unrestricted geodesic comparisons remain open. Finite Hodge matrices and continuous curve cohomology must be connected by actual comparison theorems.

## Graph, policy and external execution fronts

Exact graph measures, conditional sampling and graph-repair algebra are available in their supported scopes. General gain-graph support rank, arbitrary-column weighted Cauchy-Binet and matroid greedy optimality remain explicit structural targets. Decision regions and minimum-cost resettable noiseless diagnostic trees are executable; noisy, nonresettable or continuous hypotheses need new contracts and algorithms. The current HTTP service is local and single-worker; concurrent persistence and public deployment require deliberate engineering.

The industrial record has two different outcomes: the earlier strategy portfolio regressed, while the newer incremental ingestion replay measured a 4.73 percent summed wall-time improvement and a net gain of 64 solved queries on its declared 5,612-query cohort. The next performance work is independent replication, constant-memory streaming and realistic consumer integration. The Why3 arithmetic rules have Lean proofs, but the source parser/translator, live VC correspondence and an end-to-end GNATprove/SAW/consumer run remain unfinished. Concrete Brainpool coordinate export also needs its prime certificate for the field/group instantiation; equation identities alone establish no timing property.

## Flavor mechanism frontier

The latest finite-mediator completion protects the stated renormalizable first-order mass-phase argument but retains four physical mixing directions under fixed-mass deformation. Generic tree exchange relations also fail the light-scalar running test. The continuous SU(3) quartic relation closes a restricted algebra but cannot isolate an interior CP-breaking frame at fixed spectra. The next mathematical task is therefore a justified mechanism that correlates the permitted source, cross-sector and quark interactions while surviving the relevant running, with exact invariant contractions and canonical normalization. The 52-operator loop table is presently a numerically validated rational reconstruction and deserves an exact tensor proof. Gauge/Yukawa/Higgs running, thresholds, higher-dimensional operators and higher-loop phases remain separate physical calculations. Neither the Sommerfeld constant nor a physical 66-degree CKM phase has been derived by the current model.

These fronts interact productively: exact arithmetic can certify inverse fibres of actual curve maps; marked geometry can guide decomposition and specialization; a typed Lean interpreter can make the same compiler objects usable by external verification software. The strongest next push closes one reusable bridge and demonstrates a new complete consumer result, rather than widening a catalogue without closing its mathematical hypotheses.
