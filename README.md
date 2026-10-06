# PerfectPower

**Exact polynomial arithmetic, reusable decision policies, and algebraic-curve research from the defining polynomial.**

PerfectPower turns supported polynomial and arithmetic models into executable mathematical objects. It can return complete integer solution families, make finite solution spaces countable and addressable by rank, compile optimal calibration and diagnostic policies, and derive a curve family's differential equations directly from its polynomial. The geometry machinery connects coefficient motion, algebraic root collisions, local branches, logarithmic execution, actual quotient towers, explicit isogeny kernels, superelliptic periods, certified ordinary continuation and arithmetic Frobenius while retaining the original equation and coordinates.

The common approach is to expose structure that can be reused: a solution generator instead of another search, an exact population instead of a materialized dataset, a complete operating policy instead of one optimal setting, or a differential system and quotient maps instead of an unexplained numerical period. The program combines a Python compiler and exact algebra engines with a Lean 4 theorem library. Numerical geometry and solver integration are optional extensions.

## What you can build with it

| User and direct use | Current output | Why the structure matters |
|---|---|---|
| Algebraic-curve researchers investigating a polynomial family | Exact discriminant, de Rham connection, selected Picard–Fuchs operator, affine deformation class, simultaneous root velocities and simple nodal residues | Connects coefficient changes to shape changes, degeneration directions and differential order, with replayable polynomial identities rather than only plots or numerical fits. |
| Researchers studying symmetric genus-two curves | Translated-reflection discovery, two explicit elliptic quotient maps, an independently derived connection splitting into two elliptic blocks, rational fibres and original-coordinate integrality | Explains a reduction through actual maps and differential pullbacks; the smaller systems can be queried and executed separately. |
| Calibration and quantized-control engineers | Complete nearest-setting regions on a declared target interval or rectangle, switching contacts and every tie | Compiles repeated optimization into a reusable policy covering the entire supported target region. |
| Authors of finite diagnostic procedures | An adaptive experiment tree with globally minimum worst-case cost for the declared resettable, noiseless model | Identifies a whole hypothesis set through observations and branches, instead of assembling pairwise distinguishing experiments manually. |
| Configuration, dataset and exact-sampling authors | Count, rank, selection, paging, sampling without replacement, rank shards, supported distinct images and symbolic joins | Gives direct access to large structured design spaces without first listing every object; duplicate-value geometry becomes part of the population definition. |
| Number theorists and arithmetic solver authors | Complete lists or generators for supported integer equations, exact coordinate recovery, constrained optimization and replayable certificates | Reuses a mathematical reduction across a family and retains the original integer restrictions. Unsupported global cases remain explicitly unresolved. |
| Operator, recurrence and sequence researchers | Shared observable machines, exact state reductions, generating-function witnesses, subsequences and cheapest separating experiments | Makes the requested output and its distinguishing experiments executable across related models. |
| Graph and special-function researchers | Exact conditional graph measures and sampling; factorial-ratio valuations, stripped units, modular execution and hypergeometric recurrences | Produces reusable algebraic measures and arithmetic execution rules, including operations at indices too large for direct factorial expansion. |

These are implemented capabilities within the scopes below. The [application roadmap](docs/DIRECT_USE_BUILD_ROADMAP.md) also records proposed extensions; a roadmap entry is not itself a delivered feature. Workload-specific [solver measurements](docs/HOST_ADAPTER.md) and [incremental replay measurements](industrial_performance/REPLAY_README.md) describe performance evidence without asserting a general speed advantage over conventional tools.

## Literature into executable research

All of the latest literature directions have concrete implementations and worked receipts. The [full monograph](docs/LITERATURE_CURVE_EXECUTION_MONOGRAPH.pdf), [mathematical source and literature map](docs/LITERATURE_CURVE_EXECUTION_MONOGRAPH.md), and [twenty-two reproducible receipts](docs/literature_receipts/manifest.json) give algorithms, proofs and boundaries. The core remains standard-library Python.

| Research capacity | Current concrete result | Direct use and supported scope |
|---|---|---|
| Composed actual quotient geometry | `genus_three_tower` decomposes `y²=x⁷+t x⁵+t x³+x` into three elliptic systems after `delta⁴=-4(t-3)`, with rank-six pullback and a degree-32 Jacobian isogeny | Execute each rank-two factor and transport results through verified maps. The quartic base change is essential; no splitting over `Q(t)` is claimed. |
| Formal map reconstruction and explicit kernels | `formal_two_isogeny` lifts a tangent map through formal logarithms and reconstructs a verified rational map; `richelot` builds a genus-two correspondence and divisor kernel; `reflection_kernel` supplies marked integral norm/transfer maps and torus kernel generators | Investigate actual degree-two and degree-four isogenies, with explicit kernels in supported classes. General endomorphism rings and arbitrary tower kernels remain open. |
| Broader polynomial periods | Persistent `superelliptic_family` reduces `y^d=f(x,t)` with exact primitives, character blocks and holomorphic basis indices; `y³=x⁴+x+t` is a genus-three example | Derive period equations beyond hyperelliptic input. Coprime monic smooth models have degrees 2 through 8 and state dimension at most 32. |
| Tensor structure, invariant searches and descent | Persistent `differential_module` constructs tensor, dual, Hom, symmetric and exterior modules, rational horizontal sections, filtered polarized endomorphisms, gauges and full matrix descent under `t→-t` | Turn differential equations into reusable representation objects and descend compatible systems to `u=t²`. Searches are complete inside their stated rational ansatz, not a full differential Galois classification. |
| Combinatorics meets curves | Persistent `binomial_sum` compiles affine binomial sums into rational constant terms; Vandermonde and both Apéry families have exact telescopers; the zeta(2) operator matches an independently derived elliptic family | Move between exact sequence values, proved recurrences and polynomial period geometry. A general multivariate telescoping solver is not supplied. |
| Controlled marked execution | `certified_transport` returns Gaussian-rational centers with proved Taylor tail and propagation bounds; `marked_legendre` adds certified standard integral-cycle seeds | Continue periods along certified ordinary polygons. Singular endpoints and automatic integral monodromy recognition require further methods. |
| Integral topology and degeneration geometry | `branch_braid` executes marked Picard–Lefschetz actions; `root_clusters` builds split-root p-adic cluster trees and geometric semistable graphs; `simultaneous_nodes` resolves several quadratic collisions | Obtain exact cycle actions, graph genera and local branch contacts. Braids are supplied; cluster component twists and minimal arithmetic models are not inferred. |
| Arithmetic cohomology and deformation | `frobenius` computes actual cohomological matrices with proved p-adic tail precision; `frobenius_deformation` supplies horizontal formal jets; `tower_frobenius` reuses three elliptic blocks | At `delta=1,p=7`, the rank-six tower matrix agrees with independent counts and has polynomial `X⁶+5X⁴+35X²+343`. The backend uses bounded prime fields and good reduction. |
| Relative Feynman periods | `sunrise` derives an exact bivariate divergence certificate for the equal-mass two-dimensional sunrise integral, proves the boundary term `-6` and supplies a rank-three augmented amplitude system | Distinguish the physical relative integral from its rank-two homogeneous elliptic period system using the same Symanzik polynomial. General diagrams and masses are not claimed. |

```python
from perfectpower.curve_correspondences import genus_three_elliptic_tower
from perfectpower.arithmetic_frobenius import tower_frobenius
from perfectpower.sunrise_relative import sunrise_certificate

tower = genus_three_elliptic_tower()
print(tower["isogeny_degree"])                        # 32
print(tower_frobenius(tower)["independent_counts_match"])  # True
print(sunrise_certificate()["boundary"]["integrated_value"])  # -6
```

Run `PYTHONPATH=python python python/literature_curve_corpus.py` to rebuild every direction. These exact Python calculations and analytic/p-adic bounds do not add new Lean kernel proofs. The finite mesh/Hodge objects elsewhere are not identified with these continuous de Rham structures, and differential projectors alone still do not certify algebraic correspondences.

## Quick start

Requires **Python 3.10 or later**. The core Python package has no runtime dependencies. Use a repository checkout so the compiler can access the accompanying data and proof records. The current machinery is on `claude/laughing-lamport-qqzdo9`:

```sh
git clone --branch claude/laughing-lamport-qqzdo9 https://github.com/towre676-cloud/perfectpower.git
cd perfectpower
python -m pip install .
python -m perfectpower solve --expr '(5*n - 7)**3 - 2'
```

This asks when `(5n − 7)³ − 2` is a square, for `n ≥ 1`. The complete answer is **`n = 2`, with square roots `−5` and `5`**. The compiler recognizes a change of coordinates to the proved curve `y² = x³ − 2` and retains the original integer restrictions.

To solve a supported equation over **all integer coordinates**, use `exact-solve`. Coefficient lists run from the constant term upward: `[-199,1,1,1,1]` means `x⁴ + x³ + x² + x − 199`.

```sh
python -m perfectpower exact-solve --coeff '[-199,1,1,1,1]' --d 2 --verify
```

The complete answer is **`(x,y) = (7,−51)` or `(7,51)`**. Here `--verify` replays the exact Python certificate; it does not invoke Lean.

```python
from perfectpower.compiler import PowerConstraint, compile_constraint

plan = compile_constraint(PowerConstraint([-345, 735, -525, 125], 2))
print(plan.answer)      # complete_list
print(plan.all_hits())  # [(2, [-5, 5])]
```

See the [Python API](python/README.md), [constraint compiler guide](docs/CONSTRAINT_COMPILER.md), and [worked examples](docs/SHOWCASE_MONOGRAPH.md). Run `python -m perfectpower --help` for the full command list.

## From polynomial structure to differential execution

`CurveFamily` accepts a monic family `y² = P(x,t)` of degree 3, 5 or 7 in `x`, with rational polynomial parameter coefficients of degree at most 8. Smooth fibres have genus 1, 2 or 3. It derives the discriminant, an exact rational Gauss–Manin connection and a scalar Picard–Fuchs operator for a requested observable. The scalar order is the minimum universal order for that observable on the full period module; a particular cycle may satisfy a smaller equation.

```python
from perfectpower.curve_families import CurveFamily

# P(x,t) = x^5 - x + t; each entry is a polynomial in t,
# and both coefficient lists run from constant term upward.
family = CurveFamily({"coefficients": [[0, 1], [-1], [0], [0], [0], [1]]})
print(family.deformation()["coordinate_only_generic"])  # False
print(family.collisions()["covered_simple_roots"])      # 4
print(family.observable()["order"])                     # 4
```

The structural queries connect several interpretations of the same polynomial:

| Query | Exact mathematical output | What it clarifies |
|---|---|---|
| `deformation` | Decomposition of `P_t` modulo the translation and scaling directions `P_x` and `x P_x − mP`, with chart pivots and replayed identities | Which coefficient motion changes shape in this affine chart. For `x⁵+t`, scaling explains the first-order observable `10t F′+3F=0`; `x⁵−x+t` has essential shape motion. |
| `root_motion` | The rational polynomial representative of `−P_t/P_x` modulo `P`, checked by a polynomial identity | Every simple root's velocity without solving roots in radicals or choosing a numerical ordering. |
| `collisions` | Collision coordinates and connection residues at every simple finite discriminant root, using exact squarefree rational quotient algebras and splitting on nonunits | Where roots collide and how that collision enters period space. Repeated discriminant roots and infinity require separate local analysis. |
| `observable` | Exact derivative rows, their first dependency, and rational and primitive polynomial differential operators | The differential complexity of the chosen output, including additional scalar singularities distinct from singular fibres. |
| `period_path` | Marked numerical initialization and continuation, backed by exact exclusion of declared polynomial zeros along whole rational path segments | How to execute the derived system along a specified path. Numerical quadrature and ODE errors are not certified. |

For translated-even sextics, `elliptic_quotient` adds a complementary genus-two route. It discovers the reflection center, checks the odd-coefficient conditions, constructs two elliptic quotient maps and checks that an independently derived residue-free four-dimensional connection intertwines with their two-dimensional blocks. `construct_quotient` builds a sextic from a chosen first elliptic cubic and center; `point_image` and `rational_lifts` retain arithmetic information in the original coordinates. This supports this explicit reflection class, not arbitrary elliptic-cover discovery or gluing of arbitrary curve pairs.

The bridge combines established deformation, de Rham, Gauss–Manin, Picard–Fuchs and elliptic-cover mathematics in one executable research object. Its value here is the linked explanation and exact execution; worldwide mathematical priority is not established. See [the family compiler](docs/CURVE_FAMILIES_MONOGRAPH.md), [geometry inside the polynomial](docs/CURVE_STRUCTURE_MONOGRAPH.md), and the [ten-request service example](receipts/curve_structure/service_requests.jsonl). The current input degree limit is 8; the original family monograph describes the earlier degree-4 limit.

The [projective research extension](docs/CURVE_RESEARCH_MONOGRAPH.md) connects six further capacities to these objects:

| Research operation | Delivered machinery | Exact scope |
|---|---|---|
| Move branch coordinates projectively | `projective_deformation` on binary forms of degrees 4, 6 and 8 | Full projective tangent quotient, including a moving infinity and form scaling, on an explicit generic chart. |
| Execute near repeated-root fibres and parameter infinity | `local_analysis`, `frobenius_jet` | Exact Laurent charts, branch multiplicities, diagonal Fuchsian gauges and finite logarithmic jets at rational parameters or infinity; positive resonances are reported. |
| Vary several parameters together | `MultiCurveFamily`, catalogue `multi_curve_family` | One through three parameters, exact simultaneous connections, zero-curvature replay, joint essential deformation rank and directional observable equations, within algebra budgets. |
| Discover broader explicit quotient maps | `discover_rational_quotients`, `verify_rational_quotient` | Reciprocal and translated-reflection templates, or a supplied finite rational-map candidate list, with exact identities and differential pullbacks. The reciprocal sextic examples compile two elliptic systems. |
| Search for horizontal projectors | `de_rham_pairing`, `horizontal_projectors`, `check_projector` | Continuous residue pairing and complete bounded linear ansatz for horizontal, holomorphic-filtration-preserving, self-adjoint endomorphisms; finite idempotent candidate search. Betti rationality and Jacobian splitting are not inferred. |
| Transfer integral cycles through a marked surface map | `simplicial_cycle_map`, service `cycle_map` | Actual integral homology maps from an explicit simplicial vertex map, with Smith bases and boundary witnesses. Matching the triangulations to an algebraic quotient's period marking remains an additional obligation. |

Run `PYTHONPATH=python python python/develop_curve_research.py` to reproduce the [exact research corpus](receipts/curve_research/summary.json), or replay its [service transcript](receipts/curve_research/service_requests.jsonl). These earlier numerical paths remain uncertified; the new `certified_transport` and `marked_legendre` routes above provide separate proved ordinary continuation bounds. New Lean kernel proofs remain separate work.

The [algebraic curve extension](docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.md) now joins differential field arithmetic to those geometric operations. Finite étale algebras retain conjugate algebraic values without radical choices, extend up to three commuting parameter derivations, compute fixed algebras and cyclic Hilbert–90 witnesses, and construct primitive models of complete tensor products. `algebraic_degenerations` covers the finite discriminant support, including repeated discriminant roots, and `node_branches` executes conjugate local branches at algebraic ordinary double points. `resonant_frobenius` resolves positive resonances through simultaneous logarithmic recurrences; the corpus completes the Legendre infinity jet through order 12. `ramified_scaling_chart` constructs and verifies smooth models for the supported centered-binomial class at finite rational or algebraic points and infinity.

`SymmetryCurve` accepts a supplied finite Möbius action on a smooth hyperelliptic polynomial of degree 3 through 8. It verifies the curve automorphisms, closes the action, constructs generators of the actual quotient function field, derives the quotient equation and its independent de Rham connection, and checks the complete differential pullback. Group averages give horizontal, filtration-preserving geometric projectors. For a verified non-hyperelliptic involution, `involution_decomposition` constructs both complementary double covers and certifies their induced Jacobian isogeny; the corpus includes degree-4 genus-two and degree-8 genus-three cases. This conclusion uses the actual maps and their norm/pullback identities. A differential projector alone still does not imply a Jacobian decomposition.

```python
from perfectpower.symmetry_quotients import SymmetryCurve

# y² = x⁵ + t x³ + x, with x -> 1/x and y -> y/x³.
curve = SymmetryCurve({
    "coefficients": [0, 1, 0, [0, 1], 0, 1],
    "generators": [{"matrix": [[0, 1], [1, 0]], "y_scale": 1}],
})
print(curve.quotient()["target_genus"])             # 1
print(curve.observable(sector="quotient")["order"]) # 2
print(curve.involution_decomposition()["isogeny_degree"]) # 4
```

The arithmetic check also supplies a useful negative result: the two rank-two differential projectors for `y²=x⁵+t` select character sets that are not closed under cyclotomic Galois conjugacy. `cyclic_projector_obstruction` certifies that these cannot be rational Betti projectors compatible with the verified cyclic action. See the [earlier monograph and proofs](docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.pdf), [interactive receipt workbench](docs/algebraic_curve_workbench.html), and [reproducible corpus](receipts/algebraic_curve_extensions/summary.json). Run `PYTHONPATH=python python python/develop_algebraic_curve_extensions.py` or replay `receipts/algebraic_curve_extensions/service_requests.jsonl`. General automatically marked integral matrices and arbitrary isogeny kernels remain open; the new reflection, Richelot and elliptic routes supply explicit supported kernels. Formal local jets remain distinct from the new certified ordinary analytic continuation.

## Populations, policies and persistent research objects

[`ExactPopulation`](docs/POPULATION_MONOGRAPH.md) compiles supported finite domains and curves into reusable query spaces. It counts, selects and locates original objects by rank, samples without replacement, partitions work into balanced rank shards and exports seeded JSONL datasets. Distinct projections use complete cubic collision geometry or supported higher-degree discrete monotonicity certificates. Symbolic joins and projections have defined supported families; arbitrary polynomial image closure is not assumed.

[`CalibrationPolicy` and `DiagnosticPolicy`](docs/DECISION_POLICIES_MONOGRAPH.md) turn exact optimization into executable decisions. Calibration fixes a bounded feasible integer model and a positive definite rational metric, then computes all winning regions on a one- or two-dimensional target slice, including lower-dimensional regions and ties. Optimizer-driven discovery can avoid listing settings that never win. Diagnostics supports at most 16 finite hypotheses and minimizes worst-case total cost over adaptive trees under noiseless readouts, zero-cost reset and strictly positive operator costs. Both compilers have explicit budgets and reject incomplete compilation.

The SQLite catalogue stores immutable, content-addressed definitions with aliases. Its **19 object kinds** are `population`, `projected`, `sequence`, `inverse`, `graph`, `geometry`, `combinatorial`, `factorial`, `calibration_policy`, `diagnostic_policy`, `curve_family`, `elliptic_quotient`, `multi_curve_family`, `differential_extension`, `symmetry_curve`, `differential_module`, `superelliptic_family`, `binomial_sum` and `elliptic_curve`. The JSONL service and local HTTP console expose the supported public operations:

```sh
# Interactive local console and persistent catalogue.
python -m perfectpower service --database /tmp/pp.sqlite --http-port 8080

# Alternatively, replay the curve-structure research transcript.
python -m perfectpower service --database /tmp/pp-structure.sqlite \
  < receipts/curve_structure/service_requests.jsonl
```

Run `python -m perfectpower population --spec receipts/populations/compatible_layouts.spec.json` for a configuration population, or `python python/develop_decision_policies.py` for the coupled configuration-to-diagnosis example. See [catalogue and service foundations](docs/OPEN_CONTENT_MONOGRAPH.md), [decision-policy receipts](receipts/decision_policies/summary.json) and [curve-structure receipts](receipts/curve_structure/summary.json). Older release monographs record the catalogue counts at their publication dates.

## Arithmetic, operator and geometry interfaces

[`EllipticCurve`](docs/ELLIPTIC_WITNESSES_MONOGRAPH.md) exposes exact generalized Weierstrass arithmetic, supported rational model transport, rational two-isogenies and **complete rational halving fibres**. A separate bounded checker replays witness-span rank lower bounds with independently implemented local characters and binary elimination. On `y²=x³−4x+1`, it certifies two independent rational witnesses and recovers them from their doubles through recorded halving steps. The [eleven-packet corpus](receipts/elliptic_witnesses/summary.json) also retains a genus-two quotient point with no rational lift, preserving the original square-coordinate restriction. Run `make elliptic-witnesses`; [read the PDF](docs/ELLIPTIC_WITNESSES_MONOGRAPH.pdf). These are exact Python certificates, with no new Lean proof, full Mordell–Weil basis or global integer-point census.

| Capacity | Entry points | Scope and documentation |
|---|---|---|
| Compile polynomial power, triangular-number and quadratic-root constraints | `solve`, `prove`, `classify`, `count`, `enumerate` | Complete supported reductions, Pell and radical generators; [compiler](docs/CONSTRAINT_COMPILER.md), [overview](docs/MONOGRAPH.md). |
| Solve polynomial equations over all integers | `exact-solve`, `square-fibres`, `integer-roots` | Selected Mordell, effective quartic, Runge and other supported families; [arithmetic engine](docs/ENHANCED_MACHINERY_MONOGRAPH.md), [roots and bounds](docs/MONOGRAPH_DEVELOPMENT_MONOGRAPH.md). |
| Discover polynomial coordinates and solve sign domains or polynomial optima | `polynomial-decompose`, `polynomial-relation`, `polynomial-domain`, `polynomial-optimize` | Exact supported coordinate identities and global domain reasoning; [polynomial capacity](docs/POLYNOMIAL_CAPACITY_MONOGRAPH.md). |
| Query polynomial/modular domains and signed power curves | `semilinear-domain`, `semilinear-optimize`, `polynomial-charts`, `coefficient-charts`, `curve-query`, `family-evaluate`, Python `CurveSpace` | Count, select, restrict and optimize reusable families; [semilinear capacity](docs/SEMILINEAR_CAPACITY_MONOGRAPH.md), [query spaces](docs/QUERY_SPACE_MONOGRAPH.md). |
| Simplify arithmetic models and recover original coordinates | `simplify-query`, `analyze-power`, `polynomial-pullback`, `factored-scan` | Exact reductions, necessary local conditions and explicit bounded searches; [simplifier](docs/ARITHMETIC_SIMPLIFIER_MONOGRAPH.md), [local filters](docs/LOCALITY_AND_OBSERVABLE_MACHINES.md). |
| Execute Gamma, factorial-ratio and binomial arithmetic | `gamma-analyze`, `gamma-unit`, `gamma-domain`, `gamma-optimize`, catalogue `factorial` | Valuations, stripped units, modular values and exact hypergeometric recurrences; integrality and modular evaluation are separate claims; [Gamma arithmetic](docs/GAMMA_ARITHMETIC_MONOGRAPH.md), [nonlinear execution](docs/OPEN_CONTENT_MONOGRAPH.md). |
| Solve integer linear systems and nearest-setting problems | `integer-lift`, `nearest-lift`, catalogue `inverse`, `calibration_policy` | Exact fibres, inequality-constrained bounded calibration, every tied nearest point and complete supported target policies; [integer lifting](docs/INTEGER_LIFTING_MONOGRAPH.md), [policies](docs/DECISION_POLICIES_MONOGRAPH.md). |
| Recover monomial models and project exact relations | `monomial-solve`, `monomial-rational`, `monomial-eliminate`, `monomial-recovery`, `monomial-project` | Supported integer/rational recovery and elimination; [monomial recovery](docs/MONOMIAL_RECOVERY_MONOGRAPH.md). |
| Share operator and recurrence state; design experiments | `recurrence-batch`, `recurrence-orbit`, `observable-machine`, `integral-machine`, `operator-algebra`, catalogue `sequence`, `diagnostic_policy` | Exact observable compression, modular domains, cheapest separating experiments and finite adaptive diagnosis; [output machines](docs/LOCALITY_AND_OBSERVABLE_MACHINES.md), [integer states](docs/INTEGRAL_OUTPUT_MACHINES.md), [policies](docs/DECISION_POLICIES_MONOGRAPH.md). |
| Certify matrix-output generating functions and subsequences | `witness-resolvent` | Exact generating-function witnesses; [witness resolvents](docs/WITNESS_RESOLVENTS_AND_GRAPH_REPAIRS.md). |
| Query, sample and reweight graph bases | `connection-measure`, `connection-reweight`, catalogue `graph` | Supported gain graphs, conditional measures and exact cyclotomic arithmetic at orders 2 through 64; [graph measures](docs/MONOGRAPH_DEVELOPMENT_MONOGRAPH.md), [weight repairs](docs/WITNESS_RESOLVENTS_AND_GRAPH_REPAIRS.md), [sampling](docs/OPEN_CONTENT_MONOGRAPH.md). |
| Compute finite algebraic and differential models | `weighted-hodge`, `finite-weil`, `divisor-kernel`, `finite-mellin` | Exact finite Hodge, Fourier and divisor calculations; [deep gems](docs/DEEP_GEMS_MONOGRAPH.md), [geometry guides](docs/README.md#geometry). |
| Compute branched-curve topology, differentials and local geometry | `branched-geometry`, `branch-form`, `period-normalize`, `surface-homology`, `symplectic-periods`, `integrate-path` | Supported branched models and explicit differential/period data; [geometry documentation](docs/README.md#geometry). |
| Analyze metrics, periods and Voronoi geometry | `legendre-period-bounds`, `analytic-periods`, `intrinsic-voronoi`, `certified-voronoi`, `conformal-metric`, `conformal-voronoi` | Exact local identities and rational polyhedral enclosures have different guarantees from numerical continuous geometry; [analytic geometry](docs/ANALYTIC_GEOMETRY_MONOGRAPH.md), [enclosures](docs/VORONOI_ENCLOSURE_MONOGRAPH.md). |
| Derive and explain polynomial-family geometry | Python `CurveFamily`, `EllipticQuotientFamily`; catalogue `curve_family`, `elliptic_quotient`; service `discover_quotients`, `construct_quotient` | Exact connections, deformation classes, root motion, simple collision residues, explicit quotient reductions and marked numerical continuation; [family compiler](docs/CURVE_FAMILIES_MONOGRAPH.md), [structural machinery](docs/CURVE_STRUCTURE_MONOGRAPH.md). |
| Compare arithmetic families with local sequence records | `oeis`, `sequence-atlas` | Local OEIS matching with source attribution; [OEIS integration](docs/OEIS.md). |

For example, `curve-query --left '[1,0,-2,0,1]' --right '[0,0,0,1]' --objective 'x*x+y*y' --verify` solves `(x²−1)²=y³` completely and returns all three tied minimizers. The [semilinear receipts](receipts/semilinear_capacity/summary.json) record the defined closure and constrained-optimization workloads. For solver integration, the [SMT adapter](docs/HOST_ADAPTER.md) replaces recognized arithmetic relations with their complete solution sets; the separate [incremental replay tool](industrial_performance/REPLAY_README.md) transports SMT-LIB commands.

## Results and guarantees

<a id="the-four-answers"></a>
Constraint plans expose an `answer` describing what a caller can use:

| Answer | Meaning |
|---|---|
| `complete_list` | Every solution in the stated domain is listed. |
| `generator` | A structured family generates the solutions exactly. |
| `conditional` | Completeness depends on explicitly named mathematical premises. |
| `unresolved` | The available method does not establish a complete answer. |

<a id="what-to-trust-at-a-glance"></a>
**A complete mathematical answer and a formally verified program are separate guarantees.** Inspect the result's certificate for theorem names, premises, domain and reduction steps. Lean checks the statements of compiled theorems. Python discovers and executes plans and can replay exact certificates, but its execution is not formally verified. Emitted Lean source becomes a checked theorem only after compilation.

Global solving, finite exact calculation and numerical exploration have distinct scopes. A bounded scan or bounded integer-fibre query does not establish a global point census. Deformation charts do not classify all projective equivalences; simple collision residues do not supply a marked integral monodromy matrix. Exact path exclusion does not certify numerical period error. Generic smoothness checks and explicit algebra, degree and coefficient-size budgets constrain the family compilers. General polynomial integer solving and arbitrary algebraic-curve compilation remain outside the delivered scope. See the [trust boundary](docs/TRUST_BOUNDARY.md), [certificate format](docs/CERTIFICATE_FORMAT.md) and each module's guide.

## Representation and flavor research

The [complete minimal nonet potential](docs/VALENTINER_NONET_JOINT_POTENTIAL.md) supplies **60 independent scalar coefficients, 28 cross-sector quartics and 70 coefficients with the Higgs**. Exact character arithmetic certifies the counts. A bounded action has an isolated **21-scalar CP-breaking vacuum** with nondegenerate finite quark spectra and termwise one-loop mass-phase protection. Allowed interactions move **all four mixing observables at fixed six quark masses**, verified by renewed stationary solutions. The polynomial machinery now supplies rephasing-invariant golden/66-degree constraint equations and derives their conditional elliptic slice directly from its cubic. These are reproducible interaction and geometry results; this complete action does not predict the golden coefficient or the observed hierarchy. The [receipt](receipts/m22_interactions/valentiner_nonet_joint.json) retains every coefficient, search start, spectrum and finite-deformation check.

The repository includes a reproducible finite-group flavor program built on genuine complex `3.A6` triplets and recovered M22 geometry. Exact representation certificates, invariant contractions, joint scalar vacua and canonical quark matching are supplied with scientific receipts and reader PDFs. The [canonical completion](docs/VALENTINER_CANONICAL_RESULTS.md) enforces a Nelson–Barr interaction graph, giving a positive tree-level determinant with physical weak CP, three light quark modes per sector, and exact relations among finite-scale charged currents, neutral currents and Higgs couplings.

The [electroweak and quantum completion](docs/VALENTINER_QUANTUM_COMPLETION.md) extends that construction to a stable **71-scalar Higgs/flavor branch** with all four nonzero Higgs portals. A justified chiral-spurion charge assignment retains the mixing frame while controlling fermionic vacuum feedback. The leading canonical one-loop strong-CP mass threshold is below **2 × 10⁻¹⁴ radians** at the selected benchmark, with an independently checked CP partner and 60-digit trace evaluation. The exact higher-fermion census contains **33 Higgs covariants and 123 heavy-mass/source covariants** through three scalar insertions, including finite-group channels beyond ordinary SU(3) trace words. A uniform finite-EFT determinant bound covers every coupling in the stated coefficient domain.

The [Hermitian-source completion](docs/VALENTINER_HERMITIAN_INTERACTIONS.md) now puts **hierarchical masses, physical weak CP and exact one-loop mass-phase cancellation in the same canonical fermion action**. A real scalar nonet enforces Hermitian heavy-to-light mixing; the termwise cancellation holds for arbitrary real neutral-scalar mixing, including Higgs/flavor portals. Five justified real fermion couplings per sector give exact finite-spectrum and charged-current formulas. An explicit nine-word covariant basis has determinant equal to the cube of a CP invariant and spans Hermitian source centers through scalar degree eight. A specified scalar EFT retains a locally positive **91-scalar branch**. Its declared fitted center coefficients match six illustrative hierarchical masses and four PDG-derived finite-current targets within **2.7 × 10⁻¹⁵ relative current error**. The complete mass-only affine search certifies **128 branch pairs** without CKM input. [74 passing checks and byte-identical fresh replay](receipts/m22_interactions/valentiner_hermitian_validation.json) support the result; the [full chapter](docs/VALENTINER_HERMITIAN_INTERACTIONS.md) states its source-coefficient, higher-operator and loop-order scope. These source inputs establish attainable flavor, with the golden relation remaining a separate prediction requirement.

The [Sommerfeld constant and exact-angle calculation](docs/SOMMERFELD_CONSTANT_AND_66_DEGREES.md) establishes an electromagnetic matching sum rule: the product of all six Dirac masses is `(v y m)^3`, making the complete one-loop logarithmic photon threshold independent of the Hermitian source. A continuous fixed-spectrum weak-phase orbit has identical one-loop photon screening; twelve retained points include ±66°. The exact primitive-root carrier maps 66° to `φ^-2`, with its full embedding ambiguity retained. [Six new checks and eighteen related checks](receipts/m22_interactions/flavor_electromagnetic_validation.json) and fresh byte-identical replay accompany the [scientific receipt](receipts/m22_interactions/flavor_electromagnetic.json). The measured fine-structure constant is identified separately from the still-independent gauge normalization.

The [positive kinetic construction](docs/FLAVOR_KINETIC_FREEDOM.md) supplies nine real polynomial covariants spanning the Hermitian quark metric at the CP-breaking vacuum. The new inverse-matching benchmark constructs all six hierarchical Yukawa eigenvalues and reproduces the **PDG 2026 central CKM inputs** with magnitude error below **4.5 × 10⁻¹⁶**, while preserving the tree determinant phase. Its fitted real metric coefficients and illustrative mass inputs are explicit in the [receipt](receipts/m22_interactions/valentiner_quantum.json). These matched inputs establish attainable spectra; the canonical loop calculation and the fitted kinetic action have their own stated assumptions. The [release validation](receipts/m22_interactions/valentiner_quantum_validation.json) records **56 passing focused and related checks** and byte-identical fresh replay. [Read the full research chapter](docs/VALENTINER_QUANTUM_COMPLETION.md) for the exact action, calculation boundaries and reproduction commands.

## Build and develop

Run the core Python tests directly from the checkout:

```sh
PYTHONPATH=python python -m unittest discover -s python/tests
```

Lean and Mathlib are pinned to **4.20.0**. With [elan](https://github.com/leanprover/elan) installed, fetch Mathlib's cache and use the build script, which schedules the memory-heavy generated proofs sequentially:

```sh
lake exe cache get
make lean
```

`make test` runs the Python suites across the repository. `make verify` builds Lean, checks axioms, runs tests, regenerates receipts and [status summaries](docs/STATUS.md), and checks for drift. Individual formalization guides provide focused check scripts. Optional SMT integration dependencies install with `python -m pip install '.[industrial]'`; numerical geometry uses optional NumPy/SciPy dependencies described in its [guide](docs/ANALYTIC_GEOMETRY_MONOGRAPH.md).

## Documentation and license

The [documentation index](docs/README.md) organizes mathematical accounts, implementation guides, proof audits and benchmark reports by subject. For background, read [the history of perfect powers](docs/HISTORY.md) or [computation and the limits of solving equations](docs/HILBERT10.md).

Code and Lean sources use [Apache-2.0](LICENSE); documentation and papers use [CC BY 4.0](LICENSE-docs). Included OEIS records retain their [source attribution and CC BY-SA 4.0 license](data/oeis/SOURCE.md). Citation metadata is in [CITATION.cff](CITATION.cff).
