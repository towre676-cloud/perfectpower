# PerfectPower

**Exact polynomial arithmetic, reusable decision policies, and algebraic-curve research from the defining polynomial.**

PerfectPower turns supported polynomial and arithmetic models into executable mathematical objects. It can return complete integer solution families, make finite solution spaces countable and addressable by rank, compile optimal calibration and diagnostic policies, and derive a curve family's differential equations directly from its polynomial. The geometry machinery connects coefficient motion, algebraic root collisions, local branches, logarithmic differential execution and verified quotient maps while retaining the original equation and coordinates.

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

Run `PYTHONPATH=python python python/develop_curve_research.py` to reproduce the [exact research corpus](receipts/curve_research/summary.json), or replay its [service transcript](receipts/curve_research/service_requests.jsonl). New kernel proofs and rigorous numerical continuation remain separate work.

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

The arithmetic check also supplies a useful negative result: the two rank-two differential projectors for `y²=x⁵+t` select character sets that are not closed under cyclotomic Galois conjugacy. `cyclic_projector_obstruction` certifies that these cannot be rational Betti projectors compatible with the verified cyclic action. See the [complete monograph and proofs](docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.pdf), [interactive receipt workbench](docs/algebraic_curve_workbench.html), and [reproducible corpus](receipts/algebraic_curve_extensions/summary.json). Run `PYTHONPATH=python python python/develop_algebraic_curve_extensions.py` or replay `receipts/algebraic_curve_extensions/service_requests.jsonl`. Algebraic maps do not yet supply automatically marked integral cycle matrices or explicit isogeny-kernel generators; formal jets do not certify analytic continuation.

## Populations, policies and persistent research objects

[`ExactPopulation`](docs/POPULATION_MONOGRAPH.md) compiles supported finite domains and curves into reusable query spaces. It counts, selects and locates original objects by rank, samples without replacement, partitions work into balanced rank shards and exports seeded JSONL datasets. Distinct projections use complete cubic collision geometry or supported higher-degree discrete monotonicity certificates. Symbolic joins and projections have defined supported families; arbitrary polynomial image closure is not assumed.

[`CalibrationPolicy` and `DiagnosticPolicy`](docs/DECISION_POLICIES_MONOGRAPH.md) turn exact optimization into executable decisions. Calibration fixes a bounded feasible integer model and a positive definite rational metric, then computes all winning regions on a one- or two-dimensional target slice, including lower-dimensional regions and ties. Optimizer-driven discovery can avoid listing settings that never win. Diagnostics supports at most 16 finite hypotheses and minimizes worst-case total cost over adaptive trees under noiseless readouts, zero-cost reset and strictly positive operator costs. Both compilers have explicit budgets and reject incomplete compilation.

The SQLite catalogue stores immutable, content-addressed definitions with aliases. Its **15 object kinds** are `population`, `projected`, `sequence`, `inverse`, `graph`, `geometry`, `combinatorial`, `factorial`, `calibration_policy`, `diagnostic_policy`, `curve_family`, `elliptic_quotient`, `multi_curve_family`, `differential_extension` and `symmetry_curve`. The JSONL service and local HTTP console expose the supported public operations:

```sh
# Interactive local console and persistent catalogue.
python -m perfectpower service --database /tmp/pp.sqlite --http-port 8080

# Alternatively, replay the curve-structure research transcript.
python -m perfectpower service --database /tmp/pp-structure.sqlite \
  < receipts/curve_structure/service_requests.jsonl
```

Run `python -m perfectpower population --spec receipts/populations/compatible_layouts.spec.json` for a configuration population, or `python python/develop_decision_policies.py` for the coupled configuration-to-diagnosis example. See [catalogue and service foundations](docs/OPEN_CONTENT_MONOGRAPH.md), [decision-policy receipts](receipts/decision_policies/summary.json) and [curve-structure receipts](receipts/curve_structure/summary.json). Older release monographs record the catalogue counts at their publication dates.

## Arithmetic, operator and geometry interfaces

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

The repository also contains a separate mathematical-physics investigation of finite-group representations, invariant interactions and quark-flavor models. Its machinery includes an exact independent census of 263 CP-even scalar contractions through degree six for the declared field content, explicit interaction models, local-vacuum calculations and physical CP diagnostics. The [joint-potential analysis](docs/VALENTINER_JOINT_POTENTIAL.md) exhibits nonorthogonal local vacua and independent mixing deformations even with six masses fixed. These results do not derive the observed CKM matrix or establish a protected golden amplitude relation. Read the [supersymmetric-vacuum analysis](docs/VALENTINER_SUSY_VACUA.md) and [input audit](docs/FLAVOR_SEARCH_INPUT_AUDIT.md) for assumptions and open derivations.

The [CP-even kinetic freedom proof](docs/FLAVOR_KINETIC_FREEDOM.md) constructs nine real polynomial covariants spanning a complete Hermitian quark metric at a CP-breaking vacuum. Positive bare metrics preserve the scalar vacuum and all six quark masses while changing all four CKM parameters. It also derives a shared non-Abelian source-label contraction and a stable rank-one heavy-family branch. The [scientific receipt](receipts/m22_interactions/flavor_kinetic.json) and [validation](receipts/m22_interactions/flavor_kinetic_validation.json) include 14 positive countermetrics, 32 passing checks and byte-identical fresh replay. The golden relation remains an obligation for full UV kinetic matching.

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

The [joint rank-lifting and physical-CP construction](docs/VALENTINER_ADJOINT_UV.md) minimizes 35 complex flavor fields with all 30 renormalizable scalar channels on the declared slice nonzero. It gives three nonzero quark singular values per sector with universal source couplings, a stable 70-dimensional scalar Hessian and an independently checked physical CP invariant. Five adjoint quartic channels follow from a multiplicity-free representation. The [receipt](receipts/m22_interactions/valentiner_adjoint_uv.json) includes the CP partner, re-minimized UV deformations and fixed-mass kinetic tests; its CKM magnitudes do not match the nominated anchors, and the golden relation remains underived.
