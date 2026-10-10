# PerfectPower

**Exact polynomial arithmetic, queryable solution spaces, and algebraic-curve computation with Lean 4 proofs.**

PerfectPower began with a question: when is a polynomial value a perfect power? It now provides reusable machinery for solving supported integer equations, counting and querying structured solution families, and studying the algebraic curves defined by those equations. A reduction retains the original coordinates, divisibility conditions and domain, so its answer can be used by another program.

The project combines a Python package, exact algebra engines, a Lean 4 theorem library and reproducible research corpora. Its outputs include complete solution lists and generators, direct access to large finite populations, exact optimization policies, elliptic division fibres, and differential equations derived from polynomial curve families. Each operation states its supported inputs and the guarantee attached to its result.

## Quick start

Requires **Python 3.10 or later**. The core package uses the standard library; numerical geometry, interval arithmetic and solver integrations have optional dependencies. Install from a repository checkout to retain the accompanying data and proof records. Work is published on `main`; the GitHub default branch `claude/laughing-lamport-qqzdo9` is kept at the same commit.

Version 0.9.0 wheels also include the runtime certificates, mathematical source statements, core data and offline atlas. A source checkout is required for the full research corpus and historical build, but ordinary installed arithmetic and the atlas no longer require it. Install optional features with `.[analytic]`, `.[intervals]`, `.[industrial]` or `.[research]`.

```sh
git clone https://github.com/towre676-cloud/perfectpower.git
cd perfectpower
python -m pip install .
python -m perfectpower solve --expr '(5*n - 7)**3 - 2'
```

This asks when `(5n − 7)³ − 2` is a square for `n ≥ 1`. The complete answer is **`n = 2`**, with square roots **`−5` and `5`**. The compiler reduces the problem to `y² = x³ − 2` while preserving the restriction on the original input.

For supported equations over all integer coordinates, use `exact-solve`. Coefficients are listed from the constant term upward:

```sh
python -m perfectpower exact-solve --coeff '[-199,1,1,1,1]' --d 2 --verify
```

This solves `y² = x⁴ + x³ + x² + x − 199`, returning exactly **`(x,y) = (7,−51)` and `(7,51)`**. Here `--verify` replays the Python certificate. See the [Python API](python/README.md), [compiler guide](docs/CONSTRAINT_COMPILER.md) and [worked examples](docs/SHOWCASE_MONOGRAPH.md), or run `python -m perfectpower --help`.

## Integer arithmetic and elliptic curves

The arithmetic compiler recognizes supported polynomial power relations, Pell families, effective quartics and selected Mordell equations. It can count or generate solutions, impose polynomial and modular restrictions, optimize an objective and recover the original coordinates. [Integer lifting](docs/INTEGER_LIFTING_MONOGRAPH.md) and [monomial recovery](docs/MONOMIAL_RECOVERY_MONOGRAPH.md) extend this approach to additive and multiplicative constraint systems.

[Prime-power residue atlases](docs/RESIDUE_ATLAS_MONOGRAPH.md) retain complete local root tables, including singular branches. Their [factored intersections](docs/RESIDUE_ATLAS_INTERSECTION_FACTORED_MONOGRAPH.md) support exact counts and rank selection in large rectangles. [Rational arithmetic charts](docs/ARITHMETIC_CHART_PIPELINE_MONOGRAPH.md) preserve denominator and integrality conditions through coordinate changes. Local candidate sets and complete bounded solutions have explicit, separate meanings.

[Fixed divisors](docs/FIXED_DIVISOR_MONOGRAPH.md), [integer-valued rational polynomials](docs/INTEGER_VALUED_POLYNOMIAL_MONOGRAPH.md) and [Gamma arithmetic](docs/GAMMA_ARITHMETIC_MONOGRAPH.md) connect universal divisibility, binomial polynomials, fixed-width products, factorial valuations and modular execution. These routes retain the domain on which a rational expression is an integer.

The [elliptic interface](docs/ELLIPTIC_WITNESSES_MONOGRAPH.md) supplies exact generalized Weierstrass arithmetic, rational model transport, isogenies and rational division. [Subgroup preimages and bounded saturation](docs/ELEVENTHIRTEEN_CAPACITY_MONOGRAPH.md) support primes 2, 3, 5, 7, 11 and 13. [Torsion-aware indices](docs/TORSION_INDEX_PELL7_MONOGRAPH.md) distinguish actual point-group enlargement from a coefficient-lattice index. The Mordell frontier records 457 ranks determined by equal external PARI bounds, with matching explicit point witnesses for all 457 and zero constructive witness gaps; [Full saturation and integral enumeration](docs/MORDELL_COMPLETION_MONOGRAPH.md) now establish complete bases and integral lists for all 457 by external computation, with 788 native exact prime-saturation checks. The lists contain 270 signed points on 134 curves; 323 curves are empty. Global completeness remains outside Lean. [Binary invariant contractions and cover reduction](docs/BINARY_INVARIANTS_MONOGRAPH.md) construct exact covariants, retain transformed covering maps, and have supplied two further frontier witnesses. [Exact Mordell 3-isogenies](docs/MORDELL_ISOGENY_WITNESSES_MONOGRAPH.md) and a longer cover search close another 85 gaps, including the missing rank-two direction at k=-9257. [Pinned published coordinates and exact independent checks](docs/MORDELL_WITNESS_CLOSURE_MONOGRAPH.md) close the final five gaps.

### Solution families and populations

The [polynomial population interface](docs/POLYNOMIAL_POPULATION_MONOGRAPH.md) proves reusable polynomial interpretation, coordinate substitution, restriction composition, rank/selection inverses, and complete bivariate minimum tie sets. `checked-population` certifies batches of queries against one bounded original-equation source; its stated interval remains part of the guarantee.

The [global population bridge](docs/GLOBAL_POPULATION_MONOGRAPH.md) connects the proved curve `y²=x³−2` and its nonzero affine input pullbacks to globally complete queries. `checked-global-population` preserves divisibility and integer, nonnegative, or positive domains without a search interval.

The [nonlinear and Pell population extension](docs/EXTENDED_POPULATION_MONOGRAPH.md) proves complete polynomial input fibres for the −2 and −4 Mordell sources and exact cutoff queries for the nonnegative D=2 Pell orbit. `checked-nonlinear-population` gives global original-coordinate answers; `checked-pell-population` gives complete cutoff counts and global recurrence selections.

The [broad family engine](docs/FAMILY_ENGINE_MONOGRAPH.md) adds globally complete square-plus-constant equations, divisor-based fibres, five classical Mordell sources and a 1,026-offset emptiness atlas. General-D Pell queries include all signs, exact count-only access, binary-powered global selections and supported optimization without a cutoff.

The [automatic reductions and multiple-orbit engine](docs/ORBIT_REDUCTION_MONOGRAPH.md) recognizes supported original polynomials, queries generalized Pell equations with every checked seed, and gives binary-powered selections within each orbit. The same push proves saturation at 2 of the retained rational bases for all 457 hard census curves; complete curve-specific rank and integral-point proofs remain open.

## Queryable populations and decision policies

[`ExactPopulation`](docs/POPULATION_MONOGRAPH.md) turns a supported finite domain into a query space: count its objects, select one by rank, locate an object, page through a range, sample without replacement or partition work into rank shards. [Curve queries](docs/QUERY_SPACE_MONOGRAPH.md) and [semilinear domains](docs/SEMILINEAR_CAPACITY_MONOGRAPH.md) expose related restrictions and optimization operations. The supported structure can make a population accessible without materializing every member.

[`PopulationComparison`](docs/POPULATION_ALGEBRA_MONOGRAPH.md) compares two predicates in a common finite universe. It provides intersections, differences, complements, unions and symmetric differences with exact counts, stable original-object IDs and address transport. The CLI and persistent service expose the same operations. Fourteen generic partition and transport theorems compile in Lean; verification of the Python compiler remains separate.

The [room of possibilities](web/room-of-possibilities/README.md) is a self-contained interactive 3D walkthrough, with a fictional machine workshop and real exported arithmetic populations. Open its offline HTML, or run `python -m perfectpower service --database pp.sqlite --http-port 8080` from this checkout and visit `http://127.0.0.1:8080/atlas` to replay the comparison through Python. Reproduction: `make population-algebra` and `make population-algebra-lean`.

[`CalibrationPolicy` and `DiagnosticPolicy`](docs/DECISION_POLICIES_MONOGRAPH.md) compile entire operating policies. Calibration computes all nearest-setting regions and ties on a declared one- or two-dimensional target slice. Diagnostics minimizes worst-case adaptive experiment cost for a declared finite, noiseless, resettable model. [Observable machines](docs/LOCALITY_AND_OBSERVABLE_MACHINES.md) share recurrence state and construct separating experiments. Optional [SMT integration](docs/HOST_ADAPTER.md) and [incremental replay](industrial_performance/REPLAY_README.md) have workload-specific performance reports.

The [persistent catalogue](docs/OPEN_CONTENT_MONOGRAPH.md) stores immutable definitions with aliases and exposes supported operations through JSONL and a local HTTP console:

```sh
python -m perfectpower service --database /tmp/pp.sqlite --http-port 8080
```

## Geometry from the defining polynomial

[`CurveFamily`](docs/CURVE_FAMILIES_MONOGRAPH.md) derives exact discriminants, Gauss–Manin connections and observable Picard–Fuchs equations for supported polynomial families. Its [structural operations](docs/CURVE_STRUCTURE_MONOGRAPH.md) explain coefficient deformation, root motion, collisions and explicit elliptic quotients. For example:

```python
from perfectpower.curve_families import CurveFamily

# y² = x⁵ − x + t; both coefficient lists are constant-first.
family = CurveFamily({"coefficients": [[0, 1], [-1], [0], [0], [0], [1]]})
print(family.deformation()["coordinate_only_generic"])  # False
print(family.collisions()["covered_simple_roots"])      # 4
print(family.observable()["order"])                     # 4
```

[Algebraic curve execution](docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.md) adds finite étale differential algebras, local degeneration charts, logarithmic Frobenius jets and verified finite-symmetry quotients. The [literature execution guide](docs/LITERATURE_CURVE_EXECUTION_MONOGRAPH.md) connects these operations to quotient towers, explicit isogeny kernels, superelliptic periods and arithmetic Frobenius. The merged extensions include [certified continuation](docs/CURVE_CERTIFIED_CONTINUATION_MONOGRAPH.md), [complex genus-two periods](docs/GENUS2_COMPLEX_PERIODS_MONOGRAPH.md), and [singular Richelot correspondences and cluster reduction](docs/SINGULAR_RICHELOT_AND_CLUSTERS_MONOGRAPH.md). Local arithmetic extends to [dyadic reduction and tame extension clusters](docs/DYADIC_REDUCTION_AND_STOKES_MONOGRAPH.md) and [wild conductors](docs/WILD_CONDUCTORS_MONOGRAPH.md). Irregular singular points have [certified Stokes matrices](docs/IRREGULAR_STOKES_GENERAL_MONOGRAPH.md).

[Branched topology](docs/BRANCHED_GEOMETRY_MONOGRAPH.md), [analytic geometry](docs/ANALYTIC_GEOMETRY_MONOGRAPH.md) and [Voronoi enclosures](docs/VORONOI_ENCLOSURE_MONOGRAPH.md) provide additional views of the same equations. Exact algebraic identities, certified continuation in supported charts, polyhedral bounds and numerical smooth-surface calculations carry different guarantees. General certified smooth-curve Voronoi boundaries and arbitrary marked period matrices remain open.

## Structural algebra and observable machines

The [generating-function layer](docs/GENERATING_FUNCTIONS_MONOGRAPH.md) adds exact large-index rational coefficients, restricted weighted-budget populations with lexicographic rank/selection, positive-cost action-word series and direct DynaComp response exports. Cost-specific operator identities preserve every coefficient through an exact quotient. General theta/Weyl coefficient compilation connects the existing period operators to sequence arithmetic; bounded WZ search checks rational shift identities while retaining the separate boundary obligation. Run `make generating-functions` and `make generating-functions-kernel` for the examples and standard-library Lean foundation.

The [PSG structural algebra](docs/PSG_STRUCTURAL_MONOGRAPH.md) adds quadratic elimination with complete auxiliary reconstruction, original-coordinate affine norm populations, exact Darboux cofactor identities, parameter-dependency witnesses, rational observation fibres and finite differential-model spaces. Seven `psg-*` console commands expose the standard-library implementation. The recovered PSG source matches the existing 100-term polynomial exactly; all six supplied invariant factors replay. New Lean sources are emitted, with compilation status recorded separately.

The [enhanced SOE bridge](docs/SOE_BRIDGE_MONOGRAPH.md) preserves finite implementation fibres, composes count/mass/min-plus transports, minimizes future-equivalent state models, compares different models with shortest counterexamples, and computes optimal adaptive diagnosis policies over declared probes. Six `soe-*` console routes also expose reversible polynomial charts with exact derivative transport. These interfaces use exact standard-library arithmetic; finite carrier and probe-menu scopes remain explicit.

The [Gamma kernel bridges](docs/GAMMA_KERNEL_BRIDGES_MONOGRAPH.md) prove the general residue-block factorial-unit algorithm and the sufficient Landau integrality direction. Reconstructed checks certify original factorial units and integrality at every natural index; the converse and Python refinement remain open.

The [structural mathematics extension](docs/STRUCTURAL_MATH_MONOGRAPH.md) adds prime-exponent species populations, exact rational polynomial bounds, singular-aware PSD and Toeplitz certificates, linear Lyapunov metrics and native two-isogeny rank bounds for supported rational-two-torsion curves. Run `make structural-math` to regenerate its corpus, including exact PSG bounds and 306 curve models. These results use exact Python arithmetic and classical descent; the new certificates do not claim Lean verification.

## Proofs and result guarantees

`checked-box` emits a complete original-equation certificate for arbitrary integer polynomials through degree 32 and exponents 2 through 16, within an explicit work budget. Supplying only an x interval means **all integer y**: Lean checks a finite polynomial-value bound and derives the complete signed-root range. Supplying `--y` instead retains that rectangle as part of the theorem. Counts, selected ranks, reverse ranks and polynomial minima with every tied point have checked instances. The small foundation imports only Lean's standard library; Mathlib is unnecessary for this route.

```sh
python -m perfectpower checked-box --coeff '[-2,0,0,1]' --d 2 --x '[-2,5]' --ranks '[0,1]' --objective '[0,1]' --check
```

This checks exactly `(3,-5)` and `(3,5)` for the stated x interval. `--check` requires Lean 4.20.0 and exits unsuccessfully when acceptance fails. Emission alone is a proposal. Successful acceptance proves the reconstructed theorem; it does not verify the Python compiler or JSON parser. See [the release monograph](docs/RELEASE_HARDENING_MONOGRAPH.md) and the [current 25-finding contract](contracts/current_frontier.json). This contract separates implemented repairs, bounded proof extensions and open mathematical obligations.

<a id="the-four-answers"></a>
Constraint plans report `complete_list` when every solution in the stated domain is listed, `generator` for an exact structured family, `conditional` when completeness depends on named premises, and `unresolved` when the available method does not establish a complete answer. Bounded operations state their bounds; exhausting a work budget does not turn an incomplete search into a complete result.

<a id="what-to-trust-at-a-glance"></a>
**A complete mathematical answer and a formally verified program are separate guarantees.** Lean checks compiled theorem statements. Python discovers and executes plans and replays certificates; its general execution is not formally verified. Generated Lean source becomes a checked theorem after compilation. External rank computations, paper proofs, exact Python calculations and numerical experiments retain their own evidence labels.

The [trust boundary](docs/TRUST_BOUNDARY.md), [certificate format](docs/CERTIFICATE_FORMAT.md) and [audit summaries](docs/STATUS.md) explain the evidence. Module guides name remaining premises and implementation obligations. General polynomial integer solving, native global elliptic saturation proofs and arbitrary algebraic-curve compilation remain outside the delivered scope.

### Formal bridges

The [Mordell formal bridge](docs/MORDELL_FORMAL_BRIDGE_MONOGRAPH.md) proves saturation composition and finite-box enumeration in Lean. Its ten audited theorems leave curve-specific rank upper bounds, global saturation prime support and global integral-coordinate bounds explicit; no external receipt is promoted to an unconditional formal closure.

The [rational descent arithmetic bridges](docs/DESCENT_BRIDGES_MONOGRAPH.md) derive primitive quartic covers from actual rational points, prove prime-power chart exhaustiveness, and audit 2,651 declarations, including 1,478 excluded covers across 576 retained curve models. Isogeny coordinate identities and a corrected group-index equation are proved separately; the subsequent [actual point-group isogeny proofs](docs/ISOGENY_POINT_GROUPS_MONOGRAPH.md) prove addition compatibility and normalized dual composition. Their rank bridge requires an explicit free-plus-finite decomposition; squareclass quotient identification and unconditional Mordell–Weil rank remain open. Reproduce with `make descent-bridges-kernel` and `make isogeny-point-groups-kernel`.

The [recovered-work Lean closure](docs/NEW_WORK_LEAN_MONOGRAPH.md) audits 384 declarations, including all-future quotient completeness for 324 partial machines and the exact two-versus-three adaptive diagnosis advantage. PSG algebra and retained rational matrix/energy identities compile; the classical two-isogeny rank identity remains a separate formalization task. Reproduce with `make new-work-kernel`.

SOE finite partial machines can request source-bound Lean acceptance with `soe-states model.json --kernel-check`. Pair-specific experiments prove the coarsest all-future quotient for supported supplied models; see [the compiler contract and resource limits](docs/SOE_GENERIC_LEAN_MONOGRAPH.md).

## Research applications

The [Dresden numerical module](docs/DRESDEN_NUMERICAL_MONOGRAPH.md) applies the arithmetic machinery to exact calendar conversion, phase intersections, bounded date populations, Venus corrections and lunar interval reconstruction. The React/Three.js [Dresden Codex Observatory](https://dresden-codex-observatory.towre676.chatgpt.site) provides interactive source and numerical views, with WebGPU preferred and WebGL 2 fallback. Source readings, exact calendar models and physical or historical interpretation remain explicitly distinguished.

The [representation and flavor program](docs/VALENTINER_CANONICAL_RESULTS.md) uses finite-group arithmetic, polynomial invariants and scalar-potential calculations to study declared particle-physics models. Its [frame calculation](docs/VALENTINER_DIRECT_STABILIZER_AND_THREE_CURVES.md), [whole-line wall certificate](docs/WALL_PROFILE_INTERVAL_MONOGRAPH.md), [thermal cooling](docs/WALL_COOLING_AND_LOCALIZED_HIGGS.md), [source formation](docs/WALL_KIBBLE_ZUREK_FORMATION.md), [wall dynamics](docs/WALL_MODE_LIFETIME_MONOGRAPH.md), [gauged decay widths](docs/WALL_MODE_VECTOR_WIDTHS_MONOGRAPH.md), [network asymptotics](docs/WALL_NETWORK_ASYMPTOTICS_MONOGRAPH.md) and [two-loop and interval-certified nucleation](docs/WALL_TWO_LOOP_AND_INTERVAL_BOUNCES_MONOGRAPH.md) have separate proofs and numerical receipts. The [prediction-mechanism study](docs/FLAVOR_PREDICTION_MECHANISMS.md) proves in Lean that the five declared rays exhaust the real scalar restriction, explains their mixing degeneracy, and supplies exact spectral-moment recovery and conditional gauge-unification calculations. [The physics-lane ledger](docs/PHYSICS_LANE.md) records which wall uses which declared inputs and what an end-to-end benchmark still needs. These models do not yet predict the observed CKM parameters or fine-structure constant; fitted inputs and approximation limits are documented in the research chapters.

The [Weil representation work](docs/WEIL_SPECTRAL_MONOGRAPH.md) supplies exact Fourier/chirp commutants, orbit dimensions and spectral projectors, with [Lean matrix foundations](docs/WEIL_MONOMIAL_MONOGRAPH.md) and explicitly identified all-level formalization obligations. These applications share the project's arithmetic and algebra infrastructure.

## Build and documentation

Run the core package's tests from the checkout:

```sh
PYTHONPATH=python python -m unittest discover -s python/tests
```

Some research suites require optional dependencies. Numerical geometry uses `python/requirements-analytic.txt`; certified wall and continuation calculations use `python/requirements-wall-intervals.txt`. Solver integration installs with `python -m pip install '.[industrial]'`. Consult each module's guide for external tools and focused reproduction commands.

Lean and Mathlib are pinned to **4.20.0**. With [elan](https://github.com/leanprover/elan) installed, fetch Mathlib's cache and run the build script, which schedules memory-heavy generated proofs sequentially:

```sh
lake exe cache get
make lean
```

`make test` runs Python suites across the repository. `make verify` builds Lean, checks axioms, runs tests, regenerates receipts and status summaries, and checks for drift. The [documentation index](docs/README.md) organizes the mathematical accounts, implementation guides and benchmark reports. Start with the [overview monograph](docs/MONOGRAPH.md) for the original mathematics, the [showcase](docs/SHOWCASE_MONOGRAPH.md) for examples, or the [frontier status](docs/FRONTIER.md), generated from the [status contract](contracts/current_frontier.json), for what is open. `make check-integrity` checks every documentation link and recorded data hash.

Code and Lean sources use [Apache-2.0](LICENSE); documentation and papers use [CC BY 4.0](LICENSE-docs). Included OEIS records retain their [source attribution and CC BY-SA 4.0 license](data/oeis/SOURCE.md). Citation metadata is in [CITATION.cff](CITATION.cff).

## Biological sequence exploration

The BLAST polynomial atlas imports NCBI tracebacks, reconstructs exact finite alignment families, maps scoring sensitivity, enforces conserved motifs and coherent-fragment constraints, and connects to the existing SOE, polynomial and graph machinery. The branch includes a real public insulin-transcript example and an offline interactive atlas. See [the monograph](docs/BLAST_POLYNOMIAL_ATLAS_MONOGRAPH.md) and [the runnable workflow](CLAUDE_CODE_BLAST_START_HERE.md). Run `make blast-test` and `make blast-atlas`; kernel scope and build evidence are recorded separately.
