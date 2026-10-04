# Documentation

Start with the [constraint compiler](CONSTRAINT_COMPILER.md) to use PerfectPower, the [worked examples](SHOWCASE_MONOGRAPH.md) to see complete workflows, or the [Python API](../python/README.md) to integrate it into a program. The [mathematical overview](MONOGRAPH.md) explains the arithmetic classification. The [trust boundary](TRUST_BOUNDARY.md) distinguishes compiled theorems, named premises, exact Python computations, bounded evidence, and numerical geometry.

## Arithmetic

| Subject | Guides |
|---|---|
| Constraint plans and complete integer solving | [Compiler](CONSTRAINT_COMPILER.md), [integrated engine and optimization](ENHANCED_MACHINERY_MONOGRAPH.md), [Sturm roots and sharper power gaps](MONOGRAPH_DEVELOPMENT_MONOGRAPH.md), [checked integer-root trees](ROOT_EVENTS_LEAN_MONOGRAPH.md), [factored local filters](LOCALITY_AND_OBSERVABLE_MACHINES.md) |
| Native Lean enumeration | [Getting started](NATIVE_POWER_START_HERE.md), [square-plus-constant polynomials](NATIVE_POLYNOMIAL_MONOGRAPH.md), [Runge squares](NATIVE_RUNGE_MONOGRAPH.md), [higher powers](NATIVE_RUNGE_POWER_MONOGRAPH.md) |
| Quartics and divisor sums | [Effective quartic solver](QUARTIC_EFFECTIVE_SOLVER_MONOGRAPH.md), [divisor route](DIVISOR_REUSE_MONOGRAPH.md), [divisor-sum results](DIVISOR_SUM_RESULTS_MONOGRAPH.md) |
| Mordell curves, descent, and units | [Mordell branch](MORDELL_BRANCH.md), [unit premises](UNIT_PREMISES.md), [weighted norm lists](WEIGHTED_NORM_LISTS.md), [k = 22 proof](K22_PROOF.md) |
| Integer coordinate transport | [Integer lifting](INTEGER_LIFTING_MONOGRAPH.md), [covering lattices](COVERING_LATTICE_MONOGRAPH.md), [multiplicative systems](MONOMIAL_RECOVERY_MONOGRAPH.md), [curve scaling](CURVE_SCALING.md) |
| Other equation reductions | [Literature routes](research/literature-routes-monograph.md), [solution charts](GEOMETRIC_LANGLANDS_CONNECTION.md), [square–cube gap atlas](GAP_ATLAS.md) |

## Solver integration

| Subject | Guides |
|---|---|
| SMT-LIB arithmetic replacement | [Host adapter](HOST_ADAPTER.md), [independent corpus coverage](../independent_nia/reports/PERFECTPOWER_COVERAGE.md) |
| Incremental command replay | [Usage](../industrial_performance/REPLAY_README.md), [measurements and scope](../industrial_performance/REPLAY_MONOGRAPH.md) |
| Software arithmetic workloads | [Why3 and bitvector workflow](ARITHMETIC_WORKFLOW.md), [integer square-root workload](../why3_isqrt/README.md) |

## Operators and sequences

| Subject | Guides |
|---|---|
| Recurrence and operator machinery | [Sequences](SEQUENCE_RECOVERY_MONOGRAPH.md), [operators](OPERATOR_RECOVERY_MONOGRAPH.md), [generated algebras and graph events](MONOGRAPH_DEVELOPMENT_MONOGRAPH.md), [minimal shared output machines](LOCALITY_AND_OBSERVABLE_MACHINES.md), [witness resolvents and graph repairs](WITNESS_RESOLVENTS_AND_GRAPH_REPAIRS.md) |
| Divisor-coordinate operators | [Arithmetic kernels](DIVISOR_KERNEL_RECOVERY_MONOGRAPH.md) |
| Weighted Hodge, power composition, and finite Fourier algebra | [Constructions](DEEP_GEMS_MONOGRAPH.md), [Lean proof map](PARALLEL_LEAN_MONOGRAPH.md) |
| OEIS comparison and definition translation | [OEIS integration](OEIS.md), [definition language](DEFINITION_LANGUAGE.md), [source snapshot](../data/oeis/SOURCE.md) |

## Geometry

| Subject | Guides |
|---|---|
| Exact branching, monodromy, and finite surface models | [Branched geometry](BRANCHED_GEOMETRY_MONOGRAPH.md) |
| Collision strata and connection determinants | [Positive geometry](POSITIVE_GEOMETRY_MONOGRAPH.md), [finite graph-event laws](ROOT_EVENTS_LEAN_MONOGRAPH.md) |
| Differential bases and Legendre period enclosures | [Holomorphic bases](HOLOMORPHIC_BASIS_MONOGRAPH.md) |
| Intrinsic Voronoi and numerical curve geometry | [Analytic geometry](ANALYTIC_GEOMETRY_MONOGRAPH.md), [certified finite surface geometry](CERTIFIED_SURFACE_GEOMETRY.md) |
| Homology cycles, periods, and canonical metrics | [Symplectic analytic geometry](SYMPLECTIC_ANALYTIC_MONOGRAPH.md) |

## Proofs and evidence

The [formal audit](FORMAL_AUDIT.md), [certificate format](CERTIFICATE_FORMAT.md), and [receipt guide](RECEIPTS.md) describe the verification interfaces. Focused proof maps cover [recovered bridges](RECOVERED_LEAN_BRIDGES.md), [sequence foundations](SEQUENCE_RECOVERY_LEAN.md), [operator identities](OPERATOR_RECOVERY_LEAN.md), [geometry and arithmetic foundations](LEAN_BACKLOG_MONOGRAPH.md), and [parallel algebra and lifting](PARALLEL_LEAN_MONOGRAPH.md), and [exceptional searches and generated operator spans](MONOGRAPH_LEAN_MONOGRAPH.md). [Audit and corpus summaries](STATUS.md) retain the generated statistics separately from the main README. Original execution records live in [receipts/](../receipts/).

## Mathematical background and further work

Read [the history](HISTORY.md), [Hilbert's tenth problem](HILBERT10.md), [research notes](RESEARCH_NOTES.md), or [related work](RELATED_WORK.md) for context. The [open-front checkpoint](OPEN_FRONTS.md) tracks implementation obligations; [open problems](OPEN_PROBLEMS.md) and the [frontier plan](FRONTIER_PLAN.md) describe the broader mathematical questions. Detailed monographs retain their experiments, corrections, and provenance.
