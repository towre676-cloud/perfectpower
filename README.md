# PerfectPower

**Exact integer arithmetic, complete solution families, and Lean proof support.**

PerfectPower answers questions such as “when is this polynomial a square?” and “which integers satisfy this arithmetic constraint?” For supported equations, it replaces a candidate-by-candidate search with a complete finite answer or an exact structured generator. Supported solution spaces can be restricted by polynomial and modular conditions, counted, queried by rank and optimized in their original coordinates. When global solving remains unresolved, it can still return necessary congruences, a smaller equivalent problem, or a complete bounded answer. Results describe their mathematical justification and any remaining assumptions.

The core combines a Python constraint compiler with a Lean 4 library. It handles polynomial perfect powers, Pell equations, selected Mordell curves, effective quartic and Runge families, and exact changes of integer coordinates. Related modules provide integer lattice solving and optimization, operator algebras, sequence comparisons, and branched-curve geometry.

## Quick start

Requires **Python 3.10 or later**. The core Python package has no runtime dependencies. Run from a repository checkout so the compiler can access the accompanying data and proof records.

```sh
git clone https://github.com/towre676-cloud/perfectpower.git
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

The function API exposes the same constraint plans:

```python
from perfectpower.compiler import PowerConstraint, compile_constraint

plan = compile_constraint(PowerConstraint([-345, 735, -525, 125], 2))
print(plan.answer)      # complete_list
print(plan.all_hits())  # [(2, [-5, 5])]
```

See the [Python API](python/README.md), [constraint compiler guide](docs/CONSTRAINT_COMPILER.md), and [worked examples](docs/SHOWCASE_MONOGRAPH.md). Run `python -m perfectpower --help` for the full command list.

## What it does

For configuration generation and mathematical datasets, the new [`ExactPopulation`](docs/POPULATION_MONOGRAPH.md) interface compiles a finite supported domain or curve into a reusable object. It counts, selects and locates original objects by rank, samples without replacement, partitions work into balanced rank shards and exports seeded JSONL datasets. Run `python -m perfectpower population --spec receipts/populations/compatible_layouts.spec.json` for a configuration example. The [application roadmap](docs/DIRECT_USE_BUILD_ROADMAP.md) connects this common layer to the proposed direct uses.

The [open-content release](docs/OPEN_CONTENT_MONOGRAPH.md) adds eight persistent object kinds, a local HTTP console, inequality-constrained integer calibration, globally cheapest distinguishing experiments, exact graph sampling for cyclotomic orders 2 through 64, nonlinear factorial-ratio execution, distinct-value populations, huge symbolic joins, whole-family task splits and certified local chart transitions. Run `python python/develop_open_content.py --output /tmp/pp-open` or `python -m perfectpower service --database /tmp/pp.sqlite --http-port 8080`. [Full receipts](receipts/open_content/summary.json) include 504 graph samples, 52 nonlinear families and 512 tasks. Compatible C tiles beat the conventional dot-product examples, while the cache-friendly untiled C control is faster still. The [earlier Python demo](docs/APPLICATIONS_MONOGRAPH.md) remains historical evidence. Exact flavor diagnostics expose coefficient constraints and an allowed deformation; general effective arithmetic, global smooth geometry and physical derivations remain open. See the [dense roadmap](docs/DIRECT_USE_BUILD_ROADMAP.md) and [handoff](CLAUDE_CODE_APPLICATIONS_START_HERE.md). The full archive has no size cap.

| Task | Interface | Guide |
|---|---|---|
| Compile polynomial power, triangular-number, and quadratic-root constraints | `solve`, `prove` | [Constraint compiler](docs/CONSTRAINT_COMPILER.md) |
| Classify and count perfect-power hits; generate Pell and radical families | `classify`, `count`, `enumerate` | [Mathematical overview](docs/MONOGRAPH.md) |
| Solve supported polynomial equations over all integers | `exact-solve`, `square-fibres`, `integer-roots` | [Arithmetic engine](docs/ENHANCED_MACHINERY_MONOGRAPH.md), [roots and search bounds](docs/MONOGRAPH_DEVELOPMENT_MONOGRAPH.md) |
| Discover polynomial coordinates; solve integer sign domains and global polynomial optimization | `polynomial-decompose`, `polynomial-relation`, `polynomial-domain`, `polynomial-optimize` | [Polynomial capacity](docs/POLYNOMIAL_CAPACITY_MONOGRAPH.md) |
| Count and select polynomial/modular domains; query signed power curves and composed generators | `semilinear-domain`, `semilinear-optimize`, `polynomial-charts`, `curve-query`, `family-evaluate` | [Semilinear capacity](docs/SEMILINEAR_CAPACITY_MONOGRAPH.md) |
| Query coefficient-bearing power families, reuse integer fibres and count modular recurrence domains | `coefficient-charts`, `curve-query`, `recurrence-orbit`, Python `CurveSpace` | [Reusable query spaces](docs/QUERY_SPACE_MONOGRAPH.md) |
| Compile Gamma shifts, factorials and binomial inputs; test factorial-ratio powers and derive exact hypergeometric recurrences | `gamma-analyze`, `gamma-unit`, `gamma-domain`, `gamma-optimize` | [Gamma arithmetic](docs/GAMMA_ARITHMETIC_MONOGRAPH.md) |
| Compose arithmetic reductions and recover original models; retain partial and bounded information | `simplify-query`, `analyze-power`, `polynomial-pullback` | [Arithmetic simplifier](docs/ARITHMETIC_SIMPLIFIER_MONOGRAPH.md) |
| Search a bounded power range using factored local filters | `factored-scan` | [Local arithmetic filters](docs/LOCALITY_AND_OBSERVABLE_MACHINES.md) |
| Solve exact integer linear systems and find every tied nearest lattice point | `integer-lift`, `nearest-lift` | [Integer coordinates](docs/INTEGER_LIFTING_MONOGRAPH.md), [optimization](docs/ENHANCED_MACHINERY_MONOGRAPH.md) |
| Analyze operators and share exact state machines across recurrence models | `recurrence-batch`, `observable-machine`, `integral-machine`, `operator-algebra` | [Shared output machines](docs/LOCALITY_AND_OBSERVABLE_MACHINES.md), [integer states and congruences](docs/INTEGRAL_OUTPUT_MACHINES.md), [operator algebras](docs/MONOGRAPH_DEVELOPMENT_MONOGRAPH.md) |
| Certify matrix-output generating functions and sampled subsequences | `witness-resolvent` | [Witness resolvents](docs/WITNESS_RESOLVENTS_AND_GRAPH_REPAIRS.md) |
| Query graph events and update edge weights without enumerating every basis | `connection-measure`, `connection-reweight` | [Graph measures](docs/MONOGRAPH_DEVELOPMENT_MONOGRAPH.md), [weight repairs](docs/WITNESS_RESOLVENTS_AND_GRAPH_REPAIRS.md) |
| Compute branched-cover topology, differentials, and surface geometry | `branched-geometry`, `legendre-period-bounds`, `intrinsic-voronoi` | [Geometry documentation](docs/README.md#geometry) |
| Compare arithmetic families with local OEIS records | `oeis`, `sequence-atlas` | [OEIS integration](docs/OEIS.md) |

For solver integration, the [SMT adapter](docs/HOST_ADAPTER.md) replaces recognized arithmetic relations with their complete solution sets. The separate [incremental replay tool](industrial_performance/REPLAY_README.md) handles SMT-LIB command transport. Coverage and performance measurements are documented with their workloads in those guides.

For example, `curve-query --left '[1,0,-2,0,1]' --right '[0,0,0,1]' --objective 'x*x+y*y' --verify` solves `(x²−1)²=y³` completely and returns all three tied minimizers. The [new corpus](receipts/semilinear_capacity/summary.json) closes 262 finite-image presentations, including 238 previously unresolved cases, and independently checks 3,080 constrained quartic optima and 676 Bober recurrence domains. See the [monograph](docs/SEMILINEAR_CAPACITY_MONOGRAPH.md) for the defined workloads and proof scope.

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
**A complete mathematical answer and a formally verified program are separate guarantees.** Inspect the result's certificate for the theorem names, premises, domain, and reduction steps. Lean checks the statements of compiled theorems. Python discovers and executes plans and can replay exact certificates, but its execution is not formally verified. Emitted Lean source becomes a checked theorem only after compilation.

Some modules return bounded evidence or numerical approximations. A bounded scan does not establish global completeness, and a numerical period matrix does not certify analytic error bounds. General polynomial integer solving remains outside the supported scope. The [trust boundary](docs/TRUST_BOUNDARY.md), [certificate format](docs/CERTIFICATE_FORMAT.md), and each module's guide describe the precise guarantees.

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

`make test` runs the Python suites across the repository. `make verify` builds Lean, checks axioms, runs tests, regenerates receipts and [status summaries](docs/STATUS.md), and checks for drift. Individual formalization guides provide focused check scripts. Optional SMT integration dependencies install with `python -m pip install '.[industrial]'`; numerical geometry dependencies are described in its [guide](docs/ANALYTIC_GEOMETRY_MONOGRAPH.md).

## Documentation and license

The [documentation index](docs/README.md) organizes the mathematical accounts, implementation guides, proof audits, and benchmark reports by subject. For context, read [the history of perfect powers](docs/HISTORY.md) or [computation and the limits of solving equations](docs/HILBERT10.md).

Code and Lean sources use [Apache-2.0](LICENSE); documentation and papers use [CC BY 4.0](LICENSE-docs). The included OEIS records retain their [source attribution and CC BY-SA 4.0 license](data/oeis/SOURCE.md). Citation metadata is in [CITATION.cff](CITATION.cff).
