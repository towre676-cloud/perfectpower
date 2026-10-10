# PerfectPower 0.9.9: Budget Lab

## What is built

Budget Lab is a working local application for exploring complete public participatory-budgeting elections with PerfectPower's completion planner. It adds a second, unrelated public-data setting to the existing planning work. Users can change a budget, commit arbitrary projects in or out, inspect the exact number of remaining portfolios, request a maximum-support portfolio, open a portfolio by its rank, verify that rank, and draw a seeded uniform sample. The browser exports a JSON result containing the scenario, source provenance and original project ordering.

Run `python START_BUDGET_LAB.py` from the complete repository, then open the printed localhost URL. Alternatively, run `PYTHONPATH=python python -m perfectpower budget-lab`. Default port is 8765; `--port 0` chooses an available port. Python 3.10 or later is required. The native planning backend compiles with g++; this initial compilation is a separate startup cost. No hosted service or account is required. The server binds only to the local loopback interface and runs requests serially.

The deliverable includes the browser interface, Python API, full source datasets, independent benchmark driver, machine-readable receipts and regression tests. This is a local analytical workbench, not a deployment of a municipal voting system.

## Sources and model

Four complete elections are pinned to Pabulib repository commit `4f8497afb2168e732d42f4960307e4a85f9dcc7b`. Original bytes are retained and checked against SHA-256 hashes before opening a session. The manifest also records original Git blob identities and immutable source URLs. See `data/participatory_budgeting/SOURCE.md`, [Pabulib format](https://pabulib.org/format), and the [source repository](https://github.com/pabulib/pabulib_files/tree/4f8497afb2168e732d42f4960307e4a85f9dcc7b/pb_files).

| Election | Projects | Ballots | Original total budget | Vote type |
|---|---:|---:|---:|---|
| Toulouse 2019 | 30 | 1,494 | EUR 1,000,000 | Cumulative |
| Amsterdam Bloemenbuurt 2020 | 24 | 219 | EUR 250,000 | Approval |
| Amsterdam Rijnbuurt West 2022 | 15 | 212 | EUR 100,000 | Approval |
| Warszawa Wesoła 2023 | 29 | 1,181 | PLN 1,011,308 | Approval |

These cases were selected for supported vote types and manageable project counts before measuring timing. They are not a random or representative sample of the whole Pabulib collection. All projects, ballots, published costs and support totals are preserved. Bloemenbuurt has three additional category caps: Jeugd 82,000, Groen 53,000 and Ontmoeting 115,000. Rijnbuurt's published artificial cost of 1 for two free projects is preserved. Wesoła's edition name is 2023, while its voting dates are in June 2022.

A portfolio is a binary vector in the original source project order. Feasibility means total spending and every supported category spending cap are respected, together with explicit user commitments. Budget inputs are converted exactly into scaled integer money units; fractional values are not rounded through binary floating point. Counts are numbers of original portfolios, not merged weight states. Equal-cost or equal-support projects remain distinct.

The analytical objective is the sum of published support of selected projects: project `votes` for approval files and `score` for cumulative files. Published values are retained even if ballot reconstruction disagrees; disagreement is recorded. For these four snapshots all published support values match their ballot aggregates. Total support can count a ballot more than once when it supports multiple selected projects. The distinct represented-ballot count is descriptive and is not the optimization objective. Maximizing additive support does not implement a proportional representation rule or the municipalities' official greedy procedure. Official selected-project flags are shown when present; their absence is explicitly identified.

## Exact query contract

`BudgetElection` validates META, PROJECTS and VOTES sections, declared row counts, distinct project and voter identifiers, ballot references, cumulative points and paired category metadata. The supported contract covers approval and cumulative files, 1–64 projects, and at most 15 category caps. Unsupported neighborhood spending constraints are rejected. It is not a general implementation of every Pabulib extension.

`BudgetSession.evaluate` accepts `view`, `select`, `rank` and `sample` requests. A scenario consists of a scaled integer budget and arbitrary project-ID locks, each exactly 0 or 1. Locking a project removes its variable, subtracts its committed cost from every resource and carries its support into the objective. Free variables retain their original relative order. Results reconstruct the complete original vector. Over-budget commitments have zero feasible portfolios; all-fixed scenarios are handled directly.

Rank is zero-based in the planner's original binary ordering. `select(r)` and `rank(point)` are inverses within the same scenario. Uniform sampling draws a uniform integer rank and selects that portfolio. Sampling a maximum-support solution instead is not what this operation means. An explicit seed gives reproducible pseudorandom draws; an omitted seed uses system randomness. The session keeps a bounded least-recently-used cache of scenarios. Returned lock dictionaries are copies so callers cannot mutate cached scenario identity.

The browser sends large integer budgets, seeds and ranks as canonical decimal strings; the HTTP boundary converts them exactly. Counts and ranks return as decimal strings, avoiding JavaScript's integer precision limit. Binary vector entries remain integers. The API accepts bounded JSON requests, serves only its declared routes and rejects foreign browser origins. Work-limit failures are explicit HTTP 422 responses; they are not presented as a proof of infeasibility. This is a serial local server, without a production authentication, concurrency or deployment layer.

## Independent replication

`python/run_budget_lab.py` runs the same workflow against two different completion-counting engines. PerfectPower uses its existing planner, while the reference uses native original-variable recursive subcube counting. The reference independently computes completion counts and maxima; it shares the presentation layer and rank decomposition. It is consequently an independent counting algorithm, not a wholly independent application implementation.

Each election receives three scenarios: 100%, 90% and 80% of its original total budget. The middle scenario also commits the first source project in and the last project out, testing nonprefix conditioning. Each scenario performs one view, five select/rank pairs and three seeded samples: 14 requests per scenario and **42 per election**. All corresponding output values agree. Inverse ranks are also checked with fresh caches so a previously selected vector cannot hide a broken inverse operation.

Cold trials construct the three scenario planners and execute the complete workflow. Three trials alternate the order of planner and reference. Parsing and native compilation are reported separately and excluded from the workflow timings. Warm trials repeat the same query banks with retained scenario caches; they do not measure unseen-query throughput. The machine-readable ledger records individual samples, compiler identity and flags, source snapshot, exact answers and timing scope.

| Election | Exact full-budget count | Maximum published support | Planner cold median (s) | Recursive cold median (s) | Relative speed |
|---|---:|---:|---:|---:|---:|
| Toulouse | 283,055,991 | 6,490 | 0.082647 | 9.197819 | 111.3× |
| Bloemenbuurt | 6,790,056 | 1,802 | 0.024338 | 0.762232 | 31.3× |
| Rijnbuurt West | 12,138 | 858 | 0.014789 | 0.077217 | 5.2× |
| Wesoła | 275,189,318 | 7,322 | 0.076949 | 11.939223 | 155.2× |

These relative speeds compare the specifically stated 42-request cold workflow against the recursive counting baseline on this machine. They are not universal speedups, an OR-Tools comparison, or evidence of defeating all benchmarks. Native initial compilation took approximately 2.47 seconds in this run. Small durations and only three trials limit precision and portability; the ledger retains raw measurements.

| Election | Planner warm median (s) | Recursive warm median (s) | Planner optimization-only median (s) | OR-Tools optimization-only median (s) |
|---|---:|---:|---:|---:|
| Toulouse | 0.012093 | 0.012326 | 0.000785 | 0.000112 |
| Bloemenbuurt | 0.006073 | 0.006472 | 0.000602 | 0.000132 |
| Rijnbuurt West | 0.003868 | 0.003838 | 0.000315 | 0.000067 |
| Wesoła | 0.015220 | 0.015581 | 0.000531 | 0.000105 |

Warm performance is close and Rijnbuurt's reference is slightly faster. OR-Tools produces the same analytical optimum and is faster for the optimization-only median on all four cases. The value demonstrated here is access to exact completion counts, ranks, inverse ranks and uniform feasible sampling across interactive scenarios. It is not a new claim of superior one-shot optimization.

## Implementation change and verification

The public Toulouse case exposed an automatic backend-selection issue: an estimated capacity grid of millions of states could be chosen despite a smaller configured state limit. The ordinary dynamic-programming gate now also requires its estimated grid to fit that limit before selecting it. Otherwise the existing alternative route remains available. A Toulouse regression checks the independently reproduced count of 283,055,991. No native algorithm or formal theorem was changed to obtain this result.

The focused regression run executed 129 tests: 127 passed and two optional Mathlib-dependent checks were skipped. Coverage includes public source hashes and declared counts; exhaustive tiny rational-cost, category-cap and arbitrary-lock cases; fully fixed and infeasible scenarios; independent rank round trips; seeded sampling; cache eviction and returned-state isolation; strict malformed-input rejection; the public routing regression; and real localhost HTTP requests, including exact large integers, origin rejection and missing routes. Existing planning, hybrid routing, generating-function, arithmetic, telescoping, application and checked-SoE tests were included.

The HTTP application and API are exercised by tests. A full graphical-browser end-to-end run was not completed: the available cloud browser could not reach this container's loopback server, and the local browser executable was unavailable. Therefore this release does not claim screenshot-based layout verification or a completed graphical browser interaction suite. The self-contained frontend is included for local use and its JavaScript syntax is checked separately.

These are executable exact-integer checks and source-bound benchmark receipts. They do not add kernel proofs of the native counting implementation, prove a new complexity result, or certify general municipal decision quality. Previous formal results remain separate from these new application claims.

## Reproduce and extend

Use `make budget-lab-test` for the application regression suite and `make budget-lab-benchmark` for three-trial public replication. The latter requires the optional planning-benchmark dependency for OR-Tools. Full output is in `receipts/budget_lab/benchmark.json`; per-election model receipts sit alongside it. The original `.pb` data and hashes are committed under `data/participatory_budgeting`.

The useful next evidence would be a preregistered, broader supported-data sample, an additional independent exact-counting solver, and unseen-query latency measurements with bounded cache memory. Larger instances may hit explicit work limits; supporting richer election rules requires model extensions and separate validation. The current release establishes a concrete application and four independently replicated public cases. Its defensible claim is stronger practical evidence for exact interactive portfolio exploration.
