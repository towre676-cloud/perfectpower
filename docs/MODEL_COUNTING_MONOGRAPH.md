# PerfectPower 0.10.0: exact CNF counting on competition data

## The deliverable

This release builds a general exact unweighted CNF counting path, replacing the input-format gap that prevented the existing allocation planner from being tested on the Model Counting Competition. It includes a strict DIMACS parser, a native exact counter, conditional completion queries, original-variable ranking and inverse ranking, seeded uniform sampling, a source-bound public-data downloader, pinned competing binaries and a serial benchmark runner. The allocation planner and Budget Lab remain available as separate interfaces.

The engineering goal is a practical test against recognizable external problems and established independent solvers. The result does not establish a new complexity theorem, a formal proof of the native implementation, or a general victory over existing counters. Funding significance depends on the measured scope and on whether a useful advantage survives independent replication.

## Running it

Install Python 3.10 or later, a C++17 compiler and Boost headers. On a conventional Debian/Ubuntu environment the native requirements are `g++` and `libboost-dev`. The CNF backend is optional: other package commands do not compile it. Set `PP_CNF_BOOST_INCLUDE` to a nonstandard Boost include directory when needed. On first use the source is compiled into a temporary shared library whose filename is its source SHA-256. Build failure is an explicit work-limit error rather than a count of zero. Native source and small public fixtures are included in the wheel as runtime assets.

From the checkout:

```sh
PYTHONPATH=python python -m perfectpower model-count data/model_counting/fixtures/mc2024_track1_118.cnf
```

The extracted repository also provides `python START_MODEL_COUNTING.py input.cnf`. The command returns JSON with `status`, an exact decimal `count`, and execution counters. `--assume -1 --assume 3` fixes original variables 1 false and 3 true. `--timeout` sets a cooperative native query deadline; individual operations can overrun it and `--cache-mib` sets the retained component-cache budget estimate. A work limit produces `WORK_LIMIT`, never `EXACT` with a fabricated answer. For strict end-to-end wall time and process memory boundaries, use the benchmark runner's subprocess wrapper.

```python
from perfectpower.model_counting import CNF, CNFCounter

formula = CNF.read("example.cnf")
with CNFCounter(formula) as counter:
    population = counter.count([-1])
    point = counter.select(0, [-1])
    assert counter.rank(point, [-1]) == 0
    sample = counter.sample([-1], seed=37)
```

Points have one binary entry for every declared original variable, including variables absent from all clauses. Rank is zero-based lexicographic order with 0 before 1, within the conditional population. Arbitrary assumptions restrict that population. Repeated assumptions do not create additional variables; contradictory assumptions give an exact zero count. Sampling selects a uniformly drawn integer rank, yielding uniform original models. Seeding provides reproducible pseudorandom samples; omitted seeds use system randomness.

## Exact semantics

The parser requires a single `p cnf` header and terminated clauses matching the declared original clause count. It permits clauses spanning lines and multiple clauses on a line. Empty clauses are contradictions. Repeated literals and duplicate clauses are normalized; tautological clauses are removed. These transformations preserve the full set of models and the declared variable universe. Variables absent from the normalized formula still contribute their factor of two unless fixed by an assumption.

Weighted and explicitly projected formats are outside this release's contract. The counter does not claim to support the competition's weighted, projected, complex or approximate tracks. Ordinary comments, including independent-support hints in unweighted inputs, do not change the original-variable count. The supported input limits are 200,000 declared variables, 2,000,000 original clauses and 64 MiB of UTF-8 DIMACS text. Files beyond these boundaries remain in the benchmark ledger as explicit work-limit outcomes.

## Native algorithms and reuse

The native fold uses exact Boost multiprecision integers. Unit propagation fixes forced values and detects contradiction. Unconstrained variables contribute exact powers of two. Connected components multiply; a decision variable's two branches add. No SAT-style pure-literal elimination is used, because preserving satisfiability alone does not preserve model counts.

A deterministic cache stores complete normalized clause strings and their exact component counts. It does not accept hash fingerprints as proof of equality: the hash table checks full keys. Dense local relabeling is a bijective variable renaming and only shares counts, not original output vectors. Original-variable selection remains at the API boundary through exact conditional counts.

Two structured routes supplement recursive counting. Complete parity truth-table groups can be recognized and solved by binary Gaussian elimination. Recognition requires every forbidden assignment of one parity, with no incomplete group accepted as a parity equation. Separately, exact sum-product variable elimination combines clause factors and sums over variables. It plans an elimination order before allocating tables, requiring at most 18 variables in a combined scope and an estimated eight million table states. Otherwise it returns to component decomposition and branching. The initial implementation restricts this table route to at most 256 active variables and clause scopes of at most 12 variables.

These are established algorithm families assembled into a hybrid implementation. For background, see Rina Dechter's [bucket-elimination framework](https://doi.org/10.1016/S0004-3702(99)00059-4). The work does not present variable elimination or component caching as a new invention. Search depth, node, time and allocation limits bound execution. Completed cache entries can survive an interrupted query; a partially computed count is never stored as an exact completed entry.

## Dataset and competing methods

All 200 original 2024 Track 1 instances were downloaded and verified against the organizers' SHA-1 list, then bound to SHA-256 identities. The archived dataset is [DOI 10.5281/zenodo.14249068](https://zenodo.org/records/14249068). The original even/public and odd/evaluation labels are preserved. Public fixtures and a short public-only exploratory run informed development. The final counter source was frozen before the full serial comparison; formerly private odd cases were not used for implementation tuning. They are historical public data today, not a fresh blinded evaluation or future competition entry.

The references are Ganak 2.8.0 in deterministic `--prob 0` mode and D4's `d4_regular2` official 2024 submission. Their complete archive and executable identities are in `data/model_counting/references.json`. D4 is a historical competitor; beating this binary does not establish a win over the 2026 D4 entry. Ganak was obtained as an unchanged upstream release binary, not rebuilt with weakened options. Reference implementations are independent of our counter.

The raw corpus is approximately 1.29 GB. Its full manifest and exact retrieval script are included; the large corpus and upstream reference archives are downloaded separately rather than vendored into this repository. Three small original public fixtures are bundled. Every instance in the final scope is evaluated, including oversized and failing cases.

## Measurement contract

The primary local experiment grants each solver 10 seconds of subprocess wall-clock time and a common 6 GiB virtual-address-space limit. Parsing, process startup, normalization, native formula construction and solving are all inside that time. Native library compilation is warmed once and separately recorded. Solvers execute serially, with their order rotated between instances. The separately delivered detailed-evidence archive contains stdout/stderr logs that retain all solver results, progress, counts and failures, with local execution path prefixes replaced by placeholders and Ganak's upstream build-environment line omitted. Original output was retained locally before preparing that archive; `log_publication.json` binds original and published log hashes and lists affected files. Timings, peak RSS, outcomes and exact counts are unchanged by these redactions. `scripts/check_model_counting_receipts.py` audits the full original scope, frozen sources, competing binary identities, exact counts against raw logs, original fixture bytes, unfiltered repeat eligibility, all three trials, memory logs and reported medians. An external timeout kills the process group; a timeout, error, unsupported input and exact zero are distinct results.

This is a declared latency target on competition data, not the official hour-long/32 GiB competition score or the 2026 120-second track. Historical published rankings cannot be compared numerically with these local solve counts. A 10-second failure does not imply failure at a longer time limit. Likewise, a local timing advantage does not establish a new official record.

Development timings were excluded from the final receipts: a public-only exploratory run, an initial 4 GiB pilot that caused early D4 allocation failures, and a restart that briefly overlapped the pilot were discarded. The final 6 GiB run starts at the UTC timestamp recorded in its ledger and is the sole primary measurement reported. Output ownership is guarded by an exclusive lock; source hashes must remain unchanged.

The full benchmark manifest is written before the first result. Source hashes are checked during the run. Counts returned by multiple exact solvers must agree; a disagreement aborts the run for investigation. A result produced by only one solver is explicitly unconfirmed, not automatically an independently verified breakthrough. Repeated comparisons of every independently confirmed PerfectPower exact case are separate from the first latency screen. References are rerun even when they timed out in the screen. They include an additional control using the same Ganak binary with its documented probabilistic default mode (`--prob 1`), alongside the deterministic mode. Peak resident memory is recorded with GNU time; its small wrapper overhead is included equally in the repeated timings. The repeated subset contains every independently confirmed case our counter solves, including losses, and must not be treated as a whole-corpus speed average.

## Results

The completed machine-readable ledger and repeated comparisons supply the results below. Exact counts and per-case failures remain available in `receipts/model_counting`; do not infer a broad win from the three bundled fixtures.

The full latency screen completed all **200 original instances**. All **11** native exact results were independently matched; there were **zero exact-count disagreements**. No independently unconfirmed native result is presented as a win.

| Method | Exact / 200 | Timeout | Work limit | Public exact / 100 | Historical evaluation exact / 100 |
|---|---:|---:|---:|---:|---:|
| PerfectPower 0.10.0 | 11 | 182 | 7 | 5 | 6 |
| Ganak 2.8.0, deterministic | 34 | 166 | 0 | 16 | 18 |
| D4 regular2, archived 2024 | 37 | 163 | 0 | 20 | 17 |

This is a coverage loss overall: the native counter solves 5.5% of this corpus under the declared latency contract, versus 17% for deterministic Ganak and 18.5% for archived D4. The seven native work limits are two byte-limit cases and five dimension-limit cases; all remain in the denominator. The reference runs have no subprocess errors or unparsed successful outputs.

All 11 independently confirmed native cases were repeated three times against both reference binaries and Ganak's probabilistic default mode. The following medians include the equal GNU time wrapper. A missing median means at least one trial did not return an exact count before the cutoff, not a zero runtime.

| Instance | Original split | PerfectPower seconds | Ganak deterministic seconds | Ganak default-mode seconds | Archived D4 seconds |
|---|---|---:|---:|---:|---:|
| 028 | public | 1.350 | 3.484 | 3.085 | 6.863 |
| 030 | public | 2.533 | 4.965 | 4.371 | TIMEOUT |
| 057 | holdout | 6.644 | 0.418 | 0.424 | 0.055 |
| 079 | holdout | 0.059 | 0.031 | 0.033 | 0.019 |
| 080 | public | 0.062 | 0.018 | 0.020 | 0.016 |
| 081 | holdout | 0.057 | 0.021 | 0.022 | 0.019 |
| 082 | public | 0.062 | 0.031 | 0.028 | 0.019 |
| 083 | holdout | 0.057 | 0.029 | 0.026 | 0.019 |
| 087 | holdout | 0.113 | 0.247 | 0.245 | 0.039 |
| 118 | public | 0.066 | 0.279 | 0.255 | 0.325 |
| 183 | holdout | 0.804 | 1.196 | 1.174 | 0.470 |

Repeated median peak resident memory, in MiB (virtual-address-space cap remains 6 GiB):

| Instance | PerfectPower MiB | Ganak deterministic MiB | Ganak default-mode MiB | Archived D4 MiB |
|---|---:|---:|---:|---:|
| 028 | 24.5 | 173.7 | 121.6 | 131.5 |
| 030 | 26.6 | 289.7 | 204.1 | No complete exact-trial median |
| 057 | 28.4 | 44.3 | 44.3 | 30.4 |
| 079 | 15.9 | 8.1 | 8.1 | 26.5 |
| 080 | 15.6 | 7.8 | 7.8 | 26.2 |
| 081 | 15.6 | 7.8 | 7.8 | 26.3 |
| 082 | 15.9 | 8.0 | 8.0 | 26.4 |
| 083 | 15.8 | 8.0 | 8.0 | 26.4 |
| 087 | 16.2 | 13.5 | 13.5 | 26.5 |
| 118 | 16.7 | 21.7 | 18.6 | 31.2 |
| 183 | 24.8 | 17.7 | 15.6 | 32.2 |

The three bundled public development fixtures preserve clear local gains. On 028, the native median is 1.350 seconds, 2.29× faster than Ganak's default mode and 5.08× faster than archived D4; median peak RSS is 24.5 MiB versus 121.6 and 131.5 MiB. On 030, it is 1.73× faster than Ganak's default mode, while D4 times out in all three 10-second trials. On 118, the native median is 0.066 seconds versus 0.255 and 0.325 seconds, although the small absolute times limit the commercial significance of that gain. These fixtures were used in development, so these are reproducible local engineering results rather than fresh independent validation.

Two historical evaluation cases, 087 and 183, are respectively 2.17× and 1.46× faster than Ganak's default mode in the repeated study, but archived D4 is faster on both. No historical evaluation case shows a native win over both references. The losses are material: on 057 the native median is 6.644 seconds versus 0.424 for Ganak's default mode and 0.055 for D4, roughly 16× and 121× slower. The five small affine cases 079–083 also lose on subprocess latency and use more resident memory than Ganak.

The measured conclusion is a functioning exact CNF backend with repeatable gains on a narrow subset of a recognizable benchmark, alongside substantially worse whole-corpus coverage. This is useful evidence for targeted follow-up; it is not a general state-of-the-art result, an official competition win, or a guarantee of investment. The entire selected subset, including these losses, is reported above.

The completed receipt audit verified 200 original instance identities, every native exact case's repeat eligibility, 732 result logs and 132 associated GNU time records. All 864 delivered logs have publication hashes; no exact count disagreement or missing repeat was found.

## What would justify the next investment

A credible next claim needs a gain against current reference defaults on fresh instances that were not used to choose algorithms, together with equal-resource replications and independently matched exact counts. Fewer solved cases overall cannot be converted into a general superiority claim by highlighting two fast fixtures. If a repeatable niche remains, the next experiment should predeclare that problem family, evaluate the entire family, and connect counting or conditional sampling to a concrete application. If the default-mode control erases the apparent gains, the honest outcome is a usable new backend and a clear performance gap to close.

## Correctness and practical limits

The combined focused regression runs cover 138 test methods, with 136 passing and two optional Mathlib-dependent checks skipped. The new counter and harness account for nine of these methods; all nine were rerun successfully after receipt completion. New coverage includes 240 random small formulas compared with exhaustive enumeration, 100 planted nontrivial satisfiable formulas, conditional counts, first/middle/last ranks, fresh-counter inverse checks, large counts beyond JavaScript or machine-integer precision, parity systems, disconnected components, empty populations, missing variables, strict parsing and closed-counter errors. The real fixture 118 has count 17,528,422,464, matching Ganak and D4, and supports a seeded sample plus a fresh-counter round trip.

An additional 1,000 native formulas matched exhaustive counts in an AddressSanitizer/UndefinedBehaviorSanitizer run. `make model-count-sanitizer` reproduces the native fuzz check. In this environment `ASAN_OPTIONS=detect_leaks=0` was required: LeakSanitizer was disabled because its process inspection is unavailable in this execution environment; no leak-check result is claimed. The benchmark harness also tests exclusive output ownership, exact-versus-approximate output recognition, explicit work limits, errors and subprocess timeout termination. Native memory checks and exhaustive integer comparisons are executable evidence, not kernel proofs of all inputs.

The component-cache byte limit is an estimate for retained keys and integers, not a hard bound on total process memory. The benchmark applies a separate process memory cap. Recursive searches can still grow exponentially. Table elimination depends on width; parity recognition helps only complete affine structures. Original-variable ranking and sampling can require many conditional counts and have a cooperative whole-query deadline. Strict wall-time enforcement requires the subprocess wrapper. They are not guaranteed fast on arbitrary competition instances.

## Reproduction

```sh
python scripts/fetch_model_counting.py /tmp/mc2024
python scripts/fetch_model_counting_references.py /tmp/mc-references
PYTHONPATH=python python python/run_model_counting.py \
  --corpus /tmp/mc2024 --ganak /tmp/mc-references/ganak \
  --d4 /tmp/mc-references/d4 --timeout 10 --memory-gib 6
PYTHONPATH=python python python/repeat_model_counting.py \
  --screen receipts/model_counting/benchmark.json --corpus /tmp/mc2024 \
  --ganak /tmp/mc-references/ganak --d4 /tmp/mc-references/d4 \
  --repeats 3 --profile-memory
make model-count-test
python scripts/check_model_counting_receipts.py
```

GNU time is required for the optional repeated peak-RSS measurements (the standard `time` package on Debian/Ubuntu). `--time-binary PATH` selects a nonstandard installation. Reference downloads target Linux amd64. Other platforms require suitable upstream builds and a separately declared comparison. `--split public` and `--split holdout` preserve the historical partitions. `--limit` is useful for smoke tests but changes the benchmark scope and must not be reported as the full dataset. Full source releases include the source, manifest, downloader, fixtures, tests, measurement summaries and this monograph. Detailed solver stdout/stderr and GNU time logs are supplied in a separate evidence archive; extract its contents at the checkout root or pass the extracted root to `check_model_counting_receipts.py --log-root PATH`. The public repository carries their content hashes and per-case counts/outcomes/measurements, without executed command lines, local platform strings or CPU identification. Extensive execution output remains in the separate evidence archive.
