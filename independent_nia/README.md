# PerfectPower: independent QF_NIA handoff

This handoff removes the Zenodo download dependency. It contains 69 actual upstream SMT-LIB files, byte-exact provenance, a structural inventory, and runnable baseline tooling. It is a workload and integration handoff for an existing PerfectPower checkout; it does not contain a full copy of PerfectPower, Lean, Mathlib, Z3, or cvc5.

Read `CLAUDE_CODE_START_HERE.md` first. The deeper mathematical and commercial context is in `HANDOFF_MONOGRAPH.md`.

## Contents and initial evidence

| Cohort | Files | SMT check queries | What it establishes |
|---|---:|---:|---|
| SMT-LIB submission: industrial ELSTER | 19 | 12,801 | Authentic incremental tax-form test-generation queries, sampled from 181 files |
| cvc5 regressions explicitly declaring QF_NIA | 49 | 58 | Independent regression material, including extensions and intentional failure tests |
| STAUB motivating sample | 1 | 1 | A crafted sum-of-three-cubes problem originally from SMT-LIB |
| Total | 69 | 12,860 | Structural inspection completed; solver timings and Lean checking still pending |

The ELSTER sample picks the smallest file in each available `(type, query-variant, form)` stratum. It is a deterministic acquisition sample, not a statistically representative performance sample. All 292 SMT2 files in cvc5's three `regress[012]/nl` directories were inspected for the explicit QF_NIA declaration; all 49 matches are included. Neither cohort is presented as a downloaded official competition archive.

The conservative recognizer found zero direct univariate square/cube atoms in the industrial cohort. It found four orientations of three equations across three cvc5 files. One of those files is an intentional option-parsing failure test; another uses `int.pow2`. These are syntactic candidates, not certified substitutions or evidence of commercial speedups.

## Run locally

Python 3.10 or later is sufficient for verification, inspection, and the included safety checks. There are no Python package dependencies.

```bash
python3 tools/verify_manifest.py
python3 tools/selfcheck.py
python3 tools/inspect_corpus.py
```

On Windows, run `./RUN.ps1` in PowerShell, or use `py -3` in place of `python3`. The launcher verifies and inspects; run `py -3 tools/selfcheck.py` separately.

An installed solver is required for timings. The bundled report records **no solver baseline run**. Example commands, to run after installing the solver:

```bash
python3 tools/run_baseline.py --solver z3 --solver-arg=-smt2 --cohort cvc5 --output reports/z3_cvc5.json
python3 tools/run_baseline.py --solver cvc5 --solver-arg=--incremental --cohort elster --timeout 10 --output reports/cvc5_elster.json
python3 tools/run_baseline.py --solver cvc5 --cohort staub --output reports/cvc5_staub.json
```

The timeout applies to an entire file, including every incremental query. Original cvc5 harness flags are recorded but never executed automatically. Running raw files without those flags is a baseline on those formulas, not a reproduction of cvc5's regression harness. Intentional failure tests and extension-heavy cases require separate interpretation. Inspect `harness_directives` before comparing expected results.

`tools/fetch_remaining_elster.py` retrieves the 162 omitted industrial files from pinned Git blobs on a machine with GitHub network access. An optional `GITHUB_TOKEN` avoids low unauthenticated API rate limits. Expanded files stay outside the sealed corpus and are not added to its current manifest automatically. The original Zenodo archive was not downloaded.

## Provenance and integrity

`provenance/upstream.json` records source repository, pinned commit, upstream path, Git blob SHA1, exact byte length, and SHA256 for every file. Original line endings are preserved. `provenance/elster_full_index.json` records every file in the industrial source directory, and `provenance/cvc5_scan_index.json` records the complete scanned regression directory set. `provenance/acquisition.json` records selection and transport details.

`provenance/package_sha256.json` seals every included file except itself. Verification checks the sealed package and byte-exact corpus. Re-running inspection overwrites reports with deterministic content. New baseline reports can be added without altering upstream data; edits to sealed files intentionally fail package verification.

## Project anchor

The reviewed PerfectPower commit is `631b08d6f187438f0e5cc0707ceb9b7a050f4f16` in [towre676-cloud/perfectpower](https://github.com/towre676-cloud/perfectpower). Use the actual checkout's `AGENTS.md`, tests, and current interfaces. A newer project checkout may have additional features; record its SHA and reassess the gates before implementation. Do not overwrite local work to obtain the anchor.

## Attribution

ELSTER files credit Johannes Bauer and the mgm A12 Test Data Generator, generated June 18, 2026, for ELSTER test-data generation. They carry CC BY 4.0 metadata. The STAUB sample credits Fuqi Jia, Minghao Liu, Pei Huang, Feifei Ma, and Jian Zhang, generated February 28, 2022, and carries CC BY 4.0 metadata. cvc5 material retains its upstream modified BSD notice and authors listing under `licenses/`. See `licenses/ATTRIBUTION.md` for exact sources and the license for original handoff tools and prose.
