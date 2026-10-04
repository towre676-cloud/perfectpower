# Divisor and arithmetic reuse verification

Verified on 4 October 2026 against predecessor commit `7bb25c7b27414cea7d063a23fcbac676bb48e934`, Lean 4.20.0, and Mathlib `c211948581bde9846a99e32d97a03f0d5307c31e`.

`bash scripts/check_divisor_reuse.sh` passes. It compiles all four new foundational modules and the updated native polynomial tactic; checks the prior near-square and finite-field audit; checks nine complete polynomial lists, including both million-sized coefficient signs and repeated roots; rejects constants, trailing zeros, the infinite k=0 family, and a false point list; and checks the primitive quartic obstruction and a false obstruction. Printed axioms are confined to `propext`, `Classical.choice`, and `Quot.sound`. The new square-root equivalence and modular equation transport need only `propext` and `Quot.sound`.

Python-emitted native commands for `[1000000,1], k=1` and the quartic obstruction at 3 also compile and pass axiom audits. This checks the public emitter path separately from the handwritten audit.

The repository's four Python unittest suites pass: 345 tests in `python/tests` (four skips), 14 in `continuation_tests`, 10 in `expert_push/tests`, and 8 in `galois_merge/tests`. There are 377 tests in total, of which 373 execute and four are skipped because the regular Python test invocation lacks Lake on PATH or Why3. Z3 5.1.0.0 was installed before the passing run. The new focused suite has nine tests, including 150 independent scan comparisons and exact algebra identities in degrees two through six. It is included in the 345 count. Existing unclosed-file resource warnings do not affect the results.

The deterministic operation receipt regenerates identically. The million-shift example compares 6,000,021 prior rectangle candidates with 1,001 Python trial-divisor checks. These are operation counts, not a measured wall-clock speedup. `git diff --check` and Python compilation checks pass.

Raw logs and source hashes are retained under `receipts/divisor_reuse_*`. Earlier native receipts remain historical records of their source revisions; this record covers the updated source.

The polynomial audit uses a 64 MiB Lean worker stack and a local recursion limit for kernel reduction. The structurally recursive square-root implementation avoids the expensive well-founded reduction discovered in the original attempt. This environment additionally needed a small runtime executable-path lookup compatibility shim for Lean; it changes neither inference rules nor arithmetic evaluation. It is not a repository dependency.

The full heavy Lean repository build, full receipt regeneration pipeline, optional Sage crosschecks, Why3 session replay, and historical bounded-Pell kernel tests were not rerun. This record makes no claim about those checks. General arbitrary-polynomial power solving, complete number-ring solvers, and general Baker/Runge automation remain unfinished.
