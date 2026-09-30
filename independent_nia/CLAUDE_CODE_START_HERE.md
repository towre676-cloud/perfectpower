# Claude Code work order

## Goal

Continue PerfectPower's evidence-backed integration with nonlinear integer verification. Establish where a checked arithmetic certificate can remove expensive repeated search, with sound semantics and a measured baseline. The included corpus is obtained independently of PerfectPower and does not depend on access to Zenodo.

## Begin with the evidence

Run `python3 tools/verify_manifest.py`, `python3 tools/selfcheck.py`, and `python3 tools/inspect_corpus.py` in this directory. Inspect `reports/summary.json` and the per-file inventory. Record the SHA of the actual PerfectPower checkout. The earlier reviewed commit is `631b08d6f187438f0e5cc0707ceb9b7a050f4f16`; the artifact includes workloads and tools, not the repository itself.

If there is no project checkout, clone `https://github.com/towre676-cloud/perfectpower.git` into a separate directory and inspect it. If it already exists, use it without discarding edits. Read its AGENTS.md and existing tests before making a separate working branch/worktree. Use a newer revision if instructed; do not silently treat this reviewed anchor as the latest version.

The first triage found 19 industrial files with no direct univariate square/cube matches. Four files contain syntactically symbolic products, but that fact does not establish applicable PerfectPower structure. Inspect those four files and their live query contexts before proposing a normalized recognizer. A result of zero eligible industrial replacements must remain visible in the report.

The three cvc5 candidate files are `pow2-monotone-neg-soundness.smt2`, `proj-issue-425.smt2`, and `disj-eval.smt2`. The second deliberately expects option-parsing failure. The first uses an integer exponentiation extension. The third asserts `x*x=y*y*y` with finite disjunctive value sets. Its equation appears twice in the inventory because it has two square/cube orientations. Do not count those as four independently hard problems or as Mordell-certificate matches.

## Baseline before optimization

Install a standard Z3 or cvc5 binary if the machine permits it, record its version and invocation, and run the raw corpus with `tools/run_baseline.py`. Preserve timeout, unknown, unsupported syntax, and nonzero exit outcomes separately. Do not execute `COMMAND-LINE`, `SCRUBBER`, or other harness directives automatically; inspect them and reproduce selected harness runs explicitly where relevant. The package already preserves all such directives.

Use `--incremental` for cvc5 on ELSTER. The raw ELSTER files contain many check queries; a 2-second timeout for a whole file may yield only a partial stream. Keep file-level startup time separate from per-query measurements. The current runner reports file times; add an interactive query runner if query-level timing is needed. Never divide a file time by its query count and call that the cost of a particular obligation.

## Adapter implementation

Start with a fail-closed interface on supported positive asserted polynomial equalities. The project entry point is `python/perfectpower/compiler.py`, especially `PowerConstraint`, `compile_constraint`, `Plan.explain`, `Plan.status`, `supports`, `justification`, and `execution_verified`. Read their current definitions rather than assuming a stable API. Map a polynomial to coefficients in ascending degree. Preserve the exact source atom, symbols, sort declarations, assumptions, live query state, and normalized polynomial as the certificate's input binding.

Only enable replacement when all conditions are met: correct Int semantics; supported fragment; theorem domain established; checked normalization; a complete relevant theorem or checked certificate; correct witness/sign transport; and verified linkage back to the original query. If any condition is absent, return an explicit unsupported/not-checked record and retain the original obligation for the solver.

`COMPLETE_FINITE` is a completeness claim of a plan, not by itself a certificate that this SMT formula was checked. `CLASSIFIED_FINITE` and `NOT_ENUMERATED` never imply an empty solution set. `STRUCTURED_FILTERED` does not assert an infinite surviving set. `execution_verified` remains a separate field. Source status strings, theorem names, Python enumeration, and successfully typechecked Lean terms are different evidence levels.

The compiler's input convention `n>=1` needs special attention. Establish that guard, or split an arbitrary Int input into `n>0`, `n=0`, and `n<0`, with a checked coefficient-sign transport in the last branch. Track assumptions through push/pop. Do not apply positive-domain theorems directly to unrestricted variables. Preserve both signs of even-power witnesses. Do not descend into arbitrary disjunctions, negation, ite, or let without checked Boolean/normalization rules.

For an actual Lean-checked replacement, produce a theorem about the source mathematical statement plus a separately justified translation. Lean checking is not automatically a proof accepted by SMT, Why3, GNATprove, or AdaCore. Identify the consumer checker and trust boundary explicitly. A first deliverable can be a Lean-checked audit output alongside unchanged solver obligations; label it accordingly.

## Verification and evaluation

Add meaningful tests for malformed certificates, wrong input binding, changed coefficients, missing positivity, negative and zero inputs, even-power sign loss, unsupported div/mod and extension semantics, and live incremental assumptions. Test soundness at the replacement boundary, not only recognition of a pretty formula. Run the repository's required Python and Lean checks for the touched modules. If a checker is unavailable, report which results remain unchecked.

Report a per-query ledger with source identity, eligible fragment, domain proof status, plan status, certificate/checker status, baseline outcome, certificate generation time, checking time, residual solver time, and final result. Aggregate genuine checked replacements separately from unsupported inputs and unchecked candidates. Use held-out families or customer projects; splitting siblings from one generated form randomly is not independent validation.

The deliverable is a reviewable patch in the PerfectPower checkout, its validation results, baseline JSON, and a short coverage-and-economics report. If this independent sample provides no useful acceleration, explain why and identify the smallest real verification workload that would test the next supported fragment. Do not build a performance narrative from solver error tests or synthetic Mordell cases.

## Further acquisition

The 181-file ELSTER directory is indexed in `provenance/elster_full_index.json`; only 19 files are bundled. Run `python3 tools/fetch_remaining_elster.py` on a network-enabled machine for the remaining 162 files. This may exceed GitHub's unauthenticated rate limit and will increase uncompressed storage. Keep the expanded corpus separate and generate a new provenance manifest and cohort label before evaluation. Never claim that this retrieves the blocked Zenodo archive.

## Success criterion

A successful result either demonstrates a reproducible, semantically justified, checked replacement with a measured benefit on a real obligation, or provides a reproducible zero-coverage diagnosis and a precise acquisition/extension target. Commercial language follows measured utility. No change to the public repository is requested by this work order.
