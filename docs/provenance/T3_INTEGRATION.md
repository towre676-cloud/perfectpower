# T3 integration and source provenance

Reviewed on 2026-11-04 and subsequently authorized by the repository owner.

## Exact sources

| Contribution | Original commit | Canonical buildable module |
|---|---|---|
| PR #9: delta homomorphisms and image bounds | `5315dcfe7107833c2b713e15bd85faa2eb8bd647` | `PerfectPower/DescentDelta.lean` and `PerfectPower/DescentDeltaLabel.lean` |
| PR #10: reverse kernel inclusions and exactness | `f23520a7ba3340bcb661fb71e02704c04dccb8e7` | `PerfectPower/DescentCover.lean` |
| PR #15: torsion-aware counting and replay receipts | `698713a8b992b9ff5950f75322865a82329150c3` | `PerfectPower/DescentCounting.lean` |

The three promoted PR #9/#10 source modules are byte-for-byte identical to
their original commits. Their mathematics was not rewritten during promotion.
The squareclass uniqueness dependency is promoted alongside them. The root
library imports counting and delta labels; counting transitively imports cover
and delta. Historical files under `independent_checks/lean_gap` are retained as
provenance and are not additional canonical module definitions.

PR #9's original commit is already an ancestor of main, via merge commit
`38152ab` (merge of `origin/muse/lean-descent-delta`). Its open status reflects
its older target branch and is not evidence that its commit is absent from main.
PR #10's commit is not an ancestor of PR #15; its source is promoted unchanged.
Its original report is preserved verbatim as `DESCENT_EXACTNESS_PR10.md` beside
this ledger. This historical report's statement that T3 is open is superseded by
`../DESCENT_T3_COUNTING.md`; its remaining arithmetic obligations are not closed.

## Independent replay

The pre-approval review downloaded the official Lean 4.20.0 compiler archive,
verified SHA-256 `f3b058430f87dd9569c7ebd269f0af1be7b010b754849b543ee6cf9ccc08d4f0`,
and used Mathlib `c211948581bde9846a99e32d97a03f0d5307c31e`.
Fresh compilation and all 51 audited declarations passed (18 delta, 16 cover,
17 counting), with only `propext`, `Classical.choice` and `Quot.sound` in the
transitive axiom lists. All 14 source SHA-256 values matched. Both regenerated
JSON receipts equaled their committed originals. Exact checks reproduced five
curves, 104 bounded point-composition occurrences, 372 finite-group
homomorphism pairs and 120 doubling factorizations. These tests do not certify
Mordell--Weil ranks.

Workspace maintenance removed the unpushed pre-approval checkout and local
commit `e48401a2daec6406d46fca76d9863443a00bfbe4`. The same approved workflow and
provenance changes were reconstructed from pinned repository sources. The
verification was rerun and fresh logs retained under
`../../receipts/descent_t3/review_20261104/`; original committed receipts are
preserved separately. The regenerated commit has a different identity. No
mathematical source change is part of this follow-up.

## Authorized integration sequence

1. Retain the five original PR #15 commits and all original PR branches.
2. Apply this workflow/provenance/evidence follow-up on top of the reviewed
   PR #15 head, guarded against concurrent head changes.
3. Merge PR #15 into main with a merge commit. Do not independently merge
   PRs #9 and #10 into the older target branch.
4. Verify canonical main's source hashes, imports, documentation and certificates,
   and inspect the main-triggered Actions run.
5. Close PR #9 as already incorporated and PR #10 as superseded by PR #15,
   recording original source commits and promoted paths. Retain both branches.

The owner explicitly authorized these steps, including merging despite unresolved
GitHub Actions startup failures. No repository settings change is included.

## CI evidence and limits

PR #15's T3 run `41095499064` concluded `startup_failure` with zero jobs.
Inspected Lean, Python and repository-integrity runs on the same head also
created zero jobs. Five inspected main runs (`40788327468`, `40788328518`,
`40788326123`, `40788324953`, `40788323558`) likewise failed at startup and
created zero jobs. These runs did not compile Lean or execute the arithmetic
checks. They provide neither a mathematical failure trace nor successful CI replay.

Available diagnostics expose no explanatory check run or administration/billing
diagnosis. The specific cause remains unestablished. Cross-workflow and main
evidence supports an execution problem broader than the new T3 workflow.

The follow-up enables push replay on main, declares manual dispatch, and includes
the toolchain, manifest and directly relevant isogeny dependencies in PR path
filters. This fixes a coverage gap; it is not claimed to repair startup failures.
The configured default branch remains `claude/laughing-lamport-qqzdo9`.
GitHub requires the workflow file on the default branch for manual dispatch;
the declaration alone does not promise an immediately available manual run button.
Main push replay does not require changing the default branch. Reference:
https://docs.github.com/en/actions/how-tos/manage-workflow-runs/manually-run-a-workflow

## Mathematical boundary

For nonsingular rational models the unconditional group-theoretic identity is

    |im(deltaPhi)| |im(deltaDual)| |E(Q)[2]| = 4 [E(Q):2E(Q)].

The proof retains the actual kernel/image intersection. The correction can be
one or two; its product with rational two-torsion is four. The classical
`4 * 2^r` image product remains conditional on an actual free-plus-finite
decomposition or an explicitly justified doubling-index interpretation.
Saturation/prime-support inputs, global height bounds, arbitrary-label Selmer
theory and unconditional arithmetic completeness remain separate obligations.
Lean's `Nat.card` and natural index use zero for infinite types/index; generic
statements must be read with that convention, not as assertions of finiteness.
