# Current continuation — 6 October 2026

The active branch is `claude/laughing-lamport-qqzdo9`; this continuation starts from `a5d0f04aa6c8f666dfd9428747abbbdf3811fe50`. Read `docs/NONFLAVOR_FRONTIER_MONOGRAPH.md` and `receipts/nonflavor_frontier/summary.json` before the historical handoff below. Use `make nonflavor-frontier-lean` for the seven new Lean modules and generated factorial witness; use `make nonflavor-frontier-receipts` for source-bound executable reproduction. Flavor is reserved for a separate session. Preserve concurrent remote changes when publishing. The old whole-repository census counts are not the focused audit counts.

# Continuation handoff — 2026-09-29

## Start with the source, not earlier status numbers

Base branch: `claude/laughing-lamport-qqzdo9`.
Base commit: `ddad6befc1f16219e4860bd90273a99a25e37bd6`.
Lean: `leanprover/lean4:v4.20.0`.
Mathlib resolved commit: `c211948581bde9846a99e32d97a03f0d5307c31e`.

This ZIP is a fresh continuation against that base. It does **not** reconstruct
the unavailable previous handoff or include its claimed 31-declaration overlay.
It includes a source snapshot, the new overlay, actual replay logs, and a patch
containing only new files. No changes were pushed to GitHub.

Upstream has already proved the −13 Mordell case unconditionally. Do not start
a class-group reconstruction for it: read `MordellMinus13.lean` first.

## Apply to an existing checkout

1. Make an isolated branch/worktree. Compare its HEAD with the pinned base.
2. Apply `continuation.patch` with `git apply --check` followed by `git apply`.
   The patch adds files; it does not overwrite the root README or audit counts.
3. Install the pinned toolchain if necessary, run `lake update`/cache retrieval,
   then `python3 continuation_tools/verify.py` from the repository root.
4. Read `docs/continuation/MATHEMATICAL_CHAPTER.md`, then the new Lean modules.
5. Integrate imports and baseline auditing only after the targeted replay passes.
   Run full `make verify` before updating release claims or pushing.

The ZIP's `repository/` is also a complete tracked-source snapshot with the new
files included. It contains no `.git`, `.lake`, compiled cache, or toolchain.
It is useful for inspection and fresh replay; use your own Git checkout for
receipt regeneration and release verification because `make verify` invokes Git.

## Implemented, rather than merely proposed

- Universal monic squarefree-layer decomposition over Q[X], including constants.
- Existence after mapping any nonzero Z[X] polynomial into Q[X].
- Exact full-power extraction and weighted degree accounting.
- The comaximality counterexample over Z[X] and its rational Bezout counterpart.
- Radical shape from exactly one residual root, without assuming a rational root.
- Integer radical reduction with denominator clearing and all zero values retained.
- Generic quadratic/Pell shape and the full rational coefficient-branch reduction.
- Opposite-square branch overlap only at zero.
- Independent exact Fraction-based Yun algorithm, exact integer roots, and tests.
- Strict audit replay: real exit codes, exact audit-entry coverage, standard-axiom
  whitelist, and rejection of an empty lint run.

The definitions live in `PerfectPower.RationalYun`; module paths begin
`PerfectPower.Continuation`. This distinction matters to Batteries' module
filter. Lint with `#lint in PerfectPower.Continuation`, not the namespace.

## Next move 1: integrate the rational interface

Read `PerfectPower/Atlas.lean` before changing it. Its existing decomposition
interface uses `IsCoprime` over Z[X] and lacks universal existence. Do not prove
an impossible universal existence theorem for that structure. Move the generic
atlas to the rational interface or retain the old structure as a restricted
legacy interface with explicit adapters.

Acceptance: generic input accepts X(X+2)^2, constants work, zero is handled
separately, existing concrete results still compile, and no new axiom appears.
Update root imports, the main axiom audit and generated count logic together.
Do not mechanically change 169 to 200: use the repository's own generator and
explain whether definitions and theorems are counted differently.

## Next move 2: finish Theorem B as a count

The formerly missing general pointwise step is now
`Decomposition.integer_radical_reduction`. Connect it to
`RadicalValuation.lean`, `RadicalCount.lean`, and `RadicalAsymp.lean`.

- Prove the exceptional zero set is finite and its count changes by at most a
  fixed constant. Establish quotient-part monicity/nonvanishing if useful.
- Separate positive/negative z=vn−u using the existing signed hit predicate.
- Carry the affine congruence z≡−u (mod v) through z=z0 w^t.
- State the exact arithmetic solvability criterion; an empty residue set means
  a finite branch, not a positive power-growth constant.
- Prove the real-power conversion and derive the positive leading constant
  when the admissible residue set is nonempty.

Acceptance: an arbitrary polynomial with badDegree=1 reduces and counts with
all exceptional zeros and signs included. Test examples with a rational linear
root and a full-power factor vanishing at an integer.

## Next move 3: finish Theorem C as an orbit theorem

Use `Decomposition.integer_pell_reduction` as the pointwise entry point.

- Prove finiteness/cardinality of rational γ satisfying γ^e=c. Keep both signs
  when e is even; if no root exists, only zeros survive.
- Clear coefficients by a square L²; do not introduce a spurious congruence
  restriction on the rational square root.
- Convert the integral quadratic to its norm equation with all image congruences.
- Derive quadratic squarefreeness/nonzero discriminant from pairwise-coprime
  squarefree layers; monic degree two by itself is insufficient.
- Handle sign and split/square-discriminant cases before invoking a fundamental
  unit. Prove orbit population before asserting a positive logarithmic constant.
- Attach `PellGeneral.lean` / `PellExact.lean` counts and control finite overlap.

Acceptance: a general Pell-type F has a finite union of correctly constrained
branches and an exact bounded-discrepancy count. No finite branch is mislabeled
as logarithmically populated.

## Next move 4: root-profile transport and geometric finiteness

The new badDegree is an intrinsic rational-layer degree sum. Formalize its
agreement with the algebraic-root multiplicity list used by `ProfileG.lean`.
Transport the existing combinatorial theorem through that bridge. State the
rational finite-type geometric input explicitly; preserve the named-premise
trust label until normalization, fields of definition and Siegel are supplied.
Do not infer the genus theorem from the new decomposition alone.

## Next move 5: completeness and quartics

The new −13 proof supplies a proven nonempty genus-one model. Generalizing its
finite norm-table certificate may be more tractable than a broad elliptic-log
formalization. Compare the exact scope against Baanen et al. before announcing.
For quartics, define the rational change of model together with its inverse and
its integrality/image conditions first; a list of integral points on the cubic
image is not automatically complete for the original quartic.

## Release discipline and research positioning

The new overlay is opt-in and the original root import/audit/count setup is
unchanged. Targeted verification here is not a fresh full `make verify` pass.
Logs include existing nonfatal ResourceWarnings in the old tests. Those can be
fixed independently by context-managing file reads.

The stale blanket claim in OPEN_PROBLEMS about D=±3 deserves an independent
congruence review; do not reuse it as a theorem. Likewise never infer the
original density from a finite maximum of prefix densities. For exponent
experiments use log(1+A(N))/log N, state the scale and bounds, and keep numerical
evidence separate from complete certificates.

The public-facing value is a reproducible chain from generic input through
structural reduction to exact counts and checkable completeness, with honest
trust labels. Avoid novelty claims for Yun's algorithm, Runge enumeration,
Siegel's theorem, or classical radical/Pell reductions. A precise formal API
and a complete certificate pipeline are defensible contributions to develop.

Connected closures continuation: run `make connected-closures-lean` for the general determinant and integral uniqueness proofs plus generated population fixtures; run `make connected-closures-receipts` for bounded population output and marked Legendre loops. Existing flavor commits are preserved. Bounded numeric image ranks differ from canonical-owner projection ranks. Period replay recomputes the same analytic producer and is not an independent Lean proof. Current evidence is under `receipts/connected_closures`.
