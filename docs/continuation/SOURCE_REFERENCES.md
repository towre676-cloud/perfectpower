# Source references and verification scope

The primary technical sources used for this continuation are the current
repository and the pinned Mathlib source installed locally. No new primary-paper
literature comparison is represented as completed by this handoff.

- [Project source base](https://github.com/towre676-cloud/perfectpower/tree/ddad6befc1f16219e4860bd90273a99a25e37bd6)
- [Lean 4.20.0 release](https://github.com/leanprover/lean4/releases/tag/v4.20.0)
- [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/tree/c211948581bde9846a99e32d97a03f0d5307c31e)
- [Polynomial normalized factorization](https://github.com/leanprover-community/mathlib4/blob/c211948581bde9846a99e32d97a03f0d5307c31e/Mathlib/RingTheory/Polynomial/UniqueFactorization.lean)
- [Squarefree factor lemmas](https://github.com/leanprover-community/mathlib4/blob/c211948581bde9846a99e32d97a03f0d5307c31e/Mathlib/Algebra/Squarefree/Basic.lean)
- [Batteries lint command implementation](https://github.com/leanprover-community/batteries/blob/7a0d63fbf8fd350e891868a06d9927efa545ac1e/Batteries/Tactic/Lint/Frontend.lean)

The final machine-readable receipt is `verification/results.json`. Its hashes
identify the exact new Lean sources checked in this session. The logs record
actual command exit codes. The baseline Python suite and certificate audit were
rerun here; this does not replace a fresh full baseline `make verify`, including
all generated Lean certificates and receipt regeneration.

The ordinary axioms accepted by the new proof audit are `propext`,
`Classical.choice`, and `Quot.sound`. No named geometric finiteness premise is
used by the new decomposition or pointwise reductions. Existing repository
claims that depend on such premises retain their original trust status.
