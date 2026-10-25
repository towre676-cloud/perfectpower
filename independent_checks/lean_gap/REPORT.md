# PerfectPower Lean gap — report

Task: inventory the two named open formal items (squareclass quotient
identification; unconditional Mordell–Weil rank), check the toolchain,
and attempt closure of the smallest genuinely closable piece.
Full inventory: `INVENTORY.md` in this directory. No existing
repository file is changed by this work; these files are committed on
the branch `muse/lean-squareclass-uniqueness`, as new files under
`independent_checks/lean_gap/`, for review by pull request against the
repository's default branch.

## What is genuinely open (summary of the inventory)

There is **no `sorry`, no tactic `admit`, and no custom `axiom`
anywhere in the 1,175-file Lean tree** (exact greps in §"Verification
commands" below). The permitted axiom set in the project's own audit
gates is exactly `propext`, `Classical.choice`, `Quot.sound`. Both
named items are therefore *missing mathematics*, in two different
shapes:

- **Squareclass quotient identification is missing theorems, not
  hidden assumptions.** The descent homomorphisms δ : E′(ℚ) → ℚ*/ℚ*²
  and δ′ : E(ℚ) → ℚ*/ℚ*² do not exist as Lean definitions; neither do
  `ker δ = range ψ`, `ker δ′ = range φ`, the finite image bounds, or
  the divisor-four kernel-cardinality step. The precise requirement
  list is `docs/ISOGENY_POINT_GROUPS_MONOGRAPH.md:107`. No existing
  theorem carries these as hypotheses — they are simply absent.
- **Unconditional Mordell–Weil rank is blocked by explicit
  hypotheses.** (i) The decomposition premise
  `(e : Point ≃+ F × T)` of `DescentRankBridge.elliptic_descent_rank`
  (line 64) — a Mordell–Weil decomposition of the actual point group,
  never constructed for any retained curve. (ii) In
  `MordellCompletionBridge.lean`, the hypotheses `PrimeSupport H S`
  (global saturation prime support), `PrimeSaturated H p` (via the
  uninstantiated reduction-separation premise `hsep`), and `hbound`
  (global integral coordinate bound) — matching
  `contracts/current_frontier.json` finding id 2, status `open`:
  curve-specific rank upper bounds, saturation at other primes and
  global integral coordinate bounds remain open, and zero of the 457
  external completion packets have been promoted to unconditional
  Lean theorems (`docs/MORDELL_FORMAL_BRIDGE_MONOGRAPH.md:3`).

## Toolchain

No Lean toolchain was present initially (`which lake lean elan`
empty, no `~/.elan`). It was installed from the project's own pin:
elan with default toolchain `leanprover/lean4:v4.20.0` (matching
`lean-toolchain`), giving `Lean (version 4.20.0, commit 77cfc4d1a4f6)`.
File-level verification was established first at core level: a
standalone file compiled and kernel-checked in ~2 s with
`#print axioms` reporting only `[propext, Quot.sound]` (log:
`build_core_test.log`). Bare core has no `ring` tactic — that is a
Mathlib/Std tactic, which is why the real attempt below is built
against the pinned Mathlib v4.20.0 in the scratch project
`project/` in this directory (its only content is a lakefile
requiring Mathlib at the repo's pin; the PerfectPower repo itself
was not used as a build tree).

## What was attempted and closed

**Target chosen.** The smallest piece of item (1) that is both
genuinely part of the identification and closable in isolation: the
*uniqueness of squareclass representatives*. PerfectPower proves
existence — `TwoDescentBridges.rational_point_cover_complete`: every
nonzero rational point x-coordinate is `d·u²/v²` with `d` squarefree
and `d ∣ b` — but nowhere states that `d` is unique. Without
uniqueness, the label "the squareclass of x" is meaningless, δ
cannot be defined by representatives, and the "surviving
squareclasses" language of the generated cover theorems has no
well-defined target. The file `SquareclassUniqueness.lean` proves:

- `Int.eq_of_squarefree_of_isSquare_ratCast_div`: nonzero squarefree
  integers `d₁, d₂` with `d₁/d₂` a square in ℚ satisfy `d₁ = d₂`.
  Proof: `d₁·d₂` is then a square in ℚ, hence in ℤ
  (`Rat.isSquare_intCast_iff`); comparing prime factorizations of
  `|d₁|, |d₂|` (each exponent ≤ 1 by squarefreeness, their sum even
  because the product is a square) gives `|d₁| = |d₂|`, and
  `d₁·d₂ > 0` fixes the signs.
- `squareclass_label_unique`: the same statement in the descent's
  form — if `x = d₁·w₁² = d₂·w₂²` (x, w₁, w₂ nonzero rationals, dᵢ
  squarefree integers) then `d₁ = d₂`.

**Verification status: VERIFIED — compiled, not UNVERIFIED.** The
file was compiled with the project's pinned toolchain (Lean 4.20.0,
Mathlib v4.20.0, prebuilt cache) via `lake env lean`; exit code 0, no
errors or warnings, in 27 s warm / 74 s cold (`build.log`). The
`#print axioms` check appended for the verification run reports both
theorems depend only on `[propext, Classical.choice, Quot.sound]` —
exactly the standard axiom set the project's own gates permit, with
**no `sorryAx`**. The shipped file is the deliverable
`SquareclassUniqueness.lean` itself (the verification copy differed
only by the two appended `#print axioms` lines). File-level
verification of the repo's own code was also established: the
smallest relevant repo module chain, `PerfectPower.DescentRankBridge`
(built in a *copy* of the repo tree reusing the same Mathlib cache;
the original was never written to), builds successfully in 1m48s
(`build_repo_file.log`), and a trivial full-`import Mathlib` scratch
file builds in 6m06s (`build_scratch_project.log`). One environment
quirk worth recording: the first `lake exe cache get` failed because
the sandbox forbids the `tar` ownership change when installing the
`leantar` helper; rerunning with `TAR_OPTIONS=--no-same-owner`
fixed it and the full 6,772-file cache downloaded and unpacked
successfully.

## What remains open after this attempt

Everything else in the inventory: the definitions of δ and δ′ and
their homomorphism properties; `ker δ = range ψ` and its dual (this
is the substantial arithmetic step — it needs the homogeneous-space
solubility analysis, not just representative bookkeeping); the
finite image bounds assembled as statements about δ (the arithmetic
input `d ∣ b` is already proved); the divisor-four cardinality
computation; the Mordell–Weil decomposition construction; and the
three Mordell-completion inputs (prime support, saturation
instantiation, global coordinate bounds) for the 457-curve frontier.
The piece closed here is necessary infrastructure for the first of
those, and is not, by itself, progress on rank.

## Verification commands

Inventory greps (run in `~/workspace/research/perfectpower`):
`grep -rn --include="*.lean" -w "sorry" PerfectPower/ PerfectPower.lean`
(0 hits); `-w "admit"` (4 hits, all English in comments);
`grep -rn --include="*.lean" "^\s*axiom "` (0 hits);
file counts `find . -name "*.lean" -not -path "./.git/*"` (1,175).
Build: see `build.log` in this directory.
