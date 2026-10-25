# Lean wave two — the descent maps δ and δ′ for PerfectPower's two-isogeny setup

**Status: complete and verified.** Two new Lean modules were built against a
copy of the repository (`repo_copy/`, the clone at
`~/workspace/research/perfectpower` was not modified) with the pinned
toolchain (Lean 4.20.0, Mathlib v4.20.0). Both modules compile with
`lake build`, contain no `sorry`, and the verification file
`VerifyDelta.lean` confirms via `#print axioms` that every main theorem
depends only on `[propext, Classical.choice, Quot.sound]`. This package is submitted on the branch `muse/lean-descent-delta`.

Deliverables in this directory:

- `DescentDelta.lean` — the main module (repo path if adopted:
  `PerfectPower/DescentDelta.lean`; imports `PerfectPower.TwoIsogenyDual`
  and `PerfectPower.TwoDescentBridges`).
- `DescentDeltaLabel.lean` — companion module on uniqueness of the
  squarefree label (imports `DescentDelta` and wave one's
  `PerfectPower.SquareclassUniqueness`).
- `VerifyDelta.lean` — `#print axioms` checks (not a library module).
- `build_final.log` — the final clean build log of all three files.
- `SquareclassUniqueness.lean` — wave one's file (submitted with the Lean inventory change), imported by the companion module; it is not duplicated in this change.

## The mathematics, pinned from the repo

For `a b : ℚ` with `b ≠ 0` and `a² − 4b ≠ 0` the repo works with
`E A B : y² = x(x² + A x + B)` (`TwoIsogenyPointMap.E`), the isogeny
`φ = phiHom a b : E(a, b) →+ D(a, b)` to `D a b = E(−2a, a² − 4b)` with
kernel `{O, T}`, `T = (0, 0)`, and the normalised dual
`ψ = dualHom a b : D(a, b) →+ E(a, b)` with `ψ ∘ φ = [2]`. The connecting
homomorphism of the φ-descent is, for a general model `E A B` whose
`(0, 0)` point is the kernel point,

  δ(O) = 1,   δ(x, y) = [x]  for x ≠ 0,   δ(0, 0) = [B],

with values in ℚˣ/ℚˣ², and the two maps of the descent are its two
instances: δ := the map on `D(a, b)` (parameters `(−2a, a² − 4b)`),
δ′ := the map on `E(a, b)` (parameters `(a, b)`).

**A naming discrepancy in the task text, flagged as instructed.** The
task paired the kernel identifications as "ker δ = range ψ,
ker δ′ = range φ". With δ defined as above (on the target of φ), the
inclusion that holds — and the only one supported by direct computation —
is the standard one: **δ ∘ φ = 1 and δ′ ∘ ψ = 1**, i.e.
`range φ ⊆ ker δ` and `range ψ ⊆ ker δ′`; the reverse inclusions still
open are correspondingly `ker δ ⊆ range φ` and `ker δ′ ⊆ range ψ`. The
boundary cases confirm the pairing is forced: at a point `P` with
`x(φ(P)) = 0` the value `δ(T′) = [a² − 4b]` must be trivial for δ ∘ φ = 1
to hold, and it is, because `x² + a x + b = 0` forces `a² − 4b = (a + 2x)²`;
dually at `x(ψ(P′)) = 0`, `δ′(T) = [b]` is trivial because
`b = ((x′ − a)/2)²`. No convention on δ makes `δ ∘ ψ` or `δ′ ∘ φ` even
typecheck (the domains do not compose), so this is a slip in the task
text, not a mathematical alternative.

## Defined (DescentDelta.lean)

- `squaresSubgroup : Subgroup ℚˣ`, the subgroup of squares
  (carrier `{u | IsSquare u}`, with a manual `Normal` instance —
  conjugation is the identity in the commutative group `ℚˣ`), and the
  target group `ℚˣ ⧸ squaresSubgroup`. Mathlib v4.20.0 has no bundled
  `Squareclass ℚ`, so the quotient is built directly.
- `cls (q : ℚ) : ℚˣ ⧸ squaresSubgroup`, the class of a rational
  (`cls 0 = 1` by convention; δ never uses the convention except through
  the exceptional value below). `cls` takes no proof argument, which
  makes rewriting with coordinate identities smooth. Basic API proved:
  `cls_of_ne`, `cls_zero`, `cls_one`, `cls_eq_one_of_isSquare`,
  `isSquare_of_cls_eq_one`, `cls_mul`, `cls_sq`, `cls_inv`
  (note `cls q⁻¹ = cls q`: the quotient is 2-torsion),
  `cls_eq_of_mul_square`, `cls_eq_of_mul_isSquare`,
  `cls_eq_of_int_rep`.
- `delta (A B : ℚ) (hB : B ≠ 0) : (E A B).Point → ℚˣ ⧸ squaresSubgroup`
  by pattern matching in the repo's style: `δ(O) = 1`; at `(x, y)` with
  `x = 0`, `δ = cls B`; else `δ = cls x`. Evaluation lemmas
  `delta_zero`, `delta_some_of_ne`, `delta_some_of_eq`.
- `deltaHom (A B : ℚ) (hB : B ≠ 0) : (E A B).Point →+ Additive (ℚˣ ⧸ squaresSubgroup)`
  (the additive view of the target is `Additive`, not `Multiplicative`:
  `Multiplicative` converts additive groups to multiplicative ones, the
  wrong direction here).
- `deltaPhi a b hb hd := deltaHom (−2a) (a² − 4b) hd` on `D(a, b)` and
  `deltaDual a b hb := deltaHom a b hb` on `E(a, b)`.

Because δ is defined by coordinates, no choice of representative is
involved and there is no well-definedness obligation at the definition
stage; the representative (squarefree label) description is recovered as
theorems below.

## Proved (all compiled, axioms exactly the standard three)

Homomorphism (priority 3 of the task):

- `delta_add (A B : ℚ) (hB : B ≠ 0) (P Q : (E A B).Point) :
  delta A B hB (P + Q) = delta A B hB P * delta A B hB Q`, by the same
  case analysis as the repo's `phi_add`: the point at infinity;
  translation by `(0, 0)` (`delta_add_zero_point`, via
  `TwoIsogenyPointMap.translate_coordinates`: the sum has x-coordinate
  `B / x = (B * x) * (x⁻¹)²`, so `[B / x] = [B] * [x]`); two `(0,0)`
  points; the vertical case `Q = −P` (`Point.add_of_Y_eq`); and the
  generic chord case (`delta_add_generic`, via `chord_roots`: the
  product `x₁x₂x₃` of the three collinear x-coordinates is the square of
  the line intercept, and when `x₃ = 0` the second chord identity gives
  `x₁x₂ = B`). Hence `deltaHom` is a genuine `→+`, and
  `delta_zero : delta A B hB 0 = 1` is `δ(O) = 1` (priority 3, first
  item).

The supported kernel inclusions (priority 4):

- `deltaPhi_comp_phi (a b : ℚ) (hb : b ≠ 0) (hd : a² − 4b ≠ 0)
  (P : (E a b).Point) : delta (−2a) (a²−4b) hd (phi a b hb hd P) = 1`,
  by direct computation: for `x ≠ 0` with image not `T′`,
  `x(φ(P)) = X a b x = (y/x)²` from the curve equation; at the `T′`
  boundary, `a² − 4b = (a + 2x)²`; the cases `P ∈ {O, T}` are the repo's
  `phi_some_zero`. Packaged: `deltaPhi_comp_phiHom`
  (`deltaPhi a b hb hd (phiHom a b hb hd P) = 0`) and the subgroup form
  `phiHom_range_le_deltaPhi_ker : (phiHom a b hb hd).range ≤ (deltaPhi a b hb hd).ker`.
- `deltaDual_comp_dual (a b : ℚ) (hb : b ≠ 0) (hd : a² − 4b ≠ 0)
  (P' : (D a b).Point) : delta a b hb (dualHom a b hb hd P') = 1`:
  for `x′ ≠ 0` with image not `T`,
  `x(ψ(P′)) = X(−2a, a²−4b, x′)/4 = (y′/(2x′))²` (via the repo's
  `dual_some`); at the `T` boundary, `b = ((x′ − a)/2)²`; at `x′ = 0`
  the raw dual already vanishes (`rawDual_some_zero`). Packaged:
  `deltaDual_comp_dualHom`, `dualHom_range_le_deltaDual_ker`.

Finite image bounds (priority 3, last item), over integer parameters:

- `deltaDual_image_bound (a b : ℤ) (hb : b ≠ 0) (hbQ : (b : ℚ) ≠ 0)
  (P : (E ↑a ↑b).Point) : ∃ d : ℤ, Squarefree d ∧ d ∣ b ∧
  delta ↑a ↑b hbQ P = cls ↑d`. Proof: `O ↦ [1]`; `T ↦ [b]`, whose
  squarefree representative from `TwoDescentBridges.integer_squareclass`
  still divides `b`; every other point goes through the repo's proved
  arithmetic input `TwoDescentBridges.rational_point_cover_complete`,
  which writes `x = d·u²/v²` with `d` squarefree, `d ∣ b`, and then
  `cls_eq_of_int_rep`.
- `deltaPhi_image_bound (a b : ℤ) (hd : a² − 4b ≠ 0)
  (hdQ : (↑a)² − 4↑b ≠ 0) (P' : (D ↑a ↑b).Point) :
  ∃ d : ℤ, Squarefree d ∧ d ∣ (a² − 4b) ∧ delta (−2↑a) ((↑a)²−4↑b) hdQ P' = cls ↑d`.
- `squarefree_divisors_finite {B : ℤ} (hB : B ≠ 0) :
  {d : ℤ | Squarefree d ∧ d ∣ B}.Finite` (each such `d` has
  `|d| ≤ |B|`; the hypothesis `B ≠ 0` is necessary — every squarefree
  integer divides `0`), and consequently the ranges themselves are
  finite: `deltaDual_range_finite`, `deltaPhi_range_finite`.

Uniqueness of the label (DescentDeltaLabel.lean):

- `squarefree_label_injective {d₁ d₂ : ℤ} (h₁ : Squarefree d₁)
  (h₂ : Squarefree d₂) (h : cls ↑d₁ = cls ↑d₂) : d₁ = d₂`
  (ratio is a square by `isSquare_of_cls_eq_one`, then wave one's
  bridge lemma
  `SquareclassIdentification.Int.eq_of_squarefree_of_isSquare_ratCast_div`).
- `deltaDual_label_unique`, `deltaPhi_label_unique`: the label whose
  existence the image bounds assert is the *only* one (`∃!` form), so
  δ and δ′ have well-defined squarefree labels.
- `delta_label_unique_of_rep`: at one point, two representations
  `x = dᵢ·wᵢ²` give `δ(point) = cls ↑d₁` and `d₁ = d₂`; this is wave
  one's `SquareclassIdentification.squareclass_label_unique` applied
  verbatim (the one place the companion imports wave one's file).

## Remaining — exact theorem-shaped targets

Everything the monograph's requirement list (docs/
ISOGENY_POINT_GROUPS_MONOGRAPH.md:107) asks for is now in place except
the two reverse exactness inclusions and the cardinality step. As
precise targets, in the language of `DescentDelta.lean`:

(T1) `ker δ ⊆ range φ`:
```
theorem deltaPhi_ker_le_phiHom_range (a b : ℤ) (hb : b ≠ 0) (hd : a^2 - 4*b ≠ 0)
    (hdQ : (a:ℚ)^2 - 4*(b:ℚ) ≠ 0) :
    (deltaPhi (a:ℚ) (b:ℚ) (by exact_mod_cast hb) hdQ).ker ≤ (phiHom (a:ℚ) (b:ℚ) (by exact_mod_cast hb) hdQ).range
```
Equivalently: every `P' : (D ↑a ↑b).Point` with `δ(P') = 1` is
`phiHom ↑a ↑b _ _ P` for some `P : (E ↑a ↑b).Point`. This is the
solubility half of the descent: a point with trivial label must be
lifted through the quartic homogeneous space
`w² = d·u⁴ + A·u²v² + (B/d)·v⁴` (the shape appearing in the cover
theorem's conclusion, here with `d = 1` and `(A, B) = (−2a, a²−4b)`).
It is **not** a formal consequence of the proved direction: the
cover theorem attaches such a quartic to a point already known to
come from a rational point of the isogenous curve, while the
converse — producing the preimage from the label condition — is the
missing step, and it is genuinely absent mathematics in the repo.

(T2) `ker δ′ ⊆ range ψ`: the same statement with `deltaDual` and
`dualHom` interchanged:
```
theorem deltaDual_ker_le_dualHom_range (a b : ℤ) (hb : b ≠ 0) (hd : a^2 - 4*b ≠ 0)
    (hdQ : (a:ℚ)^2 - 4*(b:ℚ) ≠ 0) :
    (deltaDual (a:ℚ) (b:ℚ) (by exact_mod_cast hb)).ker ≤ (dualHom (a:ℚ) (b:ℚ) (by exact_mod_cast hb) hdQ).range
```

(T3) The divisor-four step of `DescentRankBridge`: with both kernels
identified, `[E(ℚ) : ψ(D(ℚ)) + torsion]`-type counting gives the
factor `4 = |image δ| · |image δ′|`-style identity the rank bound
consumes; the repo's own `dual_index_product`-family results are the
natural home for it. No statement is fixed here because the exact
form depends on how (T1)/(T2) are packaged.

## Build notes

Builds were run in `repo_copy/` (a tar copy of the repo with
`.lake/packages` symlinked to the wave-one scratch project's Mathlib
cache), never in the read-only clone. Two operational hazards worth
recording: launching two `lake build` processes on the same tree
concurrently corrupts the build state (an olean can vanish), and the
`import Mathlib` module (`SquareclassUniqueness`) takes ~20 minutes to
compile on this 7 GB VM under parallel-agent load — both are
environment facts, not code issues. The final log `build_final.log`
is a single serial `lake build` of the three deliverable modules plus
the axiom-verification run.
