/-
Descent homomorphisms δ and δ′ for PerfectPower's two-isogeny setup
(wave two of the squareclass quotient identification;
`docs/ISOGENY_POINT_GROUPS_MONOGRAPH.md:107` requires "the squareclass
homomorphisms, the identification of their kernels with the respective
isogeny images, the associated finite image bounds").

The setup is the repository's own. For `a b : ℚ` with `b ≠ 0` and
`a² - 4b ≠ 0`,

* `E A B` is the curve `y² = x(x² + A x + B)` (`TwoIsogenyPointMap.E`),
* `φ = phiHom a b : E(a, b) →+ D(a, b)` is the degree-two isogeny to
  `D(a, b) = E(-2a, a² - 4b)`, with kernel `{O, (0, 0)}`,
* `ψ = dualHom a b : D(a, b) →+ E(a, b)` is the normalised dual,
  satisfying `ψ ∘ φ = [2]`.

This file constructs, for a general model `E A B`, the connecting
homomorphism of the `2`-isogeny descent whose kernel point is `(0, 0)`:

  `delta A B hB : (E A B).Point → ℚˣ ⧸ squaresSubgroup`,
  `δ(O) = 1`, `δ(x, y) = [x]` (the class of the `x`-coordinate in
  `ℚ*/ℚ*²`) for `x ≠ 0`, and `δ(0, 0) = [B]`,

packaged as the group homomorphism `deltaHom` into the additive view
`Additive (ℚˣ ⧸ squaresSubgroup)`.

The target `ℚˣ ⧸ ℚˣ²` is built directly as the quotient of `ℚˣ` by
the subgroup of squares (Mathlib v4.20.0 has no bundled squareclass
group of `ℚ`). The map is defined by its coordinate values — no
choice of representative is involved, so well-definedness is
automatic. The representative description is recovered as a theorem:
for integer parameters, the arithmetic input
`TwoDescentBridges.rational_point_cover_complete` (with
`TwoDescentBridges.integer_squareclass` at the exceptional point)
shows every value of `δ` is `[d]` for a squarefree integer `d`
dividing the relevant coefficient; that this label `d` is unique is
the companion file `PerfectPower.DescentDeltaLabel`, which bridges
to wave one's uniqueness theorem
(`SquareclassIdentification.squareclass_label_unique`).

Specialisations (`deltaHom` at the two models):

* `deltaPhi a b hb hd = deltaHom (-2a) (a² - 4b) hd :
  D(a, b)(ℚ) →+ Additive (ℚˣ ⧸ ℚˣ²)` is the descent map attached to
  the isogeny `φ : E → D`, and
* `deltaDual a b hb = deltaHom a b hb :
  E(a, b)(ℚ) →+ Additive (ℚˣ ⧸ ℚˣ²)` is the one attached to the
  dual isogeny `ψ : D → E`.

What is proved here (all compiled, axioms exactly the standard
three):

* `delta` is a group homomorphism (`delta_add`, via the repo's
  `translate_coordinates` and `chord_roots`), packaged as `deltaHom`;
  `δ(O) = 1` is `delta_zero`.
* The kernel inclusions supported by direct coordinate computation:
  `δ ∘ φ = 0` and `δ′ ∘ ψ = 0` pointwise
  (`deltaPhi_comp_phi`, `deltaDual_comp_dual`, and the packaged
  forms `deltaPhi_comp_phiHom`, `deltaDual_comp_dualHom`), i.e.
  `range φ ≤ ker δ` and `range ψ ≤ ker δ′`
  (`phiHom_range_le_deltaPhi_ker`, `dualHom_range_le_deltaDual_ker`).
  Note the pairing: `δ` belongs to `φ` (it lands on `D`, the target
  of `φ`), and `δ′` belongs to `ψ`.
* Finite image bounds over integer parameters: every value of `δ′`
  is `[d]` for a squarefree integer `d ∣ b`, and every value of `δ`
  is `[d]` for a squarefree integer `d ∣ a² - 4b`
  (`deltaDual_image_bound`, `deltaPhi_image_bound`); the squarefree
  divisors of a nonzero integer are finite
  (`squarefree_divisors_finite`), so both ranges are finite
  (`deltaDual_range_finite`, `deltaPhi_range_finite`).

What is NOT proved here: the reverse inclusions
`ker δ ⊆ range φ` and `ker δ′ ⊆ range ψ` (the homogeneous-space
solubility half of the identification — a point `P'` of `D` with
`δ(P') = 1` must be produced as a `φ`-image, via the quartic
homogeneous spaces of the descent, and dually), and the
divisor-four cardinality step of `DescentRankBridge`.
-/

import PerfectPower.TwoIsogenyDual
import PerfectPower.TwoDescentBridges

namespace PerfectPower.DescentDelta

open WeierstrassCurve WeierstrassCurve.Affine
open TwoIsogenyPointMap
open TwoIsogenyDual

/-- The subgroup of squares of `ℚˣ`: the kernel of the squareclass
projection `ℚˣ → ℚˣ/ℚˣ²`. -/
def squaresSubgroup : Subgroup ℚˣ where
  carrier := {u | IsSquare u}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := fun hu hv => hu.mul hv
  inv_mem' := fun hu => hu.inv

instance : squaresSubgroup.Normal where
  conj_mem := fun u hu g => by
    have h : g * u * g⁻¹ = u := by
      rw [mul_comm g u, mul_assoc, mul_inv_cancel, mul_one]
    rw [h]
    exact hu

/-- The squareclass of a rational number. By convention `cls 0 = 1`
(the value is only ever used at nonzero arguments, and at `0` as the
neutral element); for `q ≠ 0`, `cls q` is the class of `q` in
`ℚˣ ⧸ ℚˣ²`. Note `cls` takes no `q ≠ 0` proof argument, which keeps
rewriting with coordinate identities free of dependent-proof issues. -/
def cls (q : ℚ) : ℚˣ ⧸ squaresSubgroup :=
  if h : q = 0 then 1 else QuotientGroup.mk' squaresSubgroup (Units.mk0 q h)

theorem cls_of_ne {q : ℚ} (hq : q ≠ 0) :
    cls q = QuotientGroup.mk' squaresSubgroup (Units.mk0 q hq) :=
  dif_neg hq

theorem cls_zero : cls 0 = 1 := dif_pos rfl

theorem mk'_eq_one_of_isSquare {t : ℚˣ} (h : IsSquare t) :
    QuotientGroup.mk' squaresSubgroup t = 1 := by
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff t).mpr h

/-- A rational square has trivial squareclass. -/
theorem cls_eq_one_of_isSquare {q : ℚ} (hq : q ≠ 0) (h : IsSquare q) : cls q = 1 := by
  rw [cls_of_ne hq]
  apply mk'_eq_one_of_isSquare
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact hq hs
  refine ⟨Units.mk0 s hs0, ?_⟩
  ext
  simp only [Units.val_mul, Units.val_mk0]
  exact hs

/-- The class of `1` is trivial. -/
theorem cls_one : cls 1 = 1 :=
  cls_eq_one_of_isSquare one_ne_zero ⟨1, by norm_num⟩

/-- Conversely, a rational number with trivial squareclass is a
square: the membership of `Units.mk0 q _` in `squaresSubgroup` is, by
definition, a square root in `ℚˣ`, whose value is a square root
in `ℚ`. -/
theorem isSquare_of_cls_eq_one {q : ℚ} (hq : q ≠ 0) (h : cls q = 1) :
    IsSquare q := by
  rw [cls_of_ne hq] at h
  have hmem : Units.mk0 q hq ∈ squaresSubgroup :=
    (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨s, hs⟩ := hmem
  refine ⟨(s : ℚ), ?_⟩
  have h2 : ((Units.mk0 q hq : ℚˣ) : ℚ) = ((s * s : ℚˣ) : ℚ) := by rw [hs]
  simp only [Units.val_mk0, Units.val_mul] at h2
  exact h2

theorem cls_mul {u v : ℚ} (hu : u ≠ 0) (hv : v ≠ 0) :
    cls (u * v) = cls u * cls v := by
  rw [cls_of_ne (mul_ne_zero hu hv), cls_of_ne hu, cls_of_ne hv,
    ← map_mul (QuotientGroup.mk' squaresSubgroup)]
  congr 1
  ext
  simp only [Units.val_mul, Units.val_mk0]

theorem cls_sq {s : ℚ} (hs : s ≠ 0) : cls (s ^ 2) = 1 :=
  cls_eq_one_of_isSquare (pow_ne_zero 2 hs) ⟨s, pow_two s⟩

/-- Multiplying by a square does not change the squareclass. -/
theorem cls_eq_of_mul_square {u v s : ℚ} (hv : v ≠ 0) (hs : s ≠ 0)
    (h : u = v * s ^ 2) : cls u = cls v := by
  have hu : u ≠ 0 := by
    rw [h]
    exact mul_ne_zero hv (pow_ne_zero 2 hs)
  have hcls : cls u = cls (v * s ^ 2) := by rw [h]
  rw [hcls, cls_mul hv (pow_ne_zero 2 hs), cls_sq hs, mul_one]

theorem cls_inv {q : ℚ} (hq : q ≠ 0) : cls q⁻¹ = cls q := by
  apply cls_eq_of_mul_square hq (inv_ne_zero hq)
  rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

/-- The key multiplicativity identity in squareclass form: if the
product `u * v * w` is a square of a rational, then
`[w] = [u] * [v]` in `ℚˣ ⧸ ℚˣ²` (every class is its own inverse). -/
theorem cls_eq_of_mul_isSquare {u v w : ℚ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : IsSquare (u * v * w)) : cls w = cls u * cls v := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact mul_ne_zero (mul_ne_zero hu hv) hw hs
  rw [cls_of_ne hu, cls_of_ne hv, cls_of_ne hw,
    ← map_mul (QuotientGroup.mk' squaresSubgroup), QuotientGroup.mk'_eq_mk']
  refine ⟨(Units.mk0 (s / w) (div_ne_zero hs0 hw)) ^ 2,
    ⟨Units.mk0 (s / w) (div_ne_zero hs0 hw), pow_two _⟩, ?_⟩
  ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  field_simp [hw]
  linear_combination (-w) * hs

/-- The descent map of the model `E A B : y² = x(x² + A x + B)`, as a
bare function: `δ(O) = 1`, `δ(x, y) = [x]` for `x ≠ 0`, and the
exceptional value `δ(0, 0) = [B]` at the rational two-torsion point.
The homomorphism property is `delta_add` below. -/
noncomputable def delta (A B : ℚ) (_hB : B ≠ 0) : (E A B).Point → ℚˣ ⧸ squaresSubgroup
  | .zero => 1
  | @Point.some _ _ _ x _y _ => if x = 0 then cls B else cls x

@[simp] theorem delta_zero (A B : ℚ) (hB : B ≠ 0) :
    delta A B hB 0 = 1 := rfl

theorem delta_some_of_ne {A B : ℚ} (hB : B ≠ 0) {x y : ℚ}
    (hp : (E A B).Nonsingular x y) (hx : x ≠ 0) :
    delta A B hB (Point.some hp) = cls x := by
  simp only [delta]
  exact if_neg hx

theorem delta_some_of_eq {A B : ℚ} (hB : B ≠ 0) {x y : ℚ}
    (hp : (E A B).Nonsingular x y) (hx : x = 0) :
    delta A B hB (Point.some hp) = cls B := by
  subst hx
  simp only [delta]
  exact if_pos trivial

/-- Translation by the point `(0, 0)`: for `P = (x, y)` with `x ≠ 0`
on `E A B`, the sum `P + (0, 0)` has `x`-coordinate `B / x`
(`translate_coordinates`), and `[B / x] = [B] * [x]` because
`B / x = (B * x) * (x⁻¹)^2`. This is the boundary case of the
homomorphism law at the kernel of `φ`. -/
theorem delta_add_zero_point (A B : ℚ) (hB : B ≠ 0) {x y : ℚ}
    (hp : (E A B).Nonsingular x y) (hp0 : (E A B).Nonsingular 0 0)
    (hx : x ≠ 0) :
    delta A B hB (Point.some hp + Point.some hp0) =
      delta A B hB (Point.some hp) * delta A B hB (Point.some hp0) := by
  have hc := translate_coordinates A B x y hx ((equation ..).mp hp.1)
  have hxy : ¬ (x = 0 ∧ y = (E A B).negY 0 0) := fun h => hx h.1
  have hsumx : (E A B).addX x 0 ((E A B).slope x 0 y 0) ≠ 0 := by
    rw [hc.1]
    exact div_ne_zero hB hx
  have e1 : delta A B hB (Point.some hp + Point.some hp0) = cls (B / x) := by
    rw [Point.add_some hxy, delta_some_of_ne hB _ hsumx, hc.1]
  have e2 : delta A B hB (Point.some hp) = cls x := delta_some_of_ne hB hp hx
  have e3 : delta A B hB (Point.some hp0) = cls B := delta_some_of_eq hB hp0 rfl
  have hbx : (B * x) * (x⁻¹) ^ 2 = B / x := by
    field_simp
    ring
  rw [e1, e2, e3, cls_eq_of_mul_square (mul_ne_zero hB hx) (inv_ne_zero hx) hbx.symm,
    cls_mul hB hx]
  exact mul_comm _ _

/-- The generic case of the homomorphism law: two points with nonzero
`x`-coordinates, not in the negation relation. By `chord_roots`, the
product `x₁ * x₂ * x₃` of the three collinear `x`-coordinates is the
square of the line's intercept, so `[x₃] = [x₁] * [x₂]` in the
squareclass group; when the sum is the `(0, 0)` point the intercept
vanishes and the second chord identity gives `x₁ * x₂ = B`. -/
theorem delta_add_generic (A B : ℚ) (hB : B ≠ 0) {x₁ x₂ y₁ y₂ : ℚ}
    (hp₁ : (E A B).Nonsingular x₁ y₁) (hp₂ : (E A B).Nonsingular x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = (E A B).negY x₂ y₂)) :
    delta A B hB (Point.some hp₁ + Point.some hp₂) =
      delta A B hB (Point.some hp₁) * delta A B hB (Point.some hp₂) := by
  have hs := chord_roots A B x₁ x₂ y₁ y₂ hp₁ hp₂ hxy
  have hprod : x₁ * x₂ * (E A B).addX x₁ x₂ ((E A B).slope x₁ x₂ y₁ y₂)
      = (y₁ - (E A B).slope x₁ x₂ y₁ y₂ * x₁) ^ 2 := hs.2.2
  have hpair : x₁ * x₂
      + x₁ * (E A B).addX x₁ x₂ ((E A B).slope x₁ x₂ y₁ y₂)
      + x₂ * (E A B).addX x₁ x₂ ((E A B).slope x₁ x₂ y₁ y₂)
      = B - 2 * (E A B).slope x₁ x₂ y₁ y₂
        * (y₁ - (E A B).slope x₁ x₂ y₁ y₂ * x₁) := hs.2.1
  rw [Point.add_some hxy, delta_some_of_ne hB hp₁ hx₁, delta_some_of_ne hB hp₂ hx₂]
  by_cases hr : (E A B).addX x₁ x₂ ((E A B).slope x₁ x₂ y₁ y₂) = 0
  · have hn : y₁ - (E A B).slope x₁ x₂ y₁ y₂ * x₁ = 0 := by
      have h := hprod
      rw [hr, mul_zero] at h
      exact pow_eq_zero h.symm
    have hxx : x₁ * x₂ = B := by
      rw [hr, hn] at hpair
      linear_combination hpair
    rw [delta_some_of_eq hB _ hr, ← cls_mul hx₁ hx₂, hxx]
  · rw [delta_some_of_ne hB _ hr]
    exact cls_eq_of_mul_isSquare hx₁ hx₂ hr
      ⟨_, by rw [pow_two] at hprod; exact hprod⟩

/-- **The homomorphism law for `δ`.** For all rational points `P, Q`
of `E A B`, `δ(P + Q) = δ(P) * δ(Q)` in `ℚˣ ⧸ squaresSubgroup`. The
proof is the case analysis of `phi_add` in the repo: the point at
infinity, translation by `(0, 0)` (`delta_add_zero_point`), the
vertical case `Q = -P`, and the generic chord case
(`delta_add_generic`). -/
theorem delta_add (A B : ℚ) (hB : B ≠ 0) (P Q : (E A B).Point) :
    delta A B hB (P + Q) = delta A B hB P * delta A B hB Q := by
  cases P with
  | zero =>
    show delta A B hB ((0 : (E A B).Point) + Q)
      = delta A B hB (0 : (E A B).Point) * delta A B hB Q
    rw [zero_add, delta_zero, one_mul]
  | @some x₁ y₁ hp₁ =>
    cases Q with
    | zero =>
      show delta A B hB (Point.some hp₁ + (0 : (E A B).Point))
        = delta A B hB (Point.some hp₁) * delta A B hB (0 : (E A B).Point)
      rw [add_zero, delta_zero, mul_one]
    | @some x₂ y₂ hp₂ =>
      by_cases hx₁ : x₁ = 0
      · subst hx₁
        have hy₁ : y₁ = 0 := by
          have he := (equation ..).mp hp₁.1
          simp only [zero_mul] at he
          exact pow_eq_zero he
        subst hy₁
        by_cases hx₂ : x₂ = 0
        · subst hx₂
          have hy₂ : y₂ = 0 := by
            have he := (equation ..).mp hp₂.1
            simp only [zero_mul] at he
            exact pow_eq_zero he
          subst hy₂
          have hsum : (Point.some hp₁ : (E A B).Point) + Point.some hp₁ = 0 := by
            apply Point.add_self_of_Y_eq
            rw [TwoIsogenyPointMap.negY]
            ring
          rw [show (Point.some hp₂ : (E A B).Point) = Point.some hp₁ from rfl,
            hsum, delta_zero, delta_some_of_eq hB hp₁ rfl, ← cls_mul hB hB]
          exact (cls_eq_one_of_isSquare (mul_ne_zero hB hB) ⟨B, rfl⟩).symm
        · rw [add_comm (Point.some hp₁) (Point.some hp₂), mul_comm]
          exact delta_add_zero_point A B hB hp₂ hp₁ hx₂
      · by_cases hx₂ : x₂ = 0
        · subst hx₂
          have hy₂ : y₂ = 0 := by
            have he := (equation ..).mp hp₂.1
            simp only [zero_mul] at he
            exact pow_eq_zero he
          subst hy₂
          exact delta_add_zero_point A B hB hp₁ hp₂ hx₁
        · by_cases hxy : x₁ = x₂ ∧ y₁ = (E A B).negY x₂ y₂
          · rw [Point.add_of_Y_eq hxy.1 hxy.2, delta_zero,
              delta_some_of_ne hB hp₁ hx₁, delta_some_of_ne hB hp₂ hx₂,
              ← hxy.1, ← cls_mul hx₁ hx₁]
            exact (cls_eq_one_of_isSquare (mul_ne_zero hx₁ hx₁) ⟨x₁, rfl⟩).symm
          · exact delta_add_generic A B hB hp₁ hp₂ hx₁ hx₂ hxy

/-- `δ` packaged as a group homomorphism from the additive group of
rational points of `E A B` to the additive view `Additive` of the
squareclass group. Together with `delta_zero` (which is
`deltaHom` at the point at infinity) this is the connecting
homomorphism of the `φ`-descent for this one curve; the two maps of
the two-isogeny descent are `deltaPhi` and `deltaDual` below. -/
noncomputable def deltaHom (A B : ℚ) (hB : B ≠ 0) :
    (E A B).Point →+ Additive (ℚˣ ⧸ squaresSubgroup) where
  toFun P := Additive.ofMul (delta A B hB P)
  map_zero' := by
    show Additive.ofMul (delta A B hB 0) = 0
    rw [delta_zero]
    rfl
  map_add' := by
    intro P Q
    show Additive.ofMul (delta A B hB (P + Q))
      = Additive.ofMul (delta A B hB P)
        + Additive.ofMul (delta A B hB Q)
    rw [delta_add]
    rfl

theorem deltaHom_apply (A B : ℚ) (hB : B ≠ 0) (P : (E A B).Point) :
    deltaHom A B hB P = Additive.ofMul (delta A B hB P) := rfl

/-- The descent map of the isogeny `φ : E a b → D a b`: the connecting
homomorphism `δ : D(ℚ) → ℚˣ ⧸ ℚˣ²`, `δ(P') = [x']` with the
exceptional value `δ(T') = [a² - 4b]` at the two-torsion point
`T' = (0, 0)` of `D`. -/
noncomputable abbrev deltaPhi (a b : ℚ) (_hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0) :
    (D a b).Point →+ Additive (ℚˣ ⧸ squaresSubgroup) :=
  deltaHom (-2 * a) (a ^ 2 - 4 * b) hd

/-- The descent map of the dual isogeny `ψ : D a b → E a b`: the
connecting homomorphism `δ' : E(ℚ) → ℚˣ ⧸ ℚˣ²`, `δ'(P) = [x]` with
the exceptional value `δ'(T) = [b]` at `T = (0, 0)`. -/
noncomputable abbrev deltaDual (a b : ℚ) (hb : b ≠ 0) :
    (E a b).Point →+ Additive (ℚˣ ⧸ squaresSubgroup) :=
  deltaHom a b hb

/-- The product of a point's `x`-coordinate expression with `x`
itself, in the form used repeatedly below: for `x ≠ 0`,
`(x + A + B / x) * x = x^2 + A * x + B`. -/
theorem x_add_div_mul (A B x : ℚ) (hx : x ≠ 0) :
    (x + A + B / x) * x = x ^ 2 + A * x + B := by
  rw [add_mul, add_mul, div_mul_cancel₀ B hx]
  ring

/-- **`δ ∘ φ = 1`, the pointwise form of `range φ ⊆ ker δ`.** For
every rational point `P` of `E a b`, the squareclass `δ(φ(P))` is
trivial. If `x ≠ 0` and the image point is not `T'`, its
`x`-coordinate is `X a b x = x + a + b / x = (y / x)^2` by the curve
equation; if the image is `T'` (that is, `X a b x = 0`), then
`x^2 + a * x + b = 0`, so the exceptional value `a^2 - 4 * b` equals
the square `(a + 2 * x)^2` and `δ(T') = 1` consistently; and
`φ(P) = O` for `P ∈ {O, T}` by `phi_eq_zero_iff`'s direction already
in the repo. -/
theorem deltaPhi_comp_phi (a b : ℚ) (hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0)
    (P : (E a b).Point) :
    delta (-2 * a) (a ^ 2 - 4 * b) hd (phi a b hb hd P) = 1 := by
  cases P with
  | zero =>
    show delta (-2 * a) (a ^ 2 - 4 * b) hd (phi a b hb hd (0 : (E a b).Point)) = 1
    rw [phi_zero, delta_zero]
  | @some x y hp =>
    by_cases hx : x = 0
    · subst hx
      rw [phi_some_zero a b y hb hd hp, delta_zero]
    · rw [phi_some a b x y hb hd hp hx]
      by_cases hX : X a b x = 0
      · rw [delta_some_of_eq hd _ hX]
        apply cls_eq_one_of_isSquare hd
        have hX2 : x + a + b / x = 0 := hX
        have hquad : x ^ 2 + a * x + b = 0 := by
          have h3 : (x + a + b / x) * x = x ^ 2 + a * x + b :=
            x_add_div_mul a b x hx
          rw [hX2, zero_mul] at h3
          exact h3.symm
        exact ⟨a + 2 * x, by linear_combination -4 * hquad⟩
      · rw [delta_some_of_ne hd _ hX]
        apply cls_eq_one_of_isSquare hX
        have hcurve : y ^ 2 = x * (x ^ 2 + a * x + b) := (equation ..).mp hp.1
        have hXx : X a b x * x = x ^ 2 + a * x + b := x_add_div_mul a b x hx
        have hmul : X a b x * x ^ 2 = y ^ 2 := by
          calc X a b x * x ^ 2 = (X a b x * x) * x := by ring
            _ = (x ^ 2 + a * x + b) * x := by rw [hXx]
            _ = y ^ 2 := by linear_combination -hcurve
        refine ⟨y / x, ?_⟩
        rw [div_mul_div_comm, ← pow_two y, ← pow_two x]
        exact (eq_div_iff (pow_ne_zero 2 hx)).mpr hmul

/-- `δ ∘ φ = 0` at the level of the packaged homomorphisms. -/
theorem deltaPhi_comp_phiHom (a b : ℚ) (hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0)
    (P : (E a b).Point) :
    deltaPhi a b hb hd (phiHom a b hb hd P) = 0 := by
  show Additive.ofMul (delta (-2 * a) (a ^ 2 - 4 * b) hd (phi a b hb hd P)) = 0
  rw [deltaPhi_comp_phi a b hb hd P]
  rfl

/-- **`range φ ⊆ ker δ`** as a subgroup inclusion: the first of the
two exactness inclusions of the two-isogeny descent that is provable
from the point-level kernel computation alone. -/
theorem phiHom_range_le_deltaPhi_ker (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (phiHom a b hb hd).range ≤ (deltaPhi a b hb hd).ker := by
  intro Q hQ
  rw [AddMonoidHom.mem_range] at hQ
  obtain ⟨P, rfl⟩ := hQ
  rw [AddMonoidHom.mem_ker]
  exact deltaPhi_comp_phiHom a b hb hd P

/-- **`δ' ∘ ψ = 1`, the pointwise form of `range ψ ⊆ ker δ'`.** For
every rational point `P'` of `D a b`, the squareclass `δ'(ψ(P'))` is
trivial. If `x' ≠ 0` and the image point is not `T`, its
`x`-coordinate is `X(-2a, a^2-4b, x') / 4 = (y' / (2 * x'))^2` by the
curve equation on `D`; if the image is `T` (that is,
`X(-2a, a^2-4b, x') = 0`), then `x'^2 - 2 * a * x' + (a^2 - 4 * b) =
0`, so the exceptional value `b` equals the square `((x' - a) / 2)^2`
and `δ'(T) = 1` consistently; and `ψ(P') = O` when `x' = 0` since
already the raw dual vanishes there (`rawDual_of_x_zero`). -/
theorem deltaDual_comp_dual (a b : ℚ) (hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0)
    (P' : (D a b).Point) :
    delta a b hb (dualHom a b hb hd P') = 1 := by
  cases P' with
  | zero =>
    show delta a b hb (dualHom a b hb hd (0 : (D a b).Point)) = 1
    rw [map_zero, delta_zero]
  | @some x y hp =>
    by_cases hx : x = 0
    · subst hx
      have h0 : dualHom a b hb hd (Point.some hp) = 0 := by
        have hr : rawDualHom a b hb hd (Point.some hp) = 0 :=
          rawDual_some_zero a b y hb hd hp
        show (scaleBackHom a b hb hd) (rawDualHom a b hb hd (Point.some hp)) = 0
        rw [hr, map_zero]
      rw [h0, delta_zero]
    · obtain ⟨hq, hqeq⟩ := dual_some a b x y hb hd hp hx
      rw [hqeq]
      by_cases hX : X (-2 * a) (a ^ 2 - 4 * b) x / 4 = 0
      · rw [delta_some_of_eq hb _ hX]
        apply cls_eq_one_of_isSquare hb
        have hX0 : X (-2 * a) (a ^ 2 - 4 * b) x = 0 := by
          have h4 : (X (-2 * a) (a ^ 2 - 4 * b) x / 4) * 4 = (0 : ℚ) := by
            rw [hX, zero_mul]
          rwa [div_mul_cancel₀ _ (by norm_num : (4 : ℚ) ≠ 0)] at h4
        have hX2 : x + -2 * a + (a ^ 2 - 4 * b) / x = 0 := hX0
        have h3 : (x + -2 * a + (a ^ 2 - 4 * b) / x) * x
            = x ^ 2 + -2 * a * x + (a ^ 2 - 4 * b) :=
          x_add_div_mul (-2 * a) (a ^ 2 - 4 * b) x hx
        rw [hX2, zero_mul] at h3
        exact ⟨(x - a) / 2, by linear_combination (-1 / 4 : ℚ) * h3.symm⟩
      · rw [delta_some_of_ne hb _ hX]
        apply cls_eq_one_of_isSquare hX
        have hcurve : y ^ 2 = x * (x ^ 2 + -2 * a * x + (a ^ 2 - 4 * b)) :=
          (equation ..).mp hp.1
        have hXx : X (-2 * a) (a ^ 2 - 4 * b) x * x
            = x ^ 2 + -2 * a * x + (a ^ 2 - 4 * b) :=
          x_add_div_mul (-2 * a) (a ^ 2 - 4 * b) x hx
        have hmul : X (-2 * a) (a ^ 2 - 4 * b) x * (4 * x ^ 2) = y ^ 2 * 4 := by
          calc X (-2 * a) (a ^ 2 - 4 * b) x * (4 * x ^ 2)
              = (X (-2 * a) (a ^ 2 - 4 * b) x * x) * (4 * x) := by ring
            _ = (x ^ 2 + -2 * a * x + (a ^ 2 - 4 * b)) * (4 * x) := by rw [hXx]
            _ = y ^ 2 * 4 := by linear_combination -4 * hcurve
        refine ⟨y / (2 * x), ?_⟩
        rw [div_mul_div_comm]
        have hden : (2 * x) * (2 * x) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hx) (mul_ne_zero (by norm_num) hx)
        rw [eq_div_iff hden]
        linear_combination (1 / 4 : ℚ) * hmul

/-- `δ' ∘ ψ = 0` at the level of the packaged homomorphisms. -/
theorem deltaDual_comp_dualHom (a b : ℚ) (hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0)
    (P' : (D a b).Point) :
    deltaDual a b hb (dualHom a b hb hd P') = 0 := by
  show Additive.ofMul (delta a b hb (dualHom a b hb hd P')) = 0
  rw [deltaDual_comp_dual a b hb hd P']
  rfl

/-- **`range ψ ⊆ ker δ'`** as a subgroup inclusion. -/
theorem dualHom_range_le_deltaDual_ker (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (dualHom a b hb hd).range ≤ (deltaDual a b hb).ker := by
  intro Q hQ
  rw [AddMonoidHom.mem_range] at hQ
  obtain ⟨P', rfl⟩ := hQ
  rw [AddMonoidHom.mem_ker]
  exact deltaDual_comp_dualHom a b hb hd P'

/-- If a rational number is written as `d * u^2 / v^2` with integers
`d, u, v` and `u, v ≠ 0`, its squareclass is the class of the integer
`d` itself: in `cls` terms, `q = (d : ℚ) * ((u : ℚ) / (v : ℚ))^2`. -/
theorem cls_eq_of_int_rep {q : ℚ} {d u v : ℤ} (hu : (u : ℚ) ≠ 0)
    (hv : (v : ℚ) ≠ 0) (h : q = (d : ℚ) * (u : ℚ) ^ 2 / (v : ℚ) ^ 2) :
    cls q = cls (d : ℚ) := by
  by_cases hd : (d : ℚ) = 0
  · have hq : q = 0 := by
      rw [h, hd]
      simp
    rw [hq, hd]
  · have hq0 : q ≠ 0 := by
      rw [h]
      exact div_ne_zero (mul_ne_zero hd (pow_ne_zero 2 hu)) (pow_ne_zero 2 hv)
    refine cls_eq_of_mul_square hd (div_ne_zero hu hv) ?_
    rw [h, div_pow, mul_div_assoc]

/-- **The image bound for `δ'` (integer parameters).** For integers
`a, b` with `b ≠ 0`, every value of `δ'` on `E(a, b)` is the class of
a squarefree integer `d` dividing `b`. The point at infinity takes
the value `1 = [1]`; the point `T` takes `[b]`, whose squarefree
representative (from `TwoDescentBridges.integer_squareclass`) still
divides `b`; every other point is handled by the proved arithmetic
input `TwoDescentBridges.rational_point_cover_complete`, which
writes the `x`-coordinate as `d * u^2 / v^2` with `d` squarefree
dividing `b`. -/
theorem deltaDual_image_bound (a b : ℤ) (hb : b ≠ 0) (hbQ : (b : ℚ) ≠ 0)
    (P : (E (a : ℚ) (b : ℚ)).Point) :
    ∃ d : ℤ, Squarefree d ∧ d ∣ b ∧
      delta (a : ℚ) (b : ℚ) hbQ P = cls (d : ℚ) := by
  cases P with
  | zero =>
    refine ⟨1, squarefree_one, one_dvd b, ?_⟩
    show delta (a : ℚ) (b : ℚ) hbQ (0 : (E (a : ℚ) (b : ℚ)).Point)
      = cls ((1 : ℤ) : ℚ)
    rw [delta_zero, show ((1 : ℤ) : ℚ) = 1 from by norm_num, cls_one]
  | @some x y hp =>
    by_cases hx : x = 0
    · subst hx
      obtain ⟨d, s, hdsf, hdeq⟩ := TwoDescentBridges.integer_squareclass b hb
      refine ⟨d, hdsf, ⟨s ^ 2, hdeq⟩, ?_⟩
      have hd0 : d ≠ 0 := by
        intro hdz
        apply hb
        rw [hdeq, hdz, zero_mul]
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
      have hcast : (b : ℚ) = (d : ℚ) * (s : ℚ) ^ 2 := by
        have h2 := congrArg (fun n : ℤ => (n : ℚ)) hdeq
        push_cast at h2
        exact h2
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp at hdeq
        exact hb hdeq
      rw [delta_some_of_eq hbQ hp rfl, hcast]
      exact cls_eq_of_mul_square hdQ (by exact_mod_cast hs0) rfl
    · have hcurve : y ^ 2 = x * (x ^ 2 + (a : ℚ) * x + (b : ℚ)) :=
        (equation ..).mp hp.1
      obtain ⟨d, u, v, w, hdsf, hddiv, hu, hv, _hcop, hrep, _hw, _hy⟩ :=
        TwoDescentBridges.rational_point_cover_complete a b x y hx hcurve
      refine ⟨d, hdsf, hddiv, ?_⟩
      rw [delta_some_of_ne hbQ hp hx]
      exact cls_eq_of_int_rep (by exact_mod_cast hu)
        (by exact_mod_cast (ne_of_gt hv)) hrep

/-- **The image bound for `δ` (integer parameters).** For integers
`a, b` with `a^2 - 4 * b ≠ 0`, every value of `δ` on the isogenous
curve `D(a, b)` is the class of a squarefree integer `d` dividing
`a^2 - 4 * b`, by the same argument as `deltaDual_image_bound`
applied to the parameters `(-2 * a, a^2 - 4 * b)`. -/
theorem deltaPhi_image_bound (a b : ℤ) (hd : a ^ 2 - 4 * b ≠ 0)
    (hdQ : (a : ℚ) ^ 2 - 4 * (b : ℚ) ≠ 0)
    (P' : (D (a : ℚ) (b : ℚ)).Point) :
    ∃ d : ℤ, Squarefree d ∧ d ∣ (a ^ 2 - 4 * b) ∧
      delta (-2 * (a : ℚ)) ((a : ℚ) ^ 2 - 4 * (b : ℚ)) hdQ P' = cls (d : ℚ) := by
  cases P' with
  | zero =>
    refine ⟨1, squarefree_one, one_dvd _, ?_⟩
    show delta (-2 * (a : ℚ)) ((a : ℚ) ^ 2 - 4 * (b : ℚ)) hdQ
        (0 : (D (a : ℚ) (b : ℚ)).Point) = cls ((1 : ℤ) : ℚ)
    rw [delta_zero, show ((1 : ℤ) : ℚ) = 1 from by norm_num, cls_one]
  | @some x y hp =>
    by_cases hx : x = 0
    · subst hx
      obtain ⟨d, s, hdsf, hdeq⟩ :=
        TwoDescentBridges.integer_squareclass (a ^ 2 - 4 * b) hd
      refine ⟨d, hdsf, ⟨s ^ 2, hdeq⟩, ?_⟩
      have hd0 : d ≠ 0 := by
        intro hdz
        apply hd
        rw [hdeq, hdz, zero_mul]
      have hdQ' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
      have hcast : (a : ℚ) ^ 2 - 4 * (b : ℚ) = (d : ℚ) * (s : ℚ) ^ 2 := by
        have h2 := congrArg (fun n : ℤ => (n : ℚ)) hdeq
        push_cast at h2
        exact h2
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp at hdeq
        exact hd hdeq
      rw [delta_some_of_eq hdQ hp rfl, hcast]
      exact cls_eq_of_mul_square hdQ' (by exact_mod_cast hs0) rfl
    · have hcurve : y ^ 2
          = x * (x ^ 2 + ((-2 * a : ℤ) : ℚ) * x + ((a ^ 2 - 4 * b : ℤ) : ℚ)) := by
        have h := (equation (-2 * (a : ℚ)) ((a : ℚ) ^ 2 - 4 * (b : ℚ)) x y).mp hp.1
        push_cast
        linear_combination h
      obtain ⟨d, u, v, w, hdsf, hddiv, hu, hv, _hcop, hrep, _hw, _hy⟩ :=
        TwoDescentBridges.rational_point_cover_complete (-2 * a) (a ^ 2 - 4 * b)
          x y hx hcurve
      refine ⟨d, hdsf, hddiv, ?_⟩
      rw [delta_some_of_ne hdQ hp hx]
      exact cls_eq_of_int_rep (by exact_mod_cast hu)
        (by exact_mod_cast (ne_of_gt hv)) hrep

/-- For a nonzero integer `B`, the squarefree divisors of `B` form a
finite set: each has absolute value at most `|B|`. (For `B = 0` the
statement would be false — every squarefree integer divides `0` —
but the descent only applies it to the nonzero coefficients `b` and
`a^2 - 4 * b`.) -/
theorem squarefree_divisors_finite {B : ℤ} (hB : B ≠ 0) :
    {d : ℤ | Squarefree d ∧ d ∣ B}.Finite := by
  have hpos : 0 < B.natAbs := Int.natAbs_pos.mpr hB
  apply Set.Finite.subset (Set.finite_Icc (-(B.natAbs : ℤ)) (B.natAbs : ℤ))
  intro d hd
  have hdvd : d ∣ B := hd.2
  have hnat : d.natAbs ∣ B.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
  have hle : d.natAbs ≤ B.natAbs := Nat.le_of_dvd hpos hnat
  have hle' : (d.natAbs : ℤ) ≤ (B.natAbs : ℤ) := by exact_mod_cast hle
  refine ⟨?_, ?_⟩
  · have h1 : -d ≤ (d.natAbs : ℤ) := by
      have h2 := Int.le_natAbs (a := -d)
      rwa [Int.natAbs_neg] at h2
    linarith
  · calc d ≤ (d.natAbs : ℤ) := Int.le_natAbs
      _ ≤ (B.natAbs : ℤ) := hle'

/-- **The image of `δ'` is finite** (integer parameters): it is
contained in the classes of the finitely many squarefree divisors
of `b`. This is the finiteness that makes the `φ`-descent terminate:
together with the analogous finiteness for `δ` and the exactness
inclusions, the rank bound of the descent becomes a finite check —
the remaining content of the rank statement is the reverse
inclusions `ker δ' ⊆ range φ`, `ker δ ⊆ range ψ`, which need the
homogeneous-space (quartic) analysis. -/
theorem deltaDual_range_finite (a b : ℤ) (hb : b ≠ 0) (hbQ : (b : ℚ) ≠ 0) :
    (Set.range (delta (a : ℚ) (b : ℚ) hbQ)).Finite := by
  apply Set.Finite.subset
    ((squarefree_divisors_finite hb).image (fun d : ℤ => cls (d : ℚ)))
  rintro _ ⟨P, rfl⟩
  obtain ⟨d, hdsf, hddiv, hval⟩ := deltaDual_image_bound a b hb hbQ P
  exact ⟨d, ⟨hdsf, hddiv⟩, hval.symm⟩

/-- **The image of `δ` is finite** (integer parameters). -/
theorem deltaPhi_range_finite (a b : ℤ) (hd : a ^ 2 - 4 * b ≠ 0)
    (hdQ : (a : ℚ) ^ 2 - 4 * (b : ℚ) ≠ 0) :
    (Set.range (delta (-2 * (a : ℚ)) ((a : ℚ) ^ 2 - 4 * (b : ℚ)) hdQ)).Finite := by
  apply Set.Finite.subset
    ((squarefree_divisors_finite hd).image (fun d : ℤ => cls (d : ℚ)))
  rintro _ ⟨P', rfl⟩
  obtain ⟨d, hdsf, hddiv, hval⟩ := deltaPhi_image_bound a b hd hdQ P'
  exact ⟨d, ⟨hdsf, hddiv⟩, hval.symm⟩

end PerfectPower.DescentDelta
