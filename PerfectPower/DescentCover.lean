/-
Quartic covers and the reverse exactness inclusions of the
two-isogeny descent (wave three).

Wave two (`PerfectPower.DescentDelta`) constructed the connecting
homomorphisms `δ` and `δ'` of the descent for
`φ = phiHom a b : E(a, b) → D(a, b)` and its normalised dual
`ψ = dualHom a b : D(a, b) → E(a, b)`, and proved the inclusions
`range φ ≤ ker δ` and `range ψ ≤ ker δ'` by direct coordinate
computation. What remained open there (targets T1/T2 of that file's
report) was the reverse inclusions

  `ker δ ⊆ range φ`        and        `ker δ' ⊆ range ψ`,

the homogeneous-space (solubility) half of the descent: a point
with trivial label must be produced as an isogeny image.

This file closes both inclusions completely, over `ℚ`, with no
extra hypothesis. The mechanism is the classical quartic cover.
For a model `E A B : y² = x(x² + A x + B)` and a label `d`, the
homogeneous space is the quartic

  `C_d : w² = d·u⁴ + A·u²v² + (B/d)·v⁴`,

recorded here in the multiplied-out form `QuarticCover A B d u v w`
(no division by `d`). Three steps are proved:

* (cover ⟹ point, for every `d`) A rational point of `C_d` maps
  to the point `(d·u²/v², d·u·w/v³)` of `E A B`, whose `δ`-value
  is exactly `cls d` (`point_of_quarticCover`) — the same shape as
  the conclusion of the repository's
  `TwoDescentBridges.rational_point_cover_complete`, proved here
  in the converse direction.
* (kernel ⟹ cover, for `d = 1`) A point of `E A B` with
  `δ`-value `1` has a rational point on `C_1`, in the normalised
  form `v = 1` (`exists_cover_of_delta_eq_one`): for `x ≠ 0` the
  triviality of the label says `x = t²`, and `(t, 1, y/t)` lies
  on `C_1` by the curve equation; for `x = 0` the label says `B`
  is a square, and `(0, 1, s)` with `s² = B` lies on `C_1`.
  So for this descent the `d = 1` cover solubility that the
  general theory leaves as a hypothesis is *automatic* from
  `δ = 1`, via wave two's `isSquare_of_cls_eq_one`.
* (cover ⟹ preimage, for `d = 1`) A rational point of the `d = 1`
  cover of the isogenous model produces an explicit preimage
  under the isogeny (`phi_preimage_of_cover`,
  `dual_preimage_of_cover`). For `φ` the preimage of the point
  `(U², U·W)` of `D(a, b)` is the point of `E(a, b)` with
  `x`-coordinate `(U² - a + W)/2` and `y`-coordinate
  `x·U`: the two scalar identities that make this work,
  `x² + (a - U²)·x + b = 0` and `x² - b = x·W`, are exact
  consequences of the cover equation, by `linear_combination`
  with coefficients `1/4` and `-1/4`. The dual construction is
  the analogous one with the roles of the models exchanged.

Assembling the steps gives the exact theorems, first in the
reduction form requested by the wave-two report (the kernel
inclusion follows from `d = 1`-cover solubility,
`deltaPhi_ker_le_phiHom_range_of_soluble`,
`deltaDual_ker_le_dualHom_range_of_soluble`), and then
unconditionally, since the solubility step is proved:

* `deltaPhi_ker_le_phiHom_range`   — **T1**: `ker δ ≤ range φ`,
* `deltaDual_ker_le_dualHom_range` — **T2**: `ker δ' ≤ range ψ`,

together with the kernel identifications
`phiHom_range_eq_deltaPhi_ker` and `dualHom_range_eq_deltaDual_ker`
(antisymmetry with wave two's inclusions) and the integer-parameter
forms `deltaPhi_ker_le_phiHom_range_int`,
`deltaDual_ker_le_dualHom_range_int`, which are the wave-two
report's target statements verbatim.

Everything is proved; there is no `sorry`, and `#print axioms`
(wave three's `VerifyCover.lean`) shows every theorem here depends
only on `[propext, Classical.choice, Quot.sound]`.
-/

import PerfectPower.DescentDelta

namespace PerfectPower.DescentCover

open WeierstrassCurve WeierstrassCurve.Affine
open TwoIsogenyPointMap
open TwoIsogenyDual
open DescentDelta

/-- The quartic homogeneous space `C_d` of the model
`E A B : y² = x(x² + A x + B)`, in multiplied-out form: the
classical equation `w² = d·u⁴ + A·u²v² + (B/d)·v⁴` multiplied
through by `d`, so no division by the label occurs. For `d ≠ 0`
the two forms are equivalent over `ℚ`. -/
def QuarticCover (A B d : ℚ) (u v w : ℚ) : Prop :=
  d * w ^ 2 = d ^ 2 * u ^ 4 + A * d * u ^ 2 * v ^ 2 + B * v ^ 4

/-- At `d = 1` the cover is the plain quartic
`w² = u⁴ + A·u²v² + B·v⁴`. -/
theorem quarticCover_one_iff (A B : ℚ) (u v w : ℚ) :
    QuarticCover A B 1 u v w ↔ w ^ 2 = u ^ 4 + A * u ^ 2 * v ^ 2 + B * v ^ 4 := by
  unfold QuarticCover
  constructor <;> intro h <;> linear_combination h

/-- A rational point of the cover has a representative with
`v = 1`: scaling `(u, v, w)` to `(u/v, 1, w/v²)` preserves the
cover equation. This is why the preimage constructions below
lose nothing by working with the normalised form. -/
theorem quarticCover_scale (A B d : ℚ) {u v w : ℚ} (hv : v ≠ 0)
    (h : QuarticCover A B d u v w) :
    QuarticCover A B d (u / v) 1 (w / v ^ 2) := by
  have h' : d * w ^ 2 = d ^ 2 * u ^ 4 + A * d * u ^ 2 * v ^ 2 + B * v ^ 4 := h
  have e1 : d * (w / v ^ 2) ^ 2 = (d * w ^ 2) / v ^ 4 := by
    rw [div_pow, show (v ^ 2) ^ 2 = v ^ 4 from by ring, mul_div_assoc]
  have e2 : d ^ 2 * (u / v) ^ 4 + A * d * (u / v) ^ 2 * (1 : ℚ) ^ 2 + B * (1 : ℚ) ^ 4
      = (d ^ 2 * u ^ 4 + A * d * u ^ 2 * v ^ 2 + B * v ^ 4) / v ^ 4 := by
    field_simp [hv]
    ring
  unfold QuarticCover
  rw [e1, e2, h']

/-- **Cover ⟹ point, with the δ-bookkeeping.** A rational point
`(u, v, w)` of the quartic cover `C_d` of `E A B` (with `v ≠ 0`)
maps to the point `(d·u²/v², d·u·w/v³)` of `E A B`, and the
`δ`-value of that point is exactly `cls d`: for `u ≠ 0` the
`x`-coordinate is `d·(u/v)²`, and for `u = 0` the exceptional
value `cls B` equals `cls d` because the cover equation at
`u = 0` reads `d·w² = B·v⁴`. This is the converse direction of
the repository's `TwoDescentBridges.rational_point_cover_complete`
shape (which attaches cover data to a point already given). -/
theorem point_of_quarticCover (A B d : ℚ) (hd : d ≠ 0) (hB : B ≠ 0)
    (hdisc : A ^ 2 - 4 * B ≠ 0) {u v w : ℚ} (hv : v ≠ 0)
    (hcov : QuarticCover A B d u v w) :
    ∃ hp : (E A B).Nonsingular (d * u ^ 2 / v ^ 2) (d * u * w / v ^ 3),
      delta A B hB (Point.some hp) = cls d := by
  have h : d * w ^ 2 = d ^ 2 * u ^ 4 + A * d * u ^ 2 * v ^ 2 + B * v ^ 4 := hcov
  have hnum : (d * u * w) ^ 2
      = (d * u ^ 2) * ((d * u ^ 2) ^ 2 + A * (d * u ^ 2) * v ^ 2 + B * v ^ 4) := by
    linear_combination (d * u ^ 2) * h
  have hcurve : (d * u * w / v ^ 3) ^ 2
      = (d * u ^ 2 / v ^ 2) * ((d * u ^ 2 / v ^ 2) ^ 2
        + A * (d * u ^ 2 / v ^ 2) + B) := by
    have e2 : (d * u * w / v ^ 3) ^ 2 = (d * u * w) ^ 2 / v ^ 6 := by
      rw [div_pow]
      congr 1
      ring
    have e1 : (d * u ^ 2 / v ^ 2) * ((d * u ^ 2 / v ^ 2) ^ 2
          + A * (d * u ^ 2 / v ^ 2) + B)
        = ((d * u ^ 2) * ((d * u ^ 2) ^ 2 + A * (d * u ^ 2) * v ^ 2
          + B * v ^ 4)) / v ^ 6 := by
      field_simp [hv]
      ring
    rw [e2, e1, hnum]
  refine ⟨smooth A B _ _ hB hdisc hcurve, ?_⟩
  by_cases hu : u = 0
  · subst hu
    have h' : d * w ^ 2 = B * v ^ 4 := by
      have h0 : d * w ^ 2
          = d ^ 2 * (0 : ℚ) ^ 4 + A * d * (0 : ℚ) ^ 2 * v ^ 2 + B * v ^ 4 := h
      simpa using h0
    have hw : w ≠ 0 := by
      intro hw0
      apply hB
      rw [hw0] at h'
      have h'' : B * v ^ 4 = 0 := by linear_combination -h'
      exact (mul_eq_zero.mp h'').resolve_right (pow_ne_zero 4 hv)
    rw [delta_some_of_eq hB _ (by simp : d * (0 : ℚ) ^ 2 / v ^ 2 = 0)]
    refine cls_eq_of_mul_square hd (div_ne_zero hw (pow_ne_zero 2 hv)) ?_
    field_simp [hv]
    linear_combination -h'
  · rw [delta_some_of_ne hB _
      (div_ne_zero (mul_ne_zero hd (pow_ne_zero 2 hu)) (pow_ne_zero 2 hv))]
    refine cls_eq_of_mul_square hd (div_ne_zero hu hv) ?_
    rw [div_pow, mul_div_assoc]

/-- **Kernel ⟹ cover (d = 1 solubility is automatic).** If a
point `(x', y')` of `E A B` has `δ`-value `1`, then the `d = 1`
quartic cover of `E A B` has a rational point `(U, 1, W)` lying
over it, i.e. `x' = U²` and `y' = U·W`. For `x' ≠ 0`: the label
triviality says `x'` is a rational square `t²` (wave two's
`isSquare_of_cls_eq_one`), and `(t, y'/t)` satisfies the cover
equation by the curve equation at `(x', y')`. For `x' = 0` the
point is `(0, 0)`, the label says `B` is a square `s²`, and
`(0, s)` satisfies the cover equation directly. -/
theorem exists_cover_of_delta_eq_one (A B : ℚ) (hB : B ≠ 0) {x' y' : ℚ}
    (hp : (E A B).Nonsingular x' y') (hδ : delta A B hB (Point.some hp) = 1) :
    ∃ U W : ℚ, QuarticCover A B 1 U 1 W ∧ x' = U ^ 2 ∧ y' = U * W := by
  have hcurve : y' ^ 2 = x' * (x' ^ 2 + A * x' + B) := (equation ..).mp hp.1
  by_cases hx' : x' = 0
  · subst hx'
    have hy' : y' = 0 := by
      have h0 : y' ^ 2 = 0 := by
        rw [hcurve]
        simp
      exact pow_eq_zero h0
    have hclsB : cls B = 1 := (delta_some_of_eq hB hp rfl).symm.trans hδ
    obtain ⟨s, hs⟩ := isSquare_of_cls_eq_one hB hclsB
    refine ⟨0, s, ?_, by norm_num, by rw [hy']; simp⟩
    rw [quarticCover_one_iff]
    have hs2 : s ^ 2 = B := by rw [pow_two]; exact hs.symm
    rw [hs2]
    simp
  · have hcls : cls x' = 1 := (delta_some_of_ne hB hp hx').symm.trans hδ
    obtain ⟨t, ht⟩ := isSquare_of_cls_eq_one hx' hcls
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at ht
      exact hx' ht
    have ht2 : t ^ 2 = x' := by rw [pow_two, ← ht]
    have hcurve' : y' ^ 2 = t ^ 2 * (t ^ 4 + A * t ^ 2 + B) := by
      rw [← ht2] at hcurve
      linear_combination hcurve
    have hEq : (y' / t) ^ 2 = t ^ 4 + A * t ^ 2 + B := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 ht0)]
      linear_combination hcurve'
    refine ⟨t, y' / t, ?_, ht2.symm, ?_⟩
    · rw [quarticCover_one_iff]
      linear_combination hEq
    · rw [mul_comm t, div_mul_cancel₀ y' ht0]

/-- **Cover ⟹ φ-preimage (the constructive direction for T1).**
Let `(U, 1, W)` be a rational point of the `d = 1` quartic
cover of the isogenous model `D(a, b)` (parameters `-2a`,
`a² - 4b`). Then the point `(U², U·W)` of `D(a, b)` is a
`φ`-image: its preimage in `E(a, b)` is the point with
`x`-coordinate `x = (U² - a + W)/2` and `y`-coordinate `x·U`.
The verification is two scalar identities, exact consequences
of the cover equation `W² = U⁴ - 2a·U² + (a² - 4b)`:
`x² + (a - U²)·x + b = 0` (so `x² + a·x + b = U²·x`, giving both
the curve equation at the preimage and `X a b x = U²`) and
`x² - b = x·W` (giving `Y b x (x·U) = U·W`). Also `x ≠ 0`, since
`x = 0` would force `b = 0` by the second identity. -/
theorem phi_preimage_of_cover (a b : ℚ) (hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0)
    {U W : ℚ} (hcov : QuarticCover (-2 * a) (a ^ 2 - 4 * b) 1 U 1 W) :
    ∃ hp' : (D a b).Nonsingular (U ^ 2) (U * W),
      ∃ P : (E a b).Point, phi a b hb hd P = Point.some hp' := by
  have hcov1 : W ^ 2 = U ^ 4 + (-2 * a) * U ^ 2 + (a ^ 2 - 4 * b) := by
    have h := (quarticCover_one_iff (-2 * a) (a ^ 2 - 4 * b) U 1 W).mp hcov
    linear_combination h
  have hcurveD : (U * W) ^ 2
      = U ^ 2 * ((U ^ 2) ^ 2 + (-2 * a) * U ^ 2 + (a ^ 2 - 4 * b)) := by
    linear_combination U ^ 2 * hcov1
  refine ⟨smooth (-2 * a) (a ^ 2 - 4 * b) _ _ hd (dual_smooth a b hb) hcurveD, ?_⟩
  have hI2 : ((U ^ 2 - a + W) / 2) ^ 2 + (a - U ^ 2) * ((U ^ 2 - a + W) / 2) + b = 0 := by
    linear_combination (1 / 4 : ℚ) * hcov1
  have hI3 : ((U ^ 2 - a + W) / 2) ^ 2 - b = ((U ^ 2 - a + W) / 2) * W := by
    linear_combination (-1 / 4 : ℚ) * hcov1
  set x0 : ℚ := (U ^ 2 - a + W) / 2 with hx0def
  have hx0 : x0 ≠ 0 := by
    intro h0
    apply hb
    rw [h0] at hI3
    linear_combination -hI3
  have hcurveE : (x0 * U) ^ 2 = x0 * (x0 ^ 2 + a * x0 + b) := by
    linear_combination (-x0) * hI2
  have hP : (E a b).Nonsingular x0 (x0 * U) := smooth a b x0 (x0 * U) hb hd hcurveE
  refine ⟨Point.some hP, ?_⟩
  rw [phi_some a b x0 (x0 * U) hb hd hP hx0]
  apply some_congr
  · have hXx : X a b x0 * x0 = U ^ 2 * x0 := by
      have h1 : (x0 + a + b / x0) * x0 = U ^ 2 * x0 := by
        rw [add_mul, add_mul, div_mul_cancel₀ b hx0]
        linear_combination hI2
      exact h1
    exact mul_right_cancel₀ hx0 hXx
  · have hYx : Y b x0 (x0 * U) * x0 ^ 2 = (U * W) * x0 ^ 2 := by
      have h1 : Y b x0 (x0 * U) * x0 ^ 2 = (x0 * U) * (x0 ^ 2 - b) := by
        dsimp only [Y]
        field_simp [hx0]
      rw [h1]
      linear_combination (x0 * U) * hI3
    exact mul_right_cancel₀ (pow_ne_zero 2 hx0) hYx

/-- **Cover ⟹ ψ-preimage (the constructive direction for T2).**
Let `(U, 1, S)` be a rational point of the `d = 1` quartic
cover of `E(a, b)`. Then the point `(U², U·S)` of `E(a, b)` is
a `ψ`-image: its preimage in `D(a, b)` is the point with
`x'`-coordinate `a + 2·U² - 2·S` and `y'`-coordinate `-2·x'·U`.
The verification is again two scalar identities, exact
consequences of the cover equation `S² = U⁴ + a·U² + b`:
`x'² - (2a + 4·U²)·x' + (a² - 4b) = 0` (giving the curve
equation at the preimage and `X(-2a, a² - 4b, x') = 4·U²`) and
`x'² + 4·S·x' - (a² - 4b) = 0` (giving
`Y(a² - 4b, x', y') = 8·U·S`, and `x' ≠ 0`, since `x' = 0`
would force `a² - 4b = 0`). -/
theorem dual_preimage_of_cover (a b : ℚ) (hb : b ≠ 0) (hd : a ^ 2 - 4 * b ≠ 0)
    {U S : ℚ} (hcov : QuarticCover a b 1 U 1 S) :
    ∃ hp' : (D a b).Nonsingular (a + 2 * U ^ 2 - 2 * S)
        (-2 * (a + 2 * U ^ 2 - 2 * S) * U),
      ∃ hpE : (E a b).Nonsingular (U ^ 2) (U * S),
        dualHom a b hb hd (Point.some hp') = Point.some hpE := by
  have hcov1 : S ^ 2 = U ^ 4 + a * U ^ 2 + b := by
    have h := (quarticCover_one_iff a b U 1 S).mp hcov
    linear_combination h
  have hcurveE : (U * S) ^ 2
      = U ^ 2 * ((U ^ 2) ^ 2 + a * U ^ 2 + b) := by
    linear_combination U ^ 2 * hcov1
  have hJ2 : (a + 2 * U ^ 2 - 2 * S) ^ 2
      - (2 * a + 4 * U ^ 2) * (a + 2 * U ^ 2 - 2 * S) + (a ^ 2 - 4 * b) = 0 := by
    linear_combination (4 : ℚ) * hcov1
  have hJ5 : (a + 2 * U ^ 2 - 2 * S) ^ 2
      + 4 * S * (a + 2 * U ^ 2 - 2 * S) - (a ^ 2 - 4 * b) = 0 := by
    linear_combination (-4 : ℚ) * hcov1
  set x' : ℚ := a + 2 * U ^ 2 - 2 * S with hx'def
  set y' : ℚ := -2 * x' * U with hy'def
  have hx'0 : x' ≠ 0 := by
    intro h0
    apply hd
    rw [h0] at hJ5
    linear_combination -hJ5
  have hJ3 : x' ^ 2 + (-2 * a) * x' + (a ^ 2 - 4 * b) = 4 * U ^ 2 * x' := by
    linear_combination hJ2
  have hcurveD : y' ^ 2
      = x' * (x' ^ 2 + (-2 * a) * x' + (a ^ 2 - 4 * b)) := by
    rw [hy'def, hJ3]
    ring
  have hp' : (D a b).Nonsingular x' y' :=
    smooth (-2 * a) (a ^ 2 - 4 * b) x' y' hd (dual_smooth a b hb) hcurveD
  have hpE : (E a b).Nonsingular (U ^ 2) (U * S) :=
    smooth a b (U ^ 2) (U * S) hb hd hcurveE
  refine ⟨hp', hpE, ?_⟩
  obtain ⟨hq, hqeq⟩ := dual_some a b x' y' hb hd hp' hx'0
  rw [hqeq]
  apply some_congr
  · have hXx : X (-2 * a) (a ^ 2 - 4 * b) x' * x' = (4 * U ^ 2) * x' := by
      have h1 : (x' + -2 * a + (a ^ 2 - 4 * b) / x') * x'
          = x' ^ 2 + -2 * a * x' + (a ^ 2 - 4 * b) := by
        rw [add_mul, add_mul, div_mul_cancel₀ _ hx'0]
        ring
      have h2 : X (-2 * a) (a ^ 2 - 4 * b) x' * x'
          = x' ^ 2 + -2 * a * x' + (a ^ 2 - 4 * b) := h1
      rw [h2, hJ3]
    have hX : X (-2 * a) (a ^ 2 - 4 * b) x' = 4 * U ^ 2 :=
      mul_right_cancel₀ hx'0 hXx
    linear_combination (1 / 4 : ℚ) * hX
  · have hJ5' : x' ^ 2 - (a ^ 2 - 4 * b) = -4 * S * x' := by
      linear_combination hJ5
    have hYx : Y (a ^ 2 - 4 * b) x' y' * x' ^ 2 = (8 * (U * S)) * x' ^ 2 := by
      have h1 : Y (a ^ 2 - 4 * b) x' y' * x' ^ 2
          = y' * (x' ^ 2 - (a ^ 2 - 4 * b)) := by
        dsimp only [Y]
        field_simp [hx'0]
      rw [h1, hy'def, hJ5']
      ring
    have hY : Y (a ^ 2 - 4 * b) x' y' = 8 * (U * S) :=
      mul_right_cancel₀ (pow_ne_zero 2 hx'0) hYx
    linear_combination (1 / 8 : ℚ) * hY

/-- Extract `δ = 1` (multiplicative form) from membership in
`ker δ` (additive form). -/
theorem delta_eq_one_of_deltaPhi_ker {a b : ℚ} {hb : b ≠ 0} {hd : a ^ 2 - 4 * b ≠ 0}
    {P' : (D a b).Point} (h : P' ∈ (deltaPhi a b hb hd).ker) :
    delta (-2 * a) (a ^ 2 - 4 * b) hd P' = 1 := by
  rw [AddMonoidHom.mem_ker] at h
  have h2 := congrArg Additive.toMul h
  simpa [deltaPhi, deltaHom_apply] using h2

/-- Extract `δ' = 1` (multiplicative form) from membership in
`ker δ'` (additive form). -/
theorem delta_eq_one_of_deltaDual_ker {a b : ℚ} {hb : b ≠ 0}
    {P : (E a b).Point} (h : P ∈ (deltaDual a b hb).ker) :
    delta a b hb P = 1 := by
  rw [AddMonoidHom.mem_ker] at h
  have h2 := congrArg Additive.toMul h
  simpa [deltaDual, deltaHom_apply] using h2

/-- **T1, reduction form.** The inclusion `ker δ ≤ range φ`
follows from solubility of the `d = 1` cover: if every point
of `D(a, b)` with `δ = 1` is lay over by a rational point of
the cover `C_1` of `D(a, b)`, then every such point is a
`φ`-image. The implication is proved completely here; the
solubility hypothesis itself is discharged by
`exists_cover_of_delta_eq_one` in
`deltaPhi_ker_le_phiHom_range` below. -/
theorem deltaPhi_ker_le_phiHom_range_of_soluble (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0)
    (hsol : ∀ (x' y' : ℚ) (hp : (D a b).Nonsingular x' y'),
      delta (-2 * a) (a ^ 2 - 4 * b) hd (Point.some hp) = 1 →
      ∃ U W : ℚ, QuarticCover (-2 * a) (a ^ 2 - 4 * b) 1 U 1 W
        ∧ x' = U ^ 2 ∧ y' = U * W) :
    (deltaPhi a b hb hd).ker ≤ (phiHom a b hb hd).range := by
  intro P' hP'
  cases P' with
  | zero => exact AddMonoidHom.mem_range.mpr ⟨0, map_zero _⟩
  | @some x' y' hp =>
    have hδ : delta (-2 * a) (a ^ 2 - 4 * b) hd (Point.some hp) = 1 :=
      delta_eq_one_of_deltaPhi_ker hP'
    obtain ⟨U, W, hcov, hx', hy'⟩ := hsol x' y' hp hδ
    obtain ⟨hp'', P, hP⟩ := phi_preimage_of_cover a b hb hd hcov
    have hpt : Point.some hp'' = Point.some hp := some_congr hx'.symm hy'.symm
    rw [hpt] at hP
    exact AddMonoidHom.mem_range.mpr ⟨P, hP⟩

/-- **T1: `ker δ ≤ range φ`.** Every rational point of
`D(a, b)` with trivial `δ`-label is a `φ`-image. Proved by the
reduction above: the `d = 1`-cover solubility it requires is
automatic from `δ = 1`, by `exists_cover_of_delta_eq_one`
applied to the model `D(a, b)`. -/
theorem deltaPhi_ker_le_phiHom_range (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (deltaPhi a b hb hd).ker ≤ (phiHom a b hb hd).range :=
  deltaPhi_ker_le_phiHom_range_of_soluble a b hb hd
    (fun _ _ hp hδ =>
      exists_cover_of_delta_eq_one (-2 * a) (a ^ 2 - 4 * b) hd hp hδ)

/-- **The kernel identification for `δ`**: `ker δ = range φ`,
by antisymmetry with wave two's
`phiHom_range_le_deltaPhi_ker`. -/
theorem phiHom_range_eq_deltaPhi_ker (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (phiHom a b hb hd).range = (deltaPhi a b hb hd).ker :=
  le_antisymm (phiHom_range_le_deltaPhi_ker a b hb hd)
    (deltaPhi_ker_le_phiHom_range a b hb hd)

/-- **T1 in the wave-two report's exact integer form.** -/
theorem deltaPhi_ker_le_phiHom_range_int (a b : ℤ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) (hdQ : (a : ℚ) ^ 2 - 4 * (b : ℚ) ≠ 0) :
    (deltaPhi (a : ℚ) (b : ℚ) (by exact_mod_cast hb) hdQ).ker
      ≤ (phiHom (a : ℚ) (b : ℚ) (by exact_mod_cast hb) hdQ).range :=
  deltaPhi_ker_le_phiHom_range (a : ℚ) (b : ℚ) (by exact_mod_cast hb) hdQ

/-- **T2, reduction form.** The inclusion `ker δ' ≤ range ψ`
follows from solubility of the dual `d = 1` cover: if every
point of `E(a, b)` with `δ' = 1` is lay over by a rational
point of the cover `C_1` of `E(a, b)`, then every such point
is a `ψ`-image. -/
theorem deltaDual_ker_le_dualHom_range_of_soluble (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0)
    (hsol : ∀ (x y : ℚ) (hp : (E a b).Nonsingular x y),
      delta a b hb (Point.some hp) = 1 →
      ∃ U S : ℚ, QuarticCover a b 1 U 1 S ∧ x = U ^ 2 ∧ y = U * S) :
    (deltaDual a b hb).ker ≤ (dualHom a b hb hd).range := by
  intro P hP
  cases P with
  | zero => exact AddMonoidHom.mem_range.mpr ⟨0, map_zero _⟩
  | @some x y hp =>
    have hδ : delta a b hb (Point.some hp) = 1 :=
      delta_eq_one_of_deltaDual_ker hP
    obtain ⟨U, S, hcov, hx, hy⟩ := hsol x y hp hδ
    obtain ⟨hp', hpE, hdual⟩ := dual_preimage_of_cover a b hb hd hcov
    have hpt : Point.some hpE = Point.some hp := some_congr hx.symm hy.symm
    rw [hpt] at hdual
    exact AddMonoidHom.mem_range.mpr ⟨Point.some hp', hdual⟩

/-- **T2: `ker δ' ≤ range ψ`.** Every rational point of
`E(a, b)` with trivial `δ'`-label is a `ψ`-image. -/
theorem deltaDual_ker_le_dualHom_range (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (deltaDual a b hb).ker ≤ (dualHom a b hb hd).range :=
  deltaDual_ker_le_dualHom_range_of_soluble a b hb hd
    (fun _ _ hp hδ => exists_cover_of_delta_eq_one a b hb hp hδ)

/-- **The kernel identification for `δ'`**: `ker δ' = range ψ`,
by antisymmetry with wave two's
`dualHom_range_le_deltaDual_ker`. -/
theorem dualHom_range_eq_deltaDual_ker (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (dualHom a b hb hd).range = (deltaDual a b hb).ker :=
  le_antisymm (dualHom_range_le_deltaDual_ker a b hb hd)
    (deltaDual_ker_le_dualHom_range a b hb hd)

/-- **T2 in the wave-two report's exact integer form.** -/
theorem deltaDual_ker_le_dualHom_range_int (a b : ℤ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) (hdQ : (a : ℚ) ^ 2 - 4 * (b : ℚ) ≠ 0) :
    (deltaDual (a : ℚ) (b : ℚ) (by exact_mod_cast hb)).ker
      ≤ (dualHom (a : ℚ) (b : ℚ) (by exact_mod_cast hb) hdQ).range :=
  deltaDual_ker_le_dualHom_range (a : ℚ) (b : ℚ) (by exact_mod_cast hb) hdQ

end PerfectPower.DescentCover
