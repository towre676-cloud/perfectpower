import PerfectPower.DescentDelta
import PerfectPower.SquareclassUniqueness

/-!
# The squarefree label of a `δ`-value is well-defined and unique

Companion to `PerfectPower.DescentDelta`. The image-bound theorems
there show that every value of `δ` (resp. `δ'`) is `cls (d : ℚ)` for
some squarefree integer `d` dividing the relevant coefficient. This
file shows the label is *unique*, in three forms:

* `squarefree_label_injective`: two squarefree integers with the
  same squareclass in `ℚˣ ⧸ squaresSubgroup` are equal. The ratio
  of the labels is a rational square by
  `DescentDelta.isSquare_of_cls_eq_one`, and then wave one's own
  bridge lemma
  `SquareclassIdentification.Int.eq_of_squarefree_of_isSquare_ratCast_div`
  (the lemma their `squareclass_label_unique` is built on)
  finishes.
* `deltaDual_label_unique`, `deltaPhi_label_unique`: the label
  whose existence the image bounds assert is the *only* one, so
  `δ` and `δ'` have well-defined squarefree labels, exactly as the
  descent formalism requires.
* `delta_label_unique_of_rep`: at the level of a point and two
  representations `x = dᵢ * wᵢ ^ 2` of its `x`-coordinate, wave
  one's uniqueness theorem applies verbatim, and the common value
  is the label of `δ` at that point.
-/

namespace PerfectPower.DescentDelta

open WeierstrassCurve WeierstrassCurve.Affine
open TwoIsogenyPointMap

/-- An integer with the squarefree property is nonzero: `2 * 2`
divides `0` but `2` is not a unit. -/
theorem ne_zero_of_squarefree {d : ℤ} (h : Squarefree d) : d ≠ 0 := by
  rintro rfl
  have h4 : IsUnit (2 : ℤ) := h 2 (dvd_zero _)
  norm_num [Int.isUnit_iff] at h4

/-- **Uniqueness of the squarefree label of a squareclass.** If
`cls (d₁ : ℚ) = cls (d₂ : ℚ)` with `d₁, d₂` squarefree integers,
then `d₁ = d₂`. -/
theorem squarefree_label_injective {d₁ d₂ : ℤ} (h₁ : Squarefree d₁)
    (h₂ : Squarefree d₂) (h : cls (d₁ : ℚ) = cls (d₂ : ℚ)) : d₁ = d₂ := by
  have hd₁ : d₁ ≠ 0 := ne_zero_of_squarefree h₁
  have hd₂ : d₂ ≠ 0 := ne_zero_of_squarefree h₂
  have hd₁Q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁
  have hd₂Q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂
  have hdiv : cls ((d₁ : ℚ) / (d₂ : ℚ)) = 1 := by
    rw [div_eq_mul_inv, cls_mul hd₁Q (inv_ne_zero hd₂Q), cls_inv hd₂Q, h,
      ← cls_mul hd₂Q hd₂Q, ← pow_two]
    exact cls_sq hd₂Q
  have hsq : IsSquare ((d₁ : ℚ) / (d₂ : ℚ)) :=
    isSquare_of_cls_eq_one (div_ne_zero hd₁Q hd₂Q) hdiv
  exact SquareclassIdentification.Int.eq_of_squarefree_of_isSquare_ratCast_div
    h₁ h₂ hd₁ hd₂ hsq

/-- **The label of `δ'` is unique**: there is exactly one squarefree
divisor `d` of `b` with `δ'(P) = cls (d : ℚ)`. Existence is
`deltaDual_image_bound`; uniqueness is
`squarefree_label_injective`. -/
theorem deltaDual_label_unique (a b : ℤ) (hb : b ≠ 0) (hbQ : (b : ℚ) ≠ 0)
    (P : (E (a : ℚ) (b : ℚ)).Point) :
    ∃! d : ℤ, Squarefree d ∧ d ∣ b ∧
      delta (a : ℚ) (b : ℚ) hbQ P = cls (d : ℚ) := by
  obtain ⟨d₀, hsf₀, hdiv₀, hval₀⟩ := deltaDual_image_bound a b hb hbQ P
  refine ⟨d₀, ⟨hsf₀, hdiv₀, hval₀⟩, ?_⟩
  intro d' h'
  exact (squarefree_label_injective hsf₀ h'.1 (hval₀.symm.trans h'.2.2)).symm

/-- **The label of `δ` is unique**: there is exactly one squarefree
divisor `d` of `a^2 - 4 * b` with `δ(P') = cls (d : ℚ)`. -/
theorem deltaPhi_label_unique (a b : ℤ) (hd : a ^ 2 - 4 * b ≠ 0)
    (hdQ : (a : ℚ) ^ 2 - 4 * (b : ℚ) ≠ 0)
    (P' : (D (a : ℚ) (b : ℚ)).Point) :
    ∃! d : ℤ, Squarefree d ∧ d ∣ (a ^ 2 - 4 * b) ∧
      delta (-2 * (a : ℚ)) ((a : ℚ) ^ 2 - 4 * (b : ℚ)) hdQ P' = cls (d : ℚ) := by
  obtain ⟨d₀, hsf₀, hdiv₀, hval₀⟩ := deltaPhi_image_bound a b hd hdQ P'
  refine ⟨d₀, ⟨hsf₀, hdiv₀, hval₀⟩, ?_⟩
  intro d' h'
  exact (squarefree_label_injective hsf₀ h'.1 (hval₀.symm.trans h'.2.2)).symm

/-- At a single point, two squarefree representations of the
`x`-coordinate give the same label, and that label is the value of
`δ` there. This is wave one's
`SquareclassIdentification.squareclass_label_unique` applied
verbatim, together with `cls_eq_of_mul_square`. -/
theorem delta_label_unique_of_rep {A B : ℚ} (hB : B ≠ 0) {x y : ℚ}
    (hp : (E A B).Nonsingular x y) (hx : x ≠ 0) {d₁ d₂ : ℤ}
    (h₁ : Squarefree d₁) (h₂ : Squarefree d₂) {w₁ w₂ : ℚ} (hw₁ : w₁ ≠ 0)
    (hw₂ : w₂ ≠ 0) (hx₁ : x = (d₁ : ℚ) * w₁ ^ 2) (hx₂ : x = (d₂ : ℚ) * w₂ ^ 2) :
    delta A B hB (Point.some hp) = cls (d₁ : ℚ) ∧ d₁ = d₂ := by
  refine ⟨?_, SquareclassIdentification.squareclass_label_unique hx h₁ h₂
    hw₁ hw₂ hx₁ hx₂⟩
  rw [delta_some_of_ne hB hp hx]
  have hd₁Q : (d₁ : ℚ) ≠ 0 := by
    rcases eq_or_ne (d₁ : ℚ) 0 with h00 | h00
    · rw [h00] at hx₁
      simp at hx₁
      exact absurd hx₁ hx
    · exact h00
  exact cls_eq_of_mul_square hd₁Q hw₁ hx₁

end PerfectPower.DescentDelta
