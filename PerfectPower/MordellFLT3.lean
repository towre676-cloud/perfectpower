import Mathlib.NumberTheory.FLT.Three
import PerfectPower.Basic

/-!
# A genus-one family with a nonempty, unconditional, kernel-checked hit list

For every integer `u ≠ 0`, the integral points of `y^2 = x^3 - 432 u^6` are exactly
`(12 u^2, ± 36 u^3)`.  An integral point gives

  `(36 u^3 + y)^3 + (36 u^3 - y)^3 = (6 u x)^3`,

so by Fermat's Last Theorem for exponent 3 (`fermatLastTheoremThree`, in Mathlib) one of the
three cubes vanishes.  `x = 0` is impossible, and `y = ± 36 u^3` forces `x^3 = (12 u^2)^3`.

Consequently `n^3 - 432 u^6` (for `n ≥ 1`) is a perfect square **iff** `n = 12 u^2`: a complete,
nonempty hit list for an infinite family of nonrigid genus-one polynomials, with no point list,
rank or external computation assumed.  (The curve `y^2 = x^3 - 432` is the classical Weierstrass
model of the Fermat cubic `a^3 + b^3 = c^3`.)
-/

namespace PerfectPower.MordellFLT3

lemma cube_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.pow_left_injective (by decide : Odd 3)) h

/-- **Integral points of `y^2 = x^3 - 432 u^6`.** -/
theorem points (u : ℤ) (hu : u ≠ 0) (x y : ℤ) :
    y ^ 2 = x ^ 3 - 432 * u ^ 6 ↔ x = 12 * u ^ 2 ∧ (y = 36 * u ^ 3 ∨ y = -(36 * u ^ 3)) := by
  constructor
  · intro h
    have flt := fermatLastTheoremFor_iff_int.mp fermatLastTheoremThree
    have key : (36 * u ^ 3 + y) ^ 3 + (36 * u ^ 3 - y) ^ 3 = (6 * u * x) ^ 3 := by
      linear_combination (216 * u ^ 3) * h
    by_cases ha : 36 * u ^ 3 + y = 0
    · have hy : y = -(36 * u ^ 3) := by linarith
      refine ⟨cube_inj ?_, Or.inr hy⟩
      rw [hy] at h; linear_combination -h
    by_cases hb : 36 * u ^ 3 - y = 0
    · have hy : y = 36 * u ^ 3 := by linarith
      refine ⟨cube_inj ?_, Or.inl hy⟩
      rw [hy] at h; linear_combination -h
    by_cases hc : 6 * u * x = 0
    · have hx : x = 0 := by
        rcases mul_eq_zero.mp hc with h6 | h6
        · exact absurd (by linarith : u = 0) hu
        · exact h6
      rw [hx] at h
      nlinarith [sq_nonneg y, pow_pos (pow_pos (lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 hu))) 3)]
    · exact absurd key (flt _ _ _ ha hb hc)
  · rintro ⟨rfl, rfl | rfl⟩ <;> ring

/-- `y^2 = x^3 - 432`: the integral points are `(12, ±36)`. -/
theorem points_432 (x y : ℤ) : y ^ 2 = x ^ 3 - 432 ↔ x = 12 ∧ (y = 36 ∨ y = -36) := by
  simpa using points 1 one_ne_zero x y

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 432 u^6` is a perfect square iff `n = 12 u^2`. -/
theorem isHit_iff (u : ℤ) (hu : u ≠ 0) (n : ℕ) :
    IsHit 2 ((n : ℤ) ^ 3 - 432 * u ^ 6) ↔ (n : ℤ) = 12 * u ^ 2 := by
  constructor
  · rintro ⟨m, hm⟩
    exact ((points u hu n m).mp hm.symm).1
  · intro h
    exact ⟨36 * u ^ 3, ((points u hu n _).mpr ⟨h, Or.inl rfl⟩).symm⟩

/-- The hit set of `n^3 - 432` is `{12}`. -/
theorem hitSet_432 (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 432) ↔ n = 12 := by
  have h := isHit_iff 1 one_ne_zero n
  norm_num at h
  rw [h]; omega

end PerfectPower.MordellFLT3
