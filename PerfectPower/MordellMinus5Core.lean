import PerfectPower.ClassTwoCore

/-!
# Class number two, empty: `y^2 = x^3 - 5` has no integral points

`ℤ[√-5]` has class number 2.  An instance of the ideal-free template `PerfectPower.ClassTwo`
(box ratio `r/t = 3/2`, so `1 ≤ k ≤ 4`; table `table5`; halving mod 8) shows that
`y + √-5` would be a cube `(p + q√-5)^3`.  The `√-5`-coefficient then gives
`q (3p^2 - 5 q^2) = 1`, which has no integer solution.

(The same statement also follows from the elementary descent of `MordellDescent`; this file is the
class-group proof, as a second, independent route.)
-/

namespace PerfectPower.MordellMinus5

open PerfectPower.ClassTwo

theorem table5 : TableOK 5 4 8 3 := by
  unfold TableOK; decide +kernel

theorem halves5 : HalvesOK 5 := halvesOK_of_mod8 5 (by decide +kernel)

/-- **`y^2 = x^3 - 5` has no integral points.** -/
theorem no_points (x y : ℤ) : y ^ 2 ≠ x ^ 3 - 5 := by
  intro h
  obtain ⟨p, q, -, hq⟩ := cube_of_table 5 (by norm_num) 3 2 (by norm_num) (by norm_num) 4 8 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) table5 halves5 x y
    (by linarith)
  have hq' : q * (3 * p ^ 2 - 5 * q ^ 2) = 1 := by linear_combination -hq
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hq' with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · have h3 : p ^ 2 = 2 := by linarith
    have hp1 : p ≤ 1 := by nlinarith
    have hp2 : -1 ≤ p := by nlinarith
    interval_cases p <;> norm_num at h3
  · have h3 : 3 * p ^ 2 = 4 := by linarith
    have h4 := Int.mul_emod_right 3 (p ^ 2)
    rw [h3] at h4; norm_num at h4

end PerfectPower.MordellMinus5
