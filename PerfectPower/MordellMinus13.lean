import PerfectPower.ClassTwo

/-!
# Class number two: the integral points of `y^2 = x^3 - 13`

`y^2 = x^3 - 13` has rank one and its integral points are `(17, ± 70)`.  `ℤ[√-13]` has class
number 2, so unique factorisation fails; the classical proof (formalised in Lean 3 by
Baanen–Best–Coppola–Dahmen) shows that the ideal `I` with `I^3 = (y + √-13)` is principal because
the class number is prime to 3.

This file is an instance of the ideal-free template `PerfectPower.ClassTwo`: the lattice of `I`,
Thue's pigeonhole bound with box ratio `r/t = 11/3` (so `1 ≤ k ≤ 7`), and the kernel-checked
table `table13` (`p^2 + 13 q^2 = k^3`, `k ≤ 7`, only for `(k, p) = (1, ± 1), (4, ± 8)`; the norms
`8, 27, 125, 216, 343` of the non-principal class are not represented) give `y + √-13 =
(p + q√-13)^3`.  The `√-13`-coefficient gives `q (3p^2 - 13 q^2) = 1`, so `y = ∓ 70`, `x = 17`.
-/

namespace PerfectPower.MordellMinus13

open PerfectPower.ClassTwo

/-- **The class-number-two table** for `D = 13`. -/
theorem table13 : TableOK 13 7 18 5 := by
  unfold TableOK; decide +kernel

theorem halves13 : HalvesOK 13 := halvesOK_of_mod8 13 (by decide +kernel)

/-- The Thue step. -/
lemma thue (y p q : ℤ) (hy : y = p ^ 3 - 3 * 13 * p * q ^ 2)
    (h1 : 1 = 3 * p ^ 2 * q - 13 * q ^ 3) : y = 70 ∨ y = -70 := by
  have hq : q * (3 * p ^ 2 - 13 * q ^ 2) = 1 := by linear_combination -h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hq with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · exfalso
    have h3 : 3 * p ^ 2 = 14 := by linarith
    have h4 := Int.mul_emod_right 3 (p ^ 2)
    rw [h3] at h4; norm_num at h4
  · have hp2 : p ^ 2 = 4 := by nlinarith
    have : (p - 2) * (p + 2) = 0 := by linear_combination hp2
    rcases mul_eq_zero.mp this with hp | hp
    · have : p = 2 := by linarith
      subst this; right; linarith
    · have : p = -2 := by linarith
      subst this; left; linarith

/-- **The integral points of `y^2 = x^3 - 13` are `(17, ± 70)`.** -/
theorem points (x y : ℤ) : y ^ 2 = x ^ 3 - 13 ↔ x = 17 ∧ (y = 70 ∨ y = -70) := by
  constructor
  swap
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num
  intro h
  obtain ⟨p, q, hp, hq⟩ := cube_of_table 13 (by norm_num) 11 3 (by norm_num) (by norm_num) 7 18 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) table13 halves13 x y
    (by linarith)
  have hy := thue y p q hp hq
  refine ⟨cube_inj ?_, hy⟩
  rcases hy with rfl | rfl <;> linarith

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 13` is a perfect square iff `n = 17`. -/
theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 13) ↔ n = 17 := by
  constructor
  · rintro ⟨m, hm⟩
    have := ((points n m).mp hm.symm).1
    exact_mod_cast this
  · rintro rfl
    exact ⟨70, by norm_num⟩

end PerfectPower.MordellMinus13
