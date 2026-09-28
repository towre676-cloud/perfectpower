import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.Tactic.ComputeDegree

open Polynomial UniqueFactorizationMonoid

namespace PerfectPower

/-! ### Davenport's bound: the function-field Hall inequality (unconditional)

Hall's conjecture asks for `|x^3 - y^2| ≫ x^(1/2 - ε)` over `ℤ`; it is open.  Over `k[X]` the
analogue is a theorem: Davenport (1965) proved `deg(f^3 - g^2) ≥ deg(f)/2 + 1`.  We derive it from
Mathlib's Mason–Stothers theorem `Polynomial.abc`, and show it is sharp. -/

variable {k : Type*} [Field k] [DecidableEq k]

/-- The radical of `f^3 g^2 h` has degree at most `deg f + deg g + deg h`. -/
lemma natDegree_radical_le_of_cube_sq {f g h : k[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) :
    (radical (f ^ 3 * g ^ 2 * h)).natDegree ≤ f.natDegree + g.natDegree + h.natDegree := by
  have hdvd : radical (f ^ 3 * g ^ 2 * h) ∣ f * g * h := by
    calc radical (f ^ 3 * g ^ 2 * h)
        ∣ radical (f ^ 3 * g ^ 2) * radical h := radical_mul_dvd
      _ ∣ radical (f ^ 3) * radical (g ^ 2) * radical h :=
          mul_dvd_mul_right radical_mul_dvd _
      _ = radical f * radical g * radical h := by
          rw [radical_pow f (by norm_num), radical_pow g (by norm_num)]
      _ ∣ f * g * h :=
          mul_dvd_mul (mul_dvd_mul radical_dvd_self radical_dvd_self) radical_dvd_self
  have hfgh : f * g * h ≠ 0 := mul_ne_zero (mul_ne_zero hf hg) hh
  calc (radical (f ^ 3 * g ^ 2 * h)).natDegree ≤ (f * g * h).natDegree :=
        natDegree_le_of_dvd hdvd hfgh
    _ = f.natDegree + g.natDegree + h.natDegree := by
        rw [natDegree_mul (mul_ne_zero hf hg) hh, natDegree_mul hf hg]

/-- **Davenport's bound.**  Over a field of characteristic zero, if `f, g` are coprime, `f` is
nonconstant and `f^3 ≠ g^2`, then `deg f + 2 ≤ 2 deg(f^3 - g^2)`, i.e.
`deg(f^3 - g^2) ≥ deg(f)/2 + 1`. -/
theorem davenport [CharZero k] {f g : k[X]} (hcop : IsCoprime f g) (hf : 0 < f.natDegree)
    (hne : f ^ 3 ≠ g ^ 2) : f.natDegree + 2 ≤ 2 * (f ^ 3 - g ^ 2).natDegree := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hu : IsUnit f := isCoprime_zero_right.mp hcop
    exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  have hh0 : f ^ 3 - g ^ 2 ≠ 0 := sub_ne_zero.mpr hne
  have hcop' : IsCoprime (f ^ 3) (-g ^ 2) := (hcop.pow).neg_right
  have key := Polynomial.abc (a := f ^ 3) (b := -g ^ 2) (c := -(f ^ 3 - g ^ 2))
    (pow_ne_zero 3 hf0) (neg_ne_zero.mpr (pow_ne_zero 2 hg0)) (neg_ne_zero.mpr hh0) hcop'
    (by ring)
  have habc : f ^ 3 * -g ^ 2 * -(f ^ 3 - g ^ 2) = f ^ 3 * g ^ 2 * (f ^ 3 - g ^ 2) := by ring
  rw [habc] at key
  have hrad := natDegree_radical_le_of_cube_sq hf0 hg0 hh0
  have hdf : (f ^ 3).natDegree = 3 * f.natDegree := by rw [natDegree_pow]
  have hdg : (g ^ 2).natDegree = 2 * g.natDegree := by rw [natDegree_pow]
  rcases key with ⟨ka, -, -⟩ | ⟨da, -, -⟩
  · rw [hdf] at ka
    rcases lt_trichotomy (2 * g.natDegree) (3 * f.natDegree) with hlt | heq | hgt
    · have : (f ^ 3 - g ^ 2).natDegree = 3 * f.natDegree := by
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hdf, hdg]; exact hlt), hdf]
      omega
    · omega
    · have : (f ^ 3 - g ^ 2).natDegree = 2 * g.natDegree := by
        rw [natDegree_sub_eq_right_of_natDegree_lt (by rw [hdf, hdg]; exact hgt), hdg]
      omega
  · -- derivative (f^3) = 3 f^2 f' = 0 forces f' = 0, so f is constant in characteristic zero
    rw [derivative_pow] at da
    have h3 : (C ((3 : ℕ) : k) : k[X]) ≠ 0 := by
      rw [Ne, C_eq_zero]; exact_mod_cast (by norm_num : (3 : ℕ) ≠ 0)
    have hd : derivative f = 0 := by
      rcases mul_eq_zero.mp da with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h3
        · exact absurd h' (pow_ne_zero _ hf0)
      · exact h
    have := natDegree_eq_zero_of_derivative_eq_zero hd
    omega

/-- Davenport's bound is sharp: `f = X^2 + 2`, `g = X^3 + 3X` give `f^3 - g^2 = 3X^2 + 8`, so
`deg f + 2 = 2 deg(f^3 - g^2)` (the smallest Birch–Chowla–Hall–Schinzel example). -/
theorem davenport_sharp :
    ((X ^ 2 + C 2 : ℚ[X]) ^ 3 - (X ^ 3 + C 3 * X) ^ 2).natDegree = 2 ∧
      (X ^ 2 + C 2 : ℚ[X]).natDegree + 2 = 2 * 2 := by
  have e : ((X ^ 2 + C 2 : ℚ[X]) ^ 3 - (X ^ 3 + C 3 * X) ^ 2) = C 3 * X ^ 2 + C 8 := by
    simp only [map_ofNat]; ring
  rw [e]
  constructor
  · compute_degree!
  · have : (X ^ 2 + C 2 : ℚ[X]).natDegree = 2 := by compute_degree!
    omega

end PerfectPower
