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

/-! ### Function-field Pillai (unconditional)

Over `ℤ`, Pillai's conjecture (`|x^a - y^b| → ∞`) is open; `ABC.lean` derives it from abc.  Over
`k[X]` Mason–Stothers makes it a theorem, with an explicit degree bound. -/

/-- The radical of `f^a g^b h` has degree at most `deg f + deg g + deg h`. -/
lemma natDegree_radical_pow_pow_le {f g h : k[X]} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hf : f ≠ 0)
    (hg : g ≠ 0) (hh : h ≠ 0) :
    (radical (f ^ a * g ^ b * h)).natDegree ≤ f.natDegree + g.natDegree + h.natDegree := by
  have hdvd : radical (f ^ a * g ^ b * h) ∣ f * g * h := by
    calc radical (f ^ a * g ^ b * h)
        ∣ radical (f ^ a * g ^ b) * radical h := radical_mul_dvd
      _ ∣ radical (f ^ a) * radical (g ^ b) * radical h :=
          mul_dvd_mul_right radical_mul_dvd _
      _ = radical f * radical g * radical h := by
          rw [radical_pow f ha, radical_pow g hb]
      _ ∣ f * g * h :=
          mul_dvd_mul (mul_dvd_mul radical_dvd_self radical_dvd_self) radical_dvd_self
  have hfgh : f * g * h ≠ 0 := mul_ne_zero (mul_ne_zero hf hg) hh
  calc (radical (f ^ a * g ^ b * h)).natDegree ≤ (f * g * h).natDegree :=
        natDegree_le_of_dvd hdvd hfgh
    _ = f.natDegree + g.natDegree + h.natDegree := by
        rw [natDegree_mul (mul_ne_zero hf hg) hh, natDegree_mul hf hg]

/-- **Function-field Pillai.**  Over a field of characteristic zero, let `f, g` be coprime with `f`
nonconstant, `a, b ≥ 1` and `f^a ≠ g^b`.  Then with `h = f^a - g^b`,
`a deg f + 1 ≤ deg f + deg g + deg h` and `b deg g + 1 ≤ deg f + deg g + deg h`.  In particular,
when `a deg f = b deg g = n`, `deg h ≥ n (1 - 1/a - 1/b) + 1` (see `pillai_polynomial_balanced`). -/
theorem pillai_polynomial [CharZero k] {f g : k[X]} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime f g) (hf : 0 < f.natDegree) (hne : f ^ a ≠ g ^ b) :
    a * f.natDegree + 1 ≤ f.natDegree + g.natDegree + (f ^ a - g ^ b).natDegree ∧
      b * g.natDegree + 1 ≤ f.natDegree + g.natDegree + (f ^ a - g ^ b).natDegree := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hu : IsUnit f := isCoprime_zero_right.mp hcop
    exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  have hh0 : f ^ a - g ^ b ≠ 0 := sub_ne_zero.mpr hne
  have hcop' : IsCoprime (f ^ a) (-g ^ b) := (hcop.pow).neg_right
  have key := Polynomial.abc (a := f ^ a) (b := -g ^ b) (c := -(f ^ a - g ^ b))
    (pow_ne_zero a hf0) (neg_ne_zero.mpr (pow_ne_zero b hg0)) (neg_ne_zero.mpr hh0) hcop'
    (by ring)
  have habc : f ^ a * -g ^ b * -(f ^ a - g ^ b) = f ^ a * g ^ b * (f ^ a - g ^ b) := by ring
  rw [habc] at key
  have hrad := natDegree_radical_pow_pow_le ha hb hf0 hg0 hh0
  rcases key with ⟨ka, kb, -⟩ | ⟨da, -, -⟩
  · rw [natDegree_pow] at ka
    rw [natDegree_neg, natDegree_pow] at kb
    exact ⟨by omega, by omega⟩
  · rw [derivative_pow] at da
    have hC : (C ((a : ℕ) : k) : k[X]) ≠ 0 := by
      rw [Ne, C_eq_zero]; exact_mod_cast ha
    have hd : derivative f = 0 := by
      rcases mul_eq_zero.mp da with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hC
        · exact absurd h' (pow_ne_zero _ hf0)
      · exact h
    have := natDegree_eq_zero_of_derivative_eq_zero hd
    omega

/-- **Balanced form.**  If `a, b ≥ 2` and `a deg f = b deg g = n`, then
`a b deg(f^a - g^b) ≥ n (a b - a - b) + a b`, i.e. `deg(f^a - g^b) ≥ n (1 - 1/a - 1/b) + 1`.
For `(a, b) = (3, 2)` this is Davenport's bound.  (With `a = 1` the difference can be constant:
`f = g^b + 1`.) -/
theorem pillai_polynomial_balanced [CharZero k] {f g : k[X]} {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcop : IsCoprime f g) (hf : 0 < f.natDegree) (hne : f ^ a ≠ g ^ b)
    (hbal : a * f.natDegree = b * g.natDegree) :
    a * f.natDegree * (a * b - a - b) + a * b ≤ a * b * (f ^ a - g ^ b).natDegree := by
  obtain ⟨h1, -⟩ := pillai_polynomial (by omega) (by omega) hcop hf hne
  set h := (f ^ a - g ^ b).natDegree
  set n := a * f.natDegree
  have e1 : a * b * f.natDegree = b * n := by simp only [n]; ring
  have e2 : a * b * g.natDegree = a * n := by rw [hbal]; ring
  have key : a * b * (n + 1) ≤ a * b * (f.natDegree + g.natDegree + h) :=
    Nat.mul_le_mul_left _ h1
  have hab : a + b ≤ a * b := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m, a * b = a + b + m := ⟨a * b - (a + b), by omega⟩
  have hm' : a * b - a - b = m := by omega
  rw [hm']
  have : a * b * (n + 1) = n * m + (a + b) * n + a * b := by rw [mul_add, hm]; ring
  nlinarith

/-- The degree bound is not vacuous for `(a, b) = (2, 3)` (Davenport) and is sharp there:
`davenport_sharp`.  For `(a, b) = (2, 2)` it gives only `deg h ≥ 1`, which is sharp:
`(X + 1)^2 - X^2 = 2X + 1`. -/
theorem pillai_polynomial_sq_sharp :
    ((X + C 1 : ℚ[X]) ^ 2 - X ^ 2).natDegree = 1 := by
  have e : ((X + C 1 : ℚ[X]) ^ 2 - X ^ 2) = C 2 * X + C 1 := by
    simp only [map_ofNat, map_one]; ring
  rw [e]; compute_degree!

end PerfectPower
