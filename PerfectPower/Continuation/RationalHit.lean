import PerfectPower.Continuation.PowerSplit
import PerfectPower.RadicalValuation

namespace PerfectPower.RationalYun
open Polynomial
noncomputable section

/-- Rational d-th power status, distinct from an integer hit predicate. -/
def RatPower (q : ℚ) (d : ℕ) : Prop := ∃ y : ℚ, q = y ^ d

/-- Strip a nonzero rational d-th-power multiplier. -/
theorem ratPower_mul_pow_iff (q h : ℚ) (d : ℕ) (hh : h ≠ 0) :
    RatPower (q * h ^ d) d ↔ RatPower q d := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y / h, ?_⟩
    rw [div_pow, ← hy]
    exact (mul_div_cancel_right₀ q (pow_ne_zero d hh)).symm
  · rintro ⟨y, rfl⟩
    exact ⟨y * h, (mul_pow y h d).symm⟩

/-- Integer factor stripping with every zero value retained. -/
theorem integer_factor_reduction {X : ℤ} {q h : ℚ} {d : ℕ} (hd : d ≠ 0)
    (hX : (X : ℚ) = q * h ^ d) :
    PerfectPower.IsHit d X ↔ X = 0 ∨ RatPower q d := by
  by_cases hh : h = 0
  · have hzero : X = 0 := by
      apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
      simpa [hh, zero_pow hd] using hX
    subst X
    simp only [true_or, iff_true]
    exact ⟨0, (zero_pow hd).symm⟩
  · constructor
    · intro hhit
      right
      obtain ⟨y, hy⟩ := (PerfectPower.isHit_iff_rat hd X).mp hhit
      exact (ratPower_mul_pow_iff q h d hh).mp ⟨y, hX.symm.trans hy⟩
    · rintro (rfl | hq)
      · exact ⟨0, (zero_pow hd).symm⟩
      · apply (PerfectPower.isHit_iff_rat hd X).mpr
        obtain ⟨y, hy⟩ := (ratPower_mul_pow_iff q h d hh).mpr hq
        exact ⟨y, hX.trans hy⟩

/-- Canonical structural extraction followed by the actual integer-hit definition. -/
theorem Decomposition.hit_reduction {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {d : ℕ} (hd : d ≠ 0) (n : ℤ) :
    PerfectPower.IsHit d (F.eval n) ↔ F.eval n = 0 ∨
      RatPower (Y.lead * (Y.remainderPart d).eval (n : ℚ)) d := by
  have heval := congrArg (Polynomial.eval (n : ℚ)) (Y.powerSplit d)
  simp only [eval_mul, eval_C, eval_pow, eval_map, eval₂_at_apply] at heval
  have hmap : F.eval₂ (Int.castRingHom ℚ) (n : ℚ) = ((F.eval n : ℤ) : ℚ) := by
    change F.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) n) =
      (Int.castRingHom ℚ) (F.eval n)
    exact Polynomial.eval₂_at_apply (Int.castRingHom ℚ) n
  rw [hmap] at heval
  exact integer_factor_reduction hd heval

/-- Even powers reduce to rational coefficient roots and square branches. -/
theorem rat_even_power_reduction (c w : ℚ) (e : ℕ) (hw : w ≠ 0) :
    RatPower (c * w ^ e) (2 * e) ↔
      ∃ γ : ℚ, γ ^ e = c ∧ RatPower (γ * w) 2 := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ^ 2 / w, ?_, y, ?_⟩
    · rw [div_pow, ← pow_mul, ← hy]
      exact mul_div_cancel_right₀ c (pow_ne_zero e hw)
    · exact div_mul_cancel₀ _ hw
  · rintro ⟨γ, hγ, y, hy⟩
    refine ⟨y, ?_⟩
    calc c * w ^ e = γ ^ e * w ^ e := by rw [hγ]
      _ = (γ * w) ^ e := (mul_pow γ w e).symm
      _ = (y ^ 2) ^ e := by rw [hy]
      _ = y ^ (2 * e) := (pow_mul y 2 e).symm

/-- The Pell evaluation reduction keeps the quadratic-zero branch explicitly. -/
theorem pell_factor_reduction {X : ℤ} {c w h : ℚ} {e : ℕ} (he : e ≠ 0)
    (hX : (X : ℚ) = c * w ^ e * h ^ (2 * e)) :
    PerfectPower.IsHit (2 * e) X ↔ X = 0 ∨
      ∃ γ : ℚ, γ ^ e = c ∧ RatPower (γ * w) 2 := by
  by_cases hw : w = 0
  · have hzero : X = 0 := by
      apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
      simpa [hw, zero_pow he] using hX
    subst X
    simp only [true_or, iff_true]
    exact ⟨0, (zero_pow (Nat.mul_ne_zero (by decide) he)).symm⟩
  · rw [integer_factor_reduction (Nat.mul_ne_zero (by decide) he) hX,
      rat_even_power_reduction c w e hw]

/-- Opposite square branches overlap only at zero. -/
theorem opposite_squares_iff_zero (q : ℚ) :
    RatPower q 2 ∧ RatPower (-q) 2 ↔ q = 0 := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    nlinarith [sq_nonneg a, sq_nonneg b]
  · rintro rfl
    exact ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

end
end PerfectPower.RationalYun
