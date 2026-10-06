import Mathlib.Tactic

/-! Conditional integer recognition from rational enclosures.
The existence of an integral object and its analytic enclosure are hypotheses. -/
namespace PerfectPower.IntegralRecognition

/-- Two integral candidates within a strict half-unit radius must coincide. -/
theorem integer_unique (c ε : ℚ) (x y : ℤ) (hε : ε < 1/2)
    (hx : |c - (x : ℚ)| ≤ ε) (hy : |c - (y : ℚ)| ≤ ε) : x = y := by
  have ht := abs_sub_le (x : ℚ) c (y : ℚ)
  rw [abs_sub_comm (x : ℚ) c] at ht
  have hq : |((x-y : ℤ) : ℚ)| < 1 := by
    push_cast
    linarith
  have hi : |x-y| < (1 : ℤ) := by
    exact_mod_cast hq
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hi)

/-- Entry enclosures imply uniqueness of a whole integral matrix. No finiteness
or symplectic premise is required for uniqueness. -/
theorem matrix_unique {m n : Type*} (C : m → n → ℚ) (ε : ℚ)
    (X Y : m → n → ℤ) (hε : ε < 1/2)
    (hX : ∀ i j, |C i j - (X i j : ℚ)| ≤ ε)
    (hY : ∀ i j, |C i j - (Y i j : ℚ)| ≤ ε) : X = Y := by
  funext i j
  exact integer_unique (C i j) ε (X i j) (Y i j) hε (hX i j) (hY i j)

end PerfectPower.IntegralRecognition
