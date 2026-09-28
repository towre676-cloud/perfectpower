import PerfectPower.Certificates

namespace PerfectPower

/-! ### Binomial coefficients that are perfect powers, via integral points on elliptic curves

`C(n,2) = m^3` and `C(n,3) = m^2` reduce to integral points on the elliptic curves
`Y^2 = X^3 + 1` (with `X = 2m`, `Y = 2n - 1`) and `Y^2 = X^3 - 36X` (with `X = 6(n-1)`,
`Y = 36m`).  Lean proves the reductions, the congruence filtering and every surviving point.
The **completeness of the integral-point list** of each curve is an explicit hypothesis
(`IntegralPointsCubePlusOne`, `IntegralPointsCongruent6`), certified outside Lean by Sage
(`receipts/binomial_curves.json`: rank proved by mwrank, saturated generators,
elliptic-logarithm sieving).  It is *not* proved in Lean. -/

/-- `2 · C(n, 2) = n (n - 1)` over `ℤ`. -/
lemma two_mul_choose_two (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; linarith

/-- `6 · C(n, 3) = n (n - 1) (n - 2)` over `ℤ`. -/
lemma six_mul_choose_three (n : ℕ) : 6 * (n.choose 3 : ℤ) = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ]; push_cast
    have h2 := two_mul_choose_two n
    linear_combination ih + 3 * h2

/-- The integral points of `Y^2 = X^3 + 1` have `X ∈ {-1, 0, 2}` (Euler; rank 0, torsion `ℤ/6`).
Certified externally, see the module docstring. -/
def IntegralPointsCubePlusOne : Prop :=
  ∀ X Y : ℤ, Y ^ 2 = X ^ 3 + 1 → X = -1 ∨ X = 0 ∨ X = 2

/-- The integral points of `Y^2 = X^3 - 36X` have `X ∈ {-6, -3, -2, 0, 6, 12, 18, 294}`
(rank 1).  Certified externally, see the module docstring. -/
def IntegralPointsCongruent6 : Prop :=
  ∀ X Y : ℤ, Y ^ 2 = X ^ 3 - 36 * X →
    X = -6 ∨ X = -3 ∨ X = -2 ∨ X = 0 ∨ X = 6 ∨ X = 12 ∨ X = 18 ∨ X = 294

/-- The listed points do lie on the curves (so the hypotheses are the *complete* lists). -/
theorem binomial_curve_points_valid :
    ([(-1, 0), (0, 1), (2, 3)] : List (ℤ × ℤ)).all (fun p => p.2 ^ 2 == p.1 ^ 3 + 1) = true ∧
    ([(-6, 0), (-3, 9), (-2, 8), (0, 0), (6, 0), (12, 36), (18, 72), (294, 5040)] : List (ℤ × ℤ)).all
      (fun p => p.2 ^ 2 == p.1 ^ 3 - 36 * p.1) = true := by decide

/-- Reduction: `C(n,2)` is a cube iff `(2n - 1)^2 = X^3 + 1` with `X = 2m` even. -/
theorem choose_two_cube_iff (n : ℕ) :
    IsHit 3 (n.choose 2 : ℤ) ↔ ∃ m : ℤ, (2 * (n : ℤ) - 1) ^ 2 = (2 * m) ^ 3 + 1 := by
  have h := two_mul_choose_two n
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by nlinarith⟩
  · rintro ⟨m, hm⟩; exact ⟨m, by nlinarith⟩

/-- **`C(n,2)` is a perfect cube only for `n = 1, 2`** (values `0, 1`), for `n ≥ 1`, given the
integral points of `Y^2 = X^3 + 1`. -/
theorem choose_two_cube_hits (hpts : IntegralPointsCubePlusOne) (n : ℕ) (hn : 1 ≤ n) :
    IsHit 3 (n.choose 2 : ℤ) ↔ n = 1 ∨ n = 2 := by
  rw [choose_two_cube_iff]
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  constructor
  · rintro ⟨m, hm⟩
    rcases hpts (2 * m) (2 * n - 1) hm with h | h | h
    · omega
    · have hm0 : m = 0 := by omega
      subst hm0
      have : (2 * (n : ℤ) - 1) = 1 := by nlinarith
      left; omega
    · have hm1 : m = 1 := by omega
      subst hm1
      have : (2 * (n : ℤ) - 1) = 3 := by nlinarith
      right; omega
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

/-- Reduction: `C(n,3)` is a square iff `Y^2 = X^3 - 36X` with `X = 6(n-1)`, `Y = 36m`. -/
theorem choose_three_square_iff (n : ℕ) :
    IsHit 2 (n.choose 3 : ℤ) ↔
      ∃ m : ℤ, (36 * m) ^ 2 = (6 * ((n : ℤ) - 1)) ^ 3 - 36 * (6 * ((n : ℤ) - 1)) := by
  have h := six_mul_choose_three n
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by nlinarith⟩
  · rintro ⟨m, hm⟩; exact ⟨m, by nlinarith⟩

/-- **`C(n,3)` is a perfect square only for `n ∈ {1, 2, 3, 4, 50}`** (values `0, 0, 1, 4, 19600`),
for `n ≥ 1`, given the integral points of `Y^2 = X^3 - 36X`. -/
theorem choose_three_square_hits (hpts : IntegralPointsCongruent6) (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (n.choose 3 : ℤ) ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 50 := by
  rw [choose_three_square_iff]
  constructor
  · rintro ⟨m, hm⟩
    rcases hpts _ _ hm with h | h | h | h | h | h | h | h <;> omega
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨140, by norm_num⟩

end PerfectPower
