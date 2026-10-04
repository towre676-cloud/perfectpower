import Mathlib.NumberTheory.ArithmeticFunction
import PerfectPower.Generated.RepunitQuartic

/-! Divisor sums connected to the complete quartic solver.
The prime hypothesis is essential: geometric sums alone are not sigma(p^a)
when the base is composite. -/
namespace PerfectPower.DivisorSum

 theorem prime_fourth_value (p : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.sigma 1 (p^4) : ℤ) =
      SquareLeadingQuartic.value 1 1 1 1 1 (p : ℤ) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, SquareLeadingQuartic.value]
  ring

 theorem prime_fourth_square (p : ℕ) (hp : p.Prime) :
    (∃ y : ℤ, y^2 = (ArithmeticFunction.sigma 1 (p^4) : ℤ)) ↔ p = 3 := by
  rw [prime_fourth_value p hp]
  have hpos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have h := RepunitQuartic.positive (p : ℤ) hpos
  constructor
  · intro hy
    have h3 := h.mp hy
    exact_mod_cast h3
  · intro h3
    apply h.mpr
    exact_mod_cast h3

 theorem shifted_prime_fourth_complete (p : ℕ) (hp : p.Prime) (k y : ℤ) :
    y^2 = (ArithmeticFunction.sigma 1 (p^4) : ℤ) + k ↔
      ((p : ℤ), y) ∈ SquareLeadingQuartic.points 1 1 1 1 (1+k) := by
  have hid : (ArithmeticFunction.sigma 1 (p^4) : ℤ) + k =
      SquareLeadingQuartic.value 1 1 1 1 (1+k) (p : ℤ) := by
    rw [prime_fourth_value p hp]
    simp only [SquareLeadingQuartic.value]
    ring
  rw [hid]
  exact (SquareLeadingQuartic.complete 1 1 1 1 (1+k) (by norm_num)
    (by left; norm_num [SquareLeadingQuartic.rc, SquareLeadingQuartic.scale,
      SquareLeadingQuartic.qa, SquareLeadingQuartic.qb]) (p : ℤ) y)

 theorem coprime_product (m n : ℕ) (h : m.Coprime n) :
    ArithmeticFunction.sigma 1 (m*n) =
      ArithmeticFunction.sigma 1 m * ArithmeticFunction.sigma 1 n :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

 theorem common_factor_square (a b g u v : ℕ)
    (ha : a = g*u^2) (hb : b = g*v^2) : a*b = (g*u*v)^2 := by
  rw [ha,hb]
  ring

 theorem sigma_22 : ArithmeticFunction.sigma 1 22 = 6^2 := by
  rw [show (22 : ℕ) = 2*11 by norm_num, coprime_product 2 11 (by norm_num)]
  have h2 := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (show Nat.Prime 2 by norm_num)
  have h11 := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (show Nat.Prime 11 by norm_num)
  norm_num [Finset.sum_range_succ] at h2 h11
  rw [h2,h11]
  norm_num

end PerfectPower.DivisorSum
