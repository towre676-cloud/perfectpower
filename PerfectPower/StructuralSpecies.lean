import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic

namespace PerfectPower.StructuralSpecies

/-- Occupations reconstruct exponents by finite suffix sums. -/
def reconstruct : List ℕ → List ℕ
  | [] => []
  | c :: cs => (c+cs.sum) :: reconstruct cs

def occupations : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: cs => (a-b) :: occupations (b :: cs)

theorem occupations_reconstruct (cs : List ℕ) : occupations (reconstruct cs)=cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => simp [reconstruct,occupations]
    | cons d ds =>
      simp only [reconstruct,List.sum_cons,occupations] at *
      rw [ih]
      congr 1
      omega

/-- Exponent scaling commutes with monomial evaluation. -/
theorem monomial_power {R : Type*} [CommMonoid R] (d : ℕ) (xs : List (R × ℕ)) :
    ((xs.map fun q => q.1^q.2).prod)^d =
      (xs.map fun q => q.1^(q.2*d)).prod := by
  induction xs with
  | nil => simp
  | cons q xs ih => simp [mul_pow,ih,pow_mul]

/-- Divisors that are d-th powers have exactly floor(e/d)+1 possible exponents. -/
theorem bounded_power_exponent (e d j : ℕ) (hd : 0 < d) :
    d*j ≤ e ↔ j < e/d+1 := by
  rw [Nat.mul_comm,← Nat.le_div_iff_mul_le hd]
  omega

end PerfectPower.StructuralSpecies
