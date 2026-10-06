import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Variable-width Gamma ratios at integer arguments: exact valuations of
N!/(N-W)!, and a reusable obstruction to every supplied perfect-power exponent.
This does not classify sums of factorials or arbitrary Gamma values. -/
namespace PerfectPower.FactorialWindow
open scoped BigOperators

/-- Product of the last min(W,N) positive integers through N. -/
def window (N W : ℕ) : ℕ := N.factorial / (N-W).factorial

theorem valuation (p N W : ℕ) [Fact p.Prime] :
    padicValNat p (window N W) =
      padicValNat p N.factorial - padicValNat p (N-W).factorial := by
  exact padicValNat.div_of_dvd (Nat.factorial_dvd_factorial (Nat.sub_le N W))

theorem legendre_window (p N W B : ℕ) [Fact p.Prime]
    (hN : Nat.log p N < B) (hW : Nat.log p (N-W) < B) :
    padicValNat p (window N W) =
      (∑ i ∈ Finset.Ico 1 B, N / p^i) - (∑ i ∈ Finset.Ico 1 B, (N-W) / p^i) := by
  rw [valuation, padicValNat_factorial hN, padicValNat_factorial hW]

/-- A valuation not divisible by the exponent is a complete local obstruction. -/
theorem not_power (p N W k : ℕ) [Fact p.Prime]
    (h : ¬ k ∣ padicValNat p (window N W)) :
    ¬ ∃ a : ℕ, a ≠ 0 ∧ window N W = a ^ k := by
  rintro ⟨a, ha, he⟩
  apply h
  rw [he, padicValNat.pow k ha]
  exact dvd_mul_right k _

end PerfectPower.FactorialWindow
