import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
noncomputable section
namespace PerfectPower.HypergeometricTransport

/-- A polynomial-coefficient recurrence yields its formal generating equation.
The constant boundary term is retained, including denominator-free transients. -/
theorem generating_equation {R : Type*} [Ring R] (P Q : ℤ → R) (a : ℕ → R)
    (recurrence : ∀ n : ℕ, Q n*a (n+1)=P n*a n) :
    PowerSeries.mk (fun n : ℕ => Q ((n : ℤ)-1)*a n) =
    PowerSeries.C R (Q (-1)*a 0) + PowerSeries.X *
      PowerSeries.mk (fun n : ℕ => P n*a n) := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_mk]
  | succ n =>
      simpa [PowerSeries.coeff_mk,PowerSeries.coeff_succ_X_mul] using recurrence n

end PerfectPower.HypergeometricTransport
