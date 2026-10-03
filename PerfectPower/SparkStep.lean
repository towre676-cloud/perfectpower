import Mathlib.Tactic

/-! Integer refinement of the accept branch in spark_pilot/selective/p.adb.
This proves the arithmetic invariant; bitwise refinement and GNAT VC discharge remain separate. -/
namespace PerfectPower.SparkStep

theorem accept_remainder (X r m : ℤ) :
    (X - r ^ 2 * (4*m)) - (4*r*m + m) = X - (2*r+1)^2*m := by ring

theorem accept_bounds (X r m : ℤ)
    (hupper : X < (r+1)^2*(4*m)) (haccept : 4*r*m+m ≤ X-r^2*(4*m)) :
    (2*r+1)^2*m ≤ X ∧ X < (2*r+2)^2*m := by
  constructor <;> nlinarith

theorem reject_bounds (X r m : ℤ)
    (hlower : r^2*(4*m) ≤ X) (hreject : X-r^2*(4*m) < 4*r*m+m) :
    (2*r)^2*m ≤ X ∧ X < (2*r+1)^2*m := by
  constructor <;> nlinarith

end PerfectPower.SparkStep
