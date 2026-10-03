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

/-- A nonnegative root of a signed 31-bit input fits below 46341. -/
theorem final_range (X r : ℤ) (hX : X ≤ 2147483647) (hr : 0 ≤ r)
    (hroot : r^2 ≤ X) : 0 ≤ r ∧ r ≤ 46340 := by
  refine ⟨hr,?_⟩
  by_contra h
  have hlarge : 46341 ≤ r := by omega
  nlinarith [sq_nonneg (r-46341)]

end PerfectPower.SparkStep
