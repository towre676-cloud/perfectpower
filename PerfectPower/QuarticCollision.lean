import Mathlib.Tactic

/-! Complete collision decomposition for even quartics: the reflection branch
and a finite sum-of-squares branch. This does not cover arbitrary quartics. -/
namespace PerfectPower.QuarticCollision

/-- An integer even quartic in its original parameter. -/
def value (a b c x : ℤ) : ℤ := a*x^4+b*x^2+c

theorem collision_identity (a b c x y : ℤ) :
    value a b c x-value a b c y = (x^2-y^2)*(a*(x^2+y^2)+b) := by
  unfold value
  ring

/-- All collisions decompose into diagonal, reflection and circle branches. -/
theorem collision_iff (a b c x y : ℤ) :
    value a b c x = value a b c y ↔
      x=y ∨ x= -y ∨ a*(x^2+y^2)+b=0 := by
  rw [← sub_eq_zero, collision_identity, mul_eq_zero, sub_eq_zero,
    sq_eq_sq_iff_eq_or_eq_neg, or_assoc]

theorem circle_bounds (a b x y : ℤ) (ha : a ≠ 0) (h : a*(x^2+y^2)+b=0) :
    0 ≤ (-b)/a ∧ x^2 ≤ (-b)/a ∧ y^2 ≤ (-b)/a := by
  have he : -b=a*(x^2+y^2) := by nlinarith
  rw [he, Int.mul_ediv_cancel_left _ ha]
  constructor
  · positivity
  · constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]

end PerfectPower.QuarticCollision
