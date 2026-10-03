import Mathlib.Tactic.Ring

/-! Integral multiplication attached to the standard binary cubic coefficients (a,b,c,d).
This is the normalized Delone–Faddeev table, not a claim that F(u,v) is a unit norm. -/
namespace PerfectPower.NativeCubic
abbrev Triple := ℤ × ℤ × ℤ

def mul (a b c d : ℤ) (x y : Triple) : Triple :=
  (x.1 * y.1 - a*c*x.2.1*y.2.1 - a*d*(x.2.1*y.2.2+x.2.2*y.2.1) - b*d*x.2.2*y.2.2,
   x.1*y.2.1+x.2.1*y.1+b*x.2.1*y.2.1+d*x.2.2*y.2.2,
   x.1*y.2.2+x.2.2*y.1-a*x.2.1*y.2.1-c*x.2.2*y.2.2)

theorem mul_comm (a b c d : ℤ) (x y : Triple) : mul a b c d x y = mul a b c d y x := by
  apply Prod.ext
  · simp only [mul]; ring
  · apply Prod.ext <;> simp only [mul] <;> ring

theorem mul_assoc (a b c d : ℤ) (x y z : Triple) :
    mul a b c d (mul a b c d x y) z = mul a b c d x (mul a b c d y z) := by
  apply Prod.ext
  · simp only [mul]; ring
  · apply Prod.ext <;> simp only [mul] <;> ring

theorem one_mul (a b c d : ℤ) (x : Triple) : mul a b c d (1,0,0) x = x := by
  apply Prod.ext
  · simp [mul]
  · apply Prod.ext <;> simp [mul]

end PerfectPower.NativeCubic
