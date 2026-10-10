import PerfectPower.TwoDescentBridges

namespace PerfectPower.IsogenyCoordinates

/-- The actual rational coordinate map lands on the 2-isogenous model. -/
theorem isogeny_lands_on_curve (a b x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+a*x+b)) :
    (y*(1-b/x^2))^2 = (x+a+b/x)*
      ((x+a+b/x)^2-2*a*(x+a+b/x)+(a^2-4*b)) := by
  rw [mul_pow,hp]
  field_simp [hx]
  ring

/-- The normalized dual coordinate equals the doubling x-coordinate. -/
theorem dual_composition_x (a b x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hp : y^2=x*(x^2+a*x+b)) :
    ((x+a+b/x)-2*a+(a^2-4*b)/(x+a+b/x))/4 = (x^2-b)^2/(4*y^2) := by
  have hs : x*(x^2+a*x+b) ≠ 0 := by rw [← hp]; exact pow_ne_zero 2 hy
  have hq : x^2+a*x+b ≠ 0 := (mul_ne_zero_iff.mp hs).2
  have hX : x+a+b/x=(x^2+a*x+b)/x := by field_simp [hx]; ring
  rw [hX,hp]
  field_simp [hx,hq]
  ring

end PerfectPower.IsogenyCoordinates
