import PerfectPower.LocalQuarticObstruction

namespace PerfectPower.LocalQuarticAudit
open LocalQuarticObstruction

theorem obstruction_three : obstructed 3 2 1 2 := by decide +kernel

theorem no_point (x e z : ℤ)
    (h : (x : ZMod 3) ≠ 0 ∨ (e : ZMod 3) ≠ 0) :
    z^2 ≠ 2*x^4 + x^2*e^2 + 2*e^4 := by
  simpa using no_primitive_point 3 2 1 2 obstruction_three x e z h

-- The certificate is about primitive points; (0,0,0) is a point.
example : (0 : ℤ)^2 = 2*0^4 + 0^2*0^2 + 2*0^4 := by norm_num

example : ¬ obstructed 3 1 0 1 := by decide +kernel

#print axioms obstruction_three
#print axioms no_primitive_point
#print axioms no_point_of_not_dvd
#print axioms no_point
end PerfectPower.LocalQuarticAudit
