import Mathlib.Tactic
namespace PerfectPower.CoveringMaps

def curve (A B x y : ℚ) : Prop := y^2=x^3+A*x^2+B*x

theorem covering (A B d u w v : ℚ) (hd : d ≠ 0) (hv : v ≠ 0)
    (h : w^2=d*u^4+A*u^2*v^2+(B/d)*v^4) :
    curve A B (d*u^2/v^2) (d*u*w/v^3) := by
  unfold curve
  field_simp at h ⊢
  linear_combination d*u^2*v^12*h

theorem isogeny (A B x y : ℚ) (hx : x ≠ 0) (h : curve A B x y) :
    curve (-2*A) (A^2-4*B) (x+A+B/x) (y*(1-B/x^2)) := by
  unfold curve at h ⊢
  field_simp
  linear_combination (x^2-B)^2*x^6*h
end PerfectPower.CoveringMaps
