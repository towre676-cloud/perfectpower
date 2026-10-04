import Mathlib.Tactic

namespace PerfectPower.QuadraticProjection

theorem discriminant_identity (a b c x : ℤ) :
    (2*a*x+b)^2-(b^2-4*a*c)=4*a*(a*x^2+b*x+c) := by ring

theorem forward (a b c x : ℤ) (h : a*x^2+b*x+c=0) :
    (2*a*x+b)^2=b^2-4*a*c := by
  have := discriminant_identity a b c x
  rw [h] at this
  nlinarith

theorem backward (a b c x w : ℤ) (ha : a ≠ 0)
    (hw : w^2=b^2-4*a*c) (hx : w=2*a*x+b) : a*x^2+b*x+c=0 := by
  have hi := discriminant_identity a b c x
  rw [← hx,hw] at hi
  have hz : 4*a*(a*x^2+b*x+c)=0 := by omega
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) ha)

/-- Discriminant reconstruction requires the divisibility filter. -/
theorem roots_iff (a b c : ℤ) (ha : a ≠ 0) :
    (∃ x : ℤ, a*x^2+b*x+c=0) ↔
      ∃ w : ℤ, w^2=b^2-4*a*c ∧ 2*a ∣ w-b := by
  constructor
  · rintro ⟨x,h⟩
    exact ⟨2*a*x+b,forward a b c x h,x,by ring⟩
  · rintro ⟨w,hw,x,hx⟩
    exact ⟨x,backward a b c x w ha hw (by omega)⟩

end PerfectPower.QuadraticProjection
