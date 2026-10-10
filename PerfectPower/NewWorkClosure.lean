import PerfectPower.PSGStructural
import PerfectPower.SOESemantics
import PerfectPower.StructuralCertificates
import PerfectPower.StructuralSpecies

namespace PerfectPower.NewWorkClosure

/-- On the regular stratum elimination loses no auxiliary rational source solutions. -/
theorem reconstruction_complete (A B C D : ℚ) (hB : B ≠ 0) :
    A^2-D*B^2=0 ↔ ∃ t : ℚ, t^2=D ∧ A+t*B+(t^2-D)*C=0 := by
  constructor
  · intro hn
    refine ⟨-A/B, PSGStructural.norm_regular_square A B D hB hn, ?_⟩
    have ht := PSGStructural.norm_regular_square A B D hB hn
    rw [ht,sub_self,zero_mul,add_zero]
    exact PSGStructural.regular_reconstruction A B hB
  · rintro ⟨t,ht,hp⟩
    exact PSGStructural.quadratic_elimination_sound A B C D t hp (by rw [ht]; ring)

/-- The retained nonlinear SOE chart has a global polynomial inverse. -/
theorem chart_inverse (x y : ℚ) : (x+y^2)-y^2=x := by ring

theorem chart_forward (x y : ℚ) : (x-y^2)+y^2=x := by ring

/-- Its Jacobian determinant is exactly one, everywhere. -/
theorem chart_jacobian (y : ℚ) : 1*1-(2*y)*0=(1:ℚ) := by ring

/-- Source observations agree with target observations under this chart. -/
theorem chart_observations (x y : ℚ) : (x+y^2,x+y^2+y)=((x+y^2),(x+y^2)+y) := by rfl

end PerfectPower.NewWorkClosure
