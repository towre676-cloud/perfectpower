import PerfectPower.Generated.DescentExclusions00
import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions04
import PerfectPower.Generated.DescentExclusions06
import PerfectPower.Generated.DescentExclusions10
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels23
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0575_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (84)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(12)*u^2*v^2+((84)/d)*v^4) :
    d ∈ ([1,3,7,21]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (84) (by decide) ([-42,-21,-14,-7,-6,-3,-2,-1,1,2,3,6,7,14,21,42]:List ℤ) ([2,3,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0017
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0073
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0107
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0222
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0287
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0477
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0667
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1081
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1242
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1406
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1452
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1475
      u v w hu hcop hw)

theorem model_0575_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(12)*x+(84))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,7,21]:List ℤ) ∧ Squarefree d ∧ d ∣ (84) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(12)*u^2*v^2+((84)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (12) (84) x y hx hp
  exact ⟨d,u,v,w,model_0575_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels23
