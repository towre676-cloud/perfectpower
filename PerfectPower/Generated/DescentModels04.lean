import PerfectPower.Generated.DescentExclusions00
import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions05
import PerfectPower.Generated.DescentExclusions07
import PerfectPower.Generated.DescentExclusions11
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions13
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0100_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (13)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((13)/d)*v^4) :
    d ∈ ([1,13]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (13) (by decide) ([-13,-1,1,13]:List ℤ) ([13]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0113
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0752
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0100_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(13))) :
    ∃ d u v w : ℤ, d ∈ ([1,13]:List ℤ) ∧ Squarefree d ∧ d ∣ (13) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((13)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (13) x y hx hp
  exact ⟨d,u,v,w,model_0100_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0101_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (17)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((17)/d)*v^4) :
    d ∈ ([1,17]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (17) (by decide) ([-17,-1,1,17]:List ℤ) ([17]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0082
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0751
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0101_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(17))) :
    ∃ d u v w : ℤ, d ∈ ([1,17]:List ℤ) ∧ Squarefree d ∧ d ∣ (17) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((17)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (17) x y hx hp
  exact ⟨d,u,v,w,model_0101_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0102_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (21)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((21)/d)*v^4) :
    d ∈ ([1,3,7,21]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (21) (by decide) ([-21,-7,-3,-1,1,3,7,21]:List ℤ) ([3,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0069
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0196
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0379
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0750
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0102_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(21))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,7,21]:List ℤ) ∧ Squarefree d ∧ d ∣ (21) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((21)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (21) x y hx hp
  exact ⟨d,u,v,w,model_0102_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0103_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (25)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((25)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (25) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0304
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0749
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0103_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(25))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (25) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((25)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (25) x y hx hp
  exact ⟨d,u,v,w,model_0103_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0104_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (29)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((29)/d)*v^4) :
    d ∈ ([1,29]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (29) (by decide) ([-29,-1,1,29]:List ℤ) ([29]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0045
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0748
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0104_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(29))) :
    ∃ d u v w : ℤ, d ∈ ([1,29]:List ℤ) ∧ Squarefree d ∧ d ∣ (29) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((29)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (29) x y hx hp
  exact ⟨d,u,v,w,model_0104_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0105_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (33)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((33)/d)*v^4) :
    d ∈ ([1,33]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (33) (by decide) ([-33,-11,-3,-1,1,3,11,33]:List ℤ) ([3,11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0035
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0130
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0378
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0747
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1258
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1430
      u v w hu hcop hw)
  · simp

theorem model_0105_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(33))) :
    ∃ d u v w : ℤ, d ∈ ([1,33]:List ℤ) ∧ Squarefree d ∧ d ∣ (33) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((33)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (33) x y hx hp
  exact ⟨d,u,v,w,model_0105_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0106_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (37)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((37)/d)*v^4) :
    d ∈ ([1,37]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (37) (by decide) ([-37,-1,1,37]:List ℤ) ([37]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0027
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0746
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0106_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(37))) :
    ∃ d u v w : ℤ, d ∈ ([1,37]:List ℤ) ∧ Squarefree d ∧ d ∣ (37) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((37)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (37) x y hx hp
  exact ⟨d,u,v,w,model_0106_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0107_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (41)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((41)/d)*v^4) :
    d ∈ ([1,41]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (41) (by decide) ([-41,-1,1,41]:List ℤ) ([41]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0019
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0745
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0107_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(41))) :
    ∃ d u v w : ℤ, d ∈ ([1,41]:List ℤ) ∧ Squarefree d ∧ d ∣ (41) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((41)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (41) x y hx hp
  exact ⟨d,u,v,w,model_0107_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0108_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (45)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((45)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (45) (by decide) ([-15,-5,-3,-1,1,3,5,15]:List ℤ) ([3,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0090
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0303
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0377
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0744
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1259
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1455
      u v w hu hcop hw)

theorem model_0108_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(45))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (45) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((45)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (45) x y hx hp
  exact ⟨d,u,v,w,model_0108_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0109_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (49)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((49)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (49) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0195
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0743
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0109_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(49))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (49) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((49)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (49) x y hx hp
  exact ⟨d,u,v,w,model_0109_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0110_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (53)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((53)/d)*v^4) :
    d ∈ ([1,53]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (53) (by decide) ([-53,-1,1,53]:List ℤ) ([53]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0013
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0742
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0110_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(53))) :
    ∃ d u v w : ℤ, d ∈ ([1,53]:List ℤ) ∧ Squarefree d ∧ d ∣ (53) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((53)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (53) x y hx hp
  exact ⟨d,u,v,w,model_0110_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0111_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (57)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-6)*u^2*v^2+((57)/d)*v^4) :
    d ∈ ([1,3,19,57]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (57) (by decide) ([-57,-19,-3,-1,1,3,19,57]:List ℤ) ([3,19]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0009
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0076
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0376
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0741
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0111_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-6)*x+(57))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,19,57]:List ℤ) ∧ Squarefree d ∧ d ∣ (57) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-6)*u^2*v^2+((57)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-6) (57) x y hx hp
  exact ⟨d,u,v,w,model_0111_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0112_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-12)/d)*v^4) :
    d ∈ ([-3,-1,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0241
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0538
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1127
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1372
      u v w hu hcop hw)

theorem model_0112_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-12))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-12) x y hx hp
  exact ⟨d,u,v,w,model_0112_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0113_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-11)/d)*v^4) :
    d ∈ ([-11,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0788
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1431
      u v w hu hcop hw)

theorem model_0113_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-11))) :
    ∃ d u v w : ℤ, d ∈ ([-11,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-11) x y hx hp
  exact ⟨d,u,v,w,model_0113_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0114_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-10)/d)*v^4) :
    d ∈ ([-10,-5,-2,-1,1,2,5,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem model_0114_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-10))) :
    ∃ d u v w : ℤ, d ∈ ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (-10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-10) x y hx hp
  exact ⟨d,u,v,w,model_0114_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0115_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-9)/d)*v^4) :
    d ∈ ([-3,-1,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0115_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-9))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-9) x y hx hp
  exact ⟨d,u,v,w,model_0115_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0116_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-8)/d)*v^4) :
    d ∈ ([-2,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0787
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1128
      u v w hu hcop hw)

theorem model_0116_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-8))) :
    ∃ d u v w : ℤ, d ∈ ([-2,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-8) x y hx hp
  exact ⟨d,u,v,w,model_0116_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0117_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-7)/d)*v^4) :
    d ∈ ([-7,-1,1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0117_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-7))) :
    ∃ d u v w : ℤ, d ∈ ([-7,-1,1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (-7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-7) x y hx hp
  exact ⟨d,u,v,w,model_0117_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0118_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-6)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-6)/d)*v^4) :
    d ∈ ([-6,-3,-2,-1,1,2,3,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-6) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem model_0118_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-6))) :
    ∃ d u v w : ℤ, d ∈ ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (-6) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-6)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-6) x y hx hp
  exact ⟨d,u,v,w,model_0118_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0119_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-5)/d)*v^4) :
    d ∈ ([-5,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0786
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1334
      u v w hu hcop hw)

theorem model_0119_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-5))) :
    ∃ d u v w : ℤ, d ∈ ([-5,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-5) x y hx hp
  exact ⟨d,u,v,w,model_0119_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0120_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-4)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0537
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1129
      u v w hu hcop hw)

theorem model_0120_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-4))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-4) x y hx hp
  exact ⟨d,u,v,w,model_0120_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0121_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-3)/d)*v^4) :
    d ∈ ([-3,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0785
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1260
      u v w hu hcop hw)

theorem model_0121_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-3))) :
    ∃ d u v w : ℤ, d ∈ ([-3,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-3) x y hx hp
  exact ⟨d,u,v,w,model_0121_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0122_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-2)/d)*v^4) :
    d ∈ ([-2,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0784
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1130
      u v w hu hcop hw)

theorem model_0122_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-2))) :
    ∃ d u v w : ℤ, d ∈ ([-2,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-2) x y hx hp
  exact ⟨d,u,v,w,model_0122_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0123_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((-1)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · simp
  · simp

theorem model_0123_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(-1))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((-1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (-1) x y hx hp
  exact ⟨d,u,v,w,model_0123_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0124_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((1)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0783
      u v w hu hcop hw)
  · simp

theorem model_0124_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(1))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (1) x y hx hp
  exact ⟨d,u,v,w,model_0124_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels04
