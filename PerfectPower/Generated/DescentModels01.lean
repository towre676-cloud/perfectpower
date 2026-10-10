import PerfectPower.Generated.DescentExclusions00
import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions05
import PerfectPower.Generated.DescentExclusions07
import PerfectPower.Generated.DescentExclusions11
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0025_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-15)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((-15)/d)*v^4) :
    d ∈ ([-15,-5,-3,-1,1,3,5,15]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-15) (by decide) ([-15,-5,-3,-1,1,3,5,15]:List ℤ) ([3,5]:List ℤ)
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

theorem model_0025_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(-15))) :
    ∃ d u v w : ℤ, d ∈ ([-15,-5,-3,-1,1,3,5,15]:List ℤ) ∧ Squarefree d ∧ d ∣ (-15) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((-15)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (-15) x y hx hp
  exact ⟨d,u,v,w,model_0025_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0026_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((-11)/d)*v^4) :
    d ∈ ([-11,-1,1,11]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0026_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(-11))) :
    ∃ d u v w : ℤ, d ∈ ([-11,-1,1,11]:List ℤ) ∧ Squarefree d ∧ d ∣ (-11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((-11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (-11) x y hx hp
  exact ⟨d,u,v,w,model_0026_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0027_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((-7)/d)*v^4) :
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

theorem model_0027_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(-7))) :
    ∃ d u v w : ℤ, d ∈ ([-7,-1,1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (-7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((-7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (-7) x y hx hp
  exact ⟨d,u,v,w,model_0027_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0028_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((-3)/d)*v^4) :
    d ∈ ([-3,-1,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0028_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(-3))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((-3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (-3) x y hx hp
  exact ⟨d,u,v,w,model_0028_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0029_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((1)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0720
      u v w hu hcop hw)
  · simp

theorem model_0029_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(1))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (1) x y hx hp
  exact ⟨d,u,v,w,model_0029_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0030_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((5)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0299
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0719
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0030_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(5))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (5) x y hx hp
  exact ⟨d,u,v,w,model_0030_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0031_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((9)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0369
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0718
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1247
      u v w hu hcop hw)

theorem model_0031_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(9))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (9) x y hx hp
  exact ⟨d,u,v,w,model_0031_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0032_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (13)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((13)/d)*v^4) :
    d ∈ ([1,13]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (13) (by decide) ([-13,-1,1,13]:List ℤ) ([13]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0111
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0717
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0032_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(13))) :
    ∃ d u v w : ℤ, d ∈ ([1,13]:List ℤ) ∧ Squarefree d ∧ d ∣ (13) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((13)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (13) x y hx hp
  exact ⟨d,u,v,w,model_0032_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0033_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (17)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((17)/d)*v^4) :
    d ∈ ([1,17]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (17) (by decide) ([-17,-1,1,17]:List ℤ) ([17]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0081
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0716
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0033_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(17))) :
    ∃ d u v w : ℤ, d ∈ ([1,17]:List ℤ) ∧ Squarefree d ∧ d ∣ (17) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((17)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (17) x y hx hp
  exact ⟨d,u,v,w,model_0033_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0034_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (21)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((21)/d)*v^4) :
    d ∈ ([1,3,7,21]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (21) (by decide) ([-21,-7,-3,-1,1,3,7,21]:List ℤ) ([3,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0068
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0192
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0368
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0715
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0034_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(21))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,7,21]:List ℤ) ∧ Squarefree d ∧ d ∣ (21) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((21)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (21) x y hx hp
  exact ⟨d,u,v,w,model_0034_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0035_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (29)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((29)/d)*v^4) :
    d ∈ ([1,29]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (29) (by decide) ([-29,-1,1,29]:List ℤ) ([29]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0044
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0714
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0035_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(29))) :
    ∃ d u v w : ℤ, d ∈ ([1,29]:List ℤ) ∧ Squarefree d ∧ d ∣ (29) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((29)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (29) x y hx hp
  exact ⟨d,u,v,w,model_0035_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0036_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (33)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((33)/d)*v^4) :
    d ∈ ([1,3,11,33]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (33) (by decide) ([-33,-11,-3,-1,1,3,11,33]:List ℤ) ([3,11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0034
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0128
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0367
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0713
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0036_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(33))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,11,33]:List ℤ) ∧ Squarefree d ∧ d ∣ (33) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((33)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (33) x y hx hp
  exact ⟨d,u,v,w,model_0036_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0037_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (37)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((37)/d)*v^4) :
    d ∈ ([1,37]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (37) (by decide) ([-37,-1,1,37]:List ℤ) ([37]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0026
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0712
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0037_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(37))) :
    ∃ d u v w : ℤ, d ∈ ([1,37]:List ℤ) ∧ Squarefree d ∧ d ∣ (37) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((37)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (37) x y hx hp
  exact ⟨d,u,v,w,model_0037_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0038_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (41)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((41)/d)*v^4) :
    d ∈ ([1,41]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (41) (by decide) ([-41,-1,1,41]:List ℤ) ([41]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0018
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0711
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0038_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(41))) :
    ∃ d u v w : ℤ, d ∈ ([1,41]:List ℤ) ∧ Squarefree d ∧ d ∣ (41) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((41)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (41) x y hx hp
  exact ⟨d,u,v,w,model_0038_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0039_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (45)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((45)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (45) (by decide) ([-15,-5,-3,-1,1,3,5,15]:List ℤ) ([3,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0088
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0298
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0366
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0710
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1248
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1453
      u v w hu hcop hw)

theorem model_0039_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(45))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (45) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((45)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (45) x y hx hp
  exact ⟨d,u,v,w,model_0039_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0040_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (49)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((49)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (49) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0191
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0709
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0040_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(49))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (49) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((49)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (49) x y hx hp
  exact ⟨d,u,v,w,model_0040_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0041_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (53)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((53)/d)*v^4) :
    d ∈ ([1,53]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (53) (by decide) ([-53,-1,1,53]:List ℤ) ([53]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0012
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0708
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0041_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(53))) :
    ∃ d u v w : ℤ, d ∈ ([1,53]:List ℤ) ∧ Squarefree d ∧ d ∣ (53) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((53)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (53) x y hx hp
  exact ⟨d,u,v,w,model_0041_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0042_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (57)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((57)/d)*v^4) :
    d ∈ ([1,3,19,57]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (57) (by decide) ([-57,-19,-3,-1,1,3,19,57]:List ℤ) ([3,19]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0008
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0075
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0365
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0707
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0042_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(57))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,19,57]:List ℤ) ∧ Squarefree d ∧ d ∣ (57) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((57)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (57) x y hx hp
  exact ⟨d,u,v,w,model_0042_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0043_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (61)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((61)/d)*v^4) :
    d ∈ ([1,61]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (61) (by decide) ([-61,-1,1,61]:List ℤ) ([61]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0006
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0706
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0043_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(61))) :
    ∃ d u v w : ℤ, d ∈ ([1,61]:List ℤ) ∧ Squarefree d ∧ d ∣ (61) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((61)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (61) x y hx hp
  exact ⟨d,u,v,w,model_0043_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0044_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (65)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((65)/d)*v^4) :
    d ∈ ([1,5,13,65]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (65) (by decide) ([-65,-13,-5,-1,1,5,13,65]:List ℤ) ([5,13]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0004
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0110
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0297
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0705
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0044_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(65))) :
    ∃ d u v w : ℤ, d ∈ ([1,5,13,65]:List ℤ) ∧ Squarefree d ∧ d ∣ (65) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((65)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (65) x y hx hp
  exact ⟨d,u,v,w,model_0044_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0045_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (69)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((69)/d)*v^4) :
    d ∈ ([1,3,23,69]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (69) (by decide) ([-69,-23,-3,-1,1,3,23,69]:List ℤ) ([3,23]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0002
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0056
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0364
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0704
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0045_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(69))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,23,69]:List ℤ) ∧ Squarefree d ∧ d ∣ (69) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((69)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (69) x y hx hp
  exact ⟨d,u,v,w,model_0045_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0046_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (73)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((73)/d)*v^4) :
    d ∈ ([1,73]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (73) (by decide) ([-73,-1,1,73]:List ℤ) ([73]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0000
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0703
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0046_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(73))) :
    ∃ d u v w : ℤ, d ∈ ([1,73]:List ℤ) ∧ Squarefree d ∧ d ∣ (73) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((73)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (73) x y hx hp
  exact ⟨d,u,v,w,model_0046_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0047_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-32)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-8)*u^2*v^2+((-32)/d)*v^4) :
    d ∈ ([-2,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-32) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0740
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1107
      u v w hu hcop hw)

theorem model_0047_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-8)*x+(-32))) :
    ∃ d u v w : ℤ, d ∈ ([-2,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-32) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-8)*u^2*v^2+((-32)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-8) (-32) x y hx hp
  exact ⟨d,u,v,w,model_0047_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0048_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-28)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-8)*u^2*v^2+((-28)/d)*v^4) :
    d ∈ ([-14,-7,-2,-1,1,2,7,14]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-28) (by decide) ([-14,-7,-2,-1,1,2,7,14]:List ℤ) ([2,7]:List ℤ)
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

theorem model_0048_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-8)*x+(-28))) :
    ∃ d u v w : ℤ, d ∈ ([-14,-7,-2,-1,1,2,7,14]:List ℤ) ∧ Squarefree d ∧ d ∣ (-28) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-8)*u^2*v^2+((-28)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-8) (-28) x y hx hp
  exact ⟨d,u,v,w,model_0048_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0049_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-24)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-8)*u^2*v^2+((-24)/d)*v^4) :
    d ∈ ([-6,-1,1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-24) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0375
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0520
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1108
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1249
      u v w hu hcop hw)
  · simp

theorem model_0049_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-8)*x+(-24))) :
    ∃ d u v w : ℤ, d ∈ ([-6,-1,1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (-24) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-8)*u^2*v^2+((-24)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-8) (-24) x y hx hp
  exact ⟨d,u,v,w,model_0049_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels01
