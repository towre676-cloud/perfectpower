import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions04
import PerfectPower.Generated.DescentExclusions05
import PerfectPower.Generated.DescentExclusions08
import PerfectPower.Generated.DescentExclusions09
import PerfectPower.Generated.DescentExclusions11
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions13
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels11
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0275_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-16)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-16)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-16) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0275_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-16))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-16) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-16)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-16) x y hx hp
  exact ⟨d,u,v,w,model_0275_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0276_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-12)/d)*v^4) :
    d ∈ ([-3,-2,1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0262
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0910
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1168
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1284
      u v w hu hcop hw)
  · simp

theorem model_0276_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-12))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-2,1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (-12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-12) x y hx hp
  exact ⟨d,u,v,w,model_0276_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0277_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-11)/d)*v^4) :
    d ∈ ([-11,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0909
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1436
      u v w hu hcop hw)

theorem model_0277_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-11))) :
    ∃ d u v w : ℤ, d ∈ ([-11,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-11) x y hx hp
  exact ⟨d,u,v,w,model_0277_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0278_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-10)/d)*v^4) :
    d ∈ ([-10,-1,1,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0328
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0597
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1169
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1345
      u v w hu hcop hw)
  · simp

theorem model_0278_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-10))) :
    ∃ d u v w : ℤ, d ∈ ([-10,-1,1,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (-10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-10) x y hx hp
  exact ⟨d,u,v,w,model_0278_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0279_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-9)/d)*v^4) :
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

theorem model_0279_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-9))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-9) x y hx hp
  exact ⟨d,u,v,w,model_0279_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0280_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-8)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0280_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-8))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-8) x y hx hp
  exact ⟨d,u,v,w,model_0280_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0281_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-7)/d)*v^4) :
    d ∈ ([-7,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0908
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1413
      u v w hu hcop hw)

theorem model_0281_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-7))) :
    ∃ d u v w : ℤ, d ∈ ([-7,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-7) x y hx hp
  exact ⟨d,u,v,w,model_0281_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0282_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-6)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-6)/d)*v^4) :
    d ∈ ([-6,-2,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-6) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0428
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0907
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1170
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1385
      u v w hu hcop hw)

theorem model_0282_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-6))) :
    ∃ d u v w : ℤ, d ∈ ([-6,-2,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-6) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-6)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-6) x y hx hp
  exact ⟨d,u,v,w,model_0282_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0283_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-5)/d)*v^4) :
    d ∈ ([-5,-1,1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0283_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-5))) :
    ∃ d u v w : ℤ, d ∈ ([-5,-1,1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (-5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-5) x y hx hp
  exact ⟨d,u,v,w,model_0283_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0284_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-4)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0284_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-4))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-4) x y hx hp
  exact ⟨d,u,v,w,model_0284_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0285_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-3)/d)*v^4) :
    d ∈ ([-3,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0906
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1285
      u v w hu hcop hw)

theorem model_0285_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-3))) :
    ∃ d u v w : ℤ, d ∈ ([-3,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-3) x y hx hp
  exact ⟨d,u,v,w,model_0285_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0286_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-2)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0286_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-2))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-2) x y hx hp
  exact ⟨d,u,v,w,model_0286_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0287_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((-1)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · simp
  · simp

theorem model_0287_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(-1))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((-1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (-1) x y hx hp
  exact ⟨d,u,v,w,model_0287_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0288_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((1)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0905
      u v w hu hcop hw)
  · simp

theorem model_0288_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(1))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (1) x y hx hp
  exact ⟨d,u,v,w,model_0288_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0289_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((2)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0596
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0904
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0289_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(2))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (2) x y hx hp
  exact ⟨d,u,v,w,model_0289_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0290_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((3)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0427
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0903
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0290_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(3))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (3) x y hx hp
  exact ⟨d,u,v,w,model_0290_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0291_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((4)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0595
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0902
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0291_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(4))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (4) x y hx hp
  exact ⟨d,u,v,w,model_0291_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0292_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((5)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0327
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0901
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0292_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(5))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (5) x y hx hp
  exact ⟨d,u,v,w,model_0292_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0293_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (6)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((6)/d)*v^4) :
    d ∈ ([1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (6) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0261
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0426
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0594
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0900
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1171
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1286
      u v w hu hcop hw)
  · simp

theorem model_0293_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(6))) :
    ∃ d u v w : ℤ, d ∈ ([1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (6) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((6)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (6) x y hx hp
  exact ⟨d,u,v,w,model_0293_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0294_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((7)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0208
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0899
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0294_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(7))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (7) x y hx hp
  exact ⟨d,u,v,w,model_0294_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0295_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((8)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0593
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0898
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0295_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(8))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (8) x y hx hp
  exact ⟨d,u,v,w,model_0295_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0296_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((9)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0425
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0897
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1287
      u v w hu hcop hw)

theorem model_0296_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(9))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (9) x y hx hp
  exact ⟨d,u,v,w,model_0296_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0297_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((10)/d)*v^4) :
    d ∈ ([1,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0172
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0326
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0592
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0896
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1172
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1346
      u v w hu hcop hw)
  · simp

theorem model_0297_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(10))) :
    ∃ d u v w : ℤ, d ∈ ([1,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (10) x y hx hp
  exact ⟨d,u,v,w,model_0297_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0298_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((11)/d)*v^4) :
    d ∈ ([1,11]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0140
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0895
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0298_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(11))) :
    ∃ d u v w : ℤ, d ∈ ([1,11]:List ℤ) ∧ Squarefree d ∧ d ∣ (11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (11) x y hx hp
  exact ⟨d,u,v,w,model_0298_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0299_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(0)*u^2*v^2+((12)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0260
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0424
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0591
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0894
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1173
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1386
      u v w hu hcop hw)

theorem model_0299_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(0)*x+(12))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(0)*u^2*v^2+((12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (0) (12) x y hx hp
  exact ⟨d,u,v,w,model_0299_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels11
