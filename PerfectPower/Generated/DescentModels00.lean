import PerfectPower.Generated.DescentExclusions00
import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions04
import PerfectPower.Generated.DescentExclusions05
import PerfectPower.Generated.DescentExclusions06
import PerfectPower.Generated.DescentExclusions07
import PerfectPower.Generated.DescentExclusions10
import PerfectPower.Generated.DescentExclusions11
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions13
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0000_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((-12)/d)*v^4) :
    d ∈ ([-3,-2,1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0230
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0702
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1097
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1243
      u v w hu hcop hw)
  · simp

theorem model_0000_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(-12))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-2,1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (-12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((-12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (-12) x y hx hp
  exact ⟨d,u,v,w,model_0000_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0001_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((-8)/d)*v^4) :
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

theorem model_0001_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(-8))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((-8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (-8) x y hx hp
  exact ⟨d,u,v,w,model_0001_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0002_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((-4)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0502
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1098
      u v w hu hcop hw)

theorem model_0002_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(-4))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((-4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (-4) x y hx hp
  exact ⟨d,u,v,w,model_0002_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0003_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((4)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0501
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0701
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0003_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(4))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (4) x y hx hp
  exact ⟨d,u,v,w,model_0003_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0004_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((8)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0500
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0700
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0004_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(8))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (8) x y hx hp
  exact ⟨d,u,v,w,model_0004_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0005_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((12)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0229
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0363
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0499
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0699
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1099
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1364
      u v w hu hcop hw)

theorem model_0005_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(12))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (12) x y hx hp
  exact ⟨d,u,v,w,model_0005_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0006_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (16)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((16)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (16) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0498
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0698
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1100
      u v w hu hcop hw)

theorem model_0006_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(16))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (16) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((16)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (16) x y hx hp
  exact ⟨d,u,v,w,model_0006_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0007_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (20)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((20)/d)*v^4) :
    d ∈ ([1,2,5,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (20) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0156
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0296
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0497
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0697
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0007_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(20))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,5,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (20) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((20)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (20) x y hx hp
  exact ⟨d,u,v,w,model_0007_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0008_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (24)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((24)/d)*v^4) :
    d ∈ ([1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (24) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0228
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0362
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0496
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0696
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1101
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1244
      u v w hu hcop hw)
  · simp

theorem model_0008_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(24))) :
    ∃ d u v w : ℤ, d ∈ ([1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (24) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((24)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (24) x y hx hp
  exact ⟨d,u,v,w,model_0008_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0009_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (28)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((28)/d)*v^4) :
    d ∈ ([1,2,7,14]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (28) (by decide) ([-14,-7,-2,-1,1,2,7,14]:List ℤ) ([2,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0099
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0190
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0495
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0695
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0009_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(28))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,7,14]:List ℤ) ∧ Squarefree d ∧ d ∣ (28) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((28)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (28) x y hx hp
  exact ⟨d,u,v,w,model_0009_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0010_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (32)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((32)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (32) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0494
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0694
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0010_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(32))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (32) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((32)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (32) x y hx hp
  exact ⟨d,u,v,w,model_0010_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0011_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (40)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((40)/d)*v^4) :
    d ∈ ([1,2,5,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (40) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0155
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0295
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0493
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0693
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0011_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(40))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,5,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (40) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((40)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (40) x y hx hp
  exact ⟨d,u,v,w,model_0011_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0012_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (44)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((44)/d)*v^4) :
    d ∈ ([1,2,11,22]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (44) (by decide) ([-22,-11,-2,-1,1,2,11,22]:List ℤ) ([2,11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0058
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0127
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0492
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0692
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0012_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(44))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,11,22]:List ℤ) ∧ Squarefree d ∧ d ∣ (44) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((44)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (44) x y hx hp
  exact ⟨d,u,v,w,model_0012_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0013_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (48)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((48)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (48) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0227
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0361
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0491
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0691
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1102
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1365
      u v w hu hcop hw)

theorem model_0013_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(48))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (48) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((48)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (48) x y hx hp
  exact ⟨d,u,v,w,model_0013_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0014_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (52)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((52)/d)*v^4) :
    d ∈ ([1,2,13,26]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (52) (by decide) ([-26,-13,-2,-1,1,2,13,26]:List ℤ) ([2,13]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0050
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0109
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0490
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0690
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0014_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(52))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,13,26]:List ℤ) ∧ Squarefree d ∧ d ∣ (52) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((52)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (52) x y hx hp
  exact ⟨d,u,v,w,model_0014_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0015_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (56)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((56)/d)*v^4) :
    d ∈ ([1,14]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (56) (by decide) ([-14,-7,-2,-1,1,2,7,14]:List ℤ) ([2,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0098
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0189
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0489
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0689
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1103
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1407
      u v w hu hcop hw)
  · simp

theorem model_0015_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(56))) :
    ∃ d u v w : ℤ, d ∈ ([1,14]:List ℤ) ∧ Squarefree d ∧ d ∣ (56) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((56)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (56) x y hx hp
  exact ⟨d,u,v,w,model_0015_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0016_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (60)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((60)/d)*v^4) :
    d ∈ ([1,6,10,15]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (60) (by decide) ([-30,-15,-10,-6,-5,-3,-2,-1,1,2,3,5,6,10,15,30]:List ℤ) ([2,3,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0040
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0087
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0154
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0226
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0294
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0360
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0488
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0688
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1104
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1245
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1328
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1467
      u v w hu hcop hw)

theorem model_0016_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(60))) :
    ∃ d u v w : ℤ, d ∈ ([1,6,10,15]:List ℤ) ∧ Squarefree d ∧ d ∣ (60) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((60)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (60) x y hx hp
  exact ⟨d,u,v,w,model_0016_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0017_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (64)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((64)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (64) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0487
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0687
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0017_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(64))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (64) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((64)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (64) x y hx hp
  exact ⟨d,u,v,w,model_0017_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0018_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (68)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((68)/d)*v^4) :
    d ∈ ([1,2,17,34]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (68) (by decide) ([-34,-17,-2,-1,1,2,17,34]:List ℤ) ([2,17]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0032
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0080
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0486
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0686
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0018_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(68))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,17,34]:List ℤ) ∧ Squarefree d ∧ d ∣ (68) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((68)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (68) x y hx hp
  exact ⟨d,u,v,w,model_0018_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0019_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (72)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((72)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (72) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0225
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0359
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0485
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0685
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1246
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1366
      u v w hu hcop hw)

theorem model_0019_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(72))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (72) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((72)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (72) x y hx hp
  exact ⟨d,u,v,w,model_0019_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0020_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (76)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((76)/d)*v^4) :
    d ∈ ([1,19]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (76) (by decide) ([-38,-19,-2,-1,1,2,19,38]:List ℤ) ([2,19]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0024
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0074
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0484
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0684
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1105
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1470
      u v w hu hcop hw)

theorem model_0020_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(76))) :
    ∃ d u v w : ℤ, d ∈ ([1,19]:List ℤ) ∧ Squarefree d ∧ d ∣ (76) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((76)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (76) x y hx hp
  exact ⟨d,u,v,w,model_0020_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0021_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (80)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((80)/d)*v^4) :
    d ∈ ([1,2,5,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (80) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0153
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0293
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0483
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0683
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0021_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(80))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,5,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (80) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((80)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (80) x y hx hp
  exact ⟨d,u,v,w,model_0021_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0022_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (84)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-12)*u^2*v^2+((84)/d)*v^4) :
    d ∈ ([1,3,7,21]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (84) (by decide) ([-42,-21,-14,-7,-6,-3,-2,-1,1,2,3,6,7,14,21,42]:List ℤ) ([2,3,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0016
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0067
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0097
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0188
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0224
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0358
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0482
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0682
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1106
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1367
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1447
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1474
      u v w hu hcop hw)

theorem model_0022_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-12)*x+(84))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,7,21]:List ℤ) ∧ Squarefree d ∧ d ∣ (84) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-12)*u^2*v^2+((84)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-12) (84) x y hx hp
  exact ⟨d,u,v,w,model_0022_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0023_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-23)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((-23)/d)*v^4) :
    d ∈ ([-23,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-23) (by decide) ([-23,-1,1,23]:List ℤ) ([23]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0721
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1460
      u v w hu hcop hw)

theorem model_0023_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(-23))) :
    ∃ d u v w : ℤ, d ∈ ([-23,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-23) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((-23)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (-23) x y hx hp
  exact ⟨d,u,v,w,model_0023_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0024_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-19)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-10)*u^2*v^2+((-19)/d)*v^4) :
    d ∈ ([-19,-1,1,19]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-19) (by decide) ([-19,-1,1,19]:List ℤ) ([19]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0024_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-10)*x+(-19))) :
    ∃ d u v w : ℤ, d ∈ ([-19,-1,1,19]:List ℤ) ∧ Squarefree d ∧ d ∣ (-19) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-10)*u^2*v^2+((-19)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-10) (-19) x y hx hp
  exact ⟨d,u,v,w,model_0024_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels00
