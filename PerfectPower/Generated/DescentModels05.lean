import PerfectPower.Generated.DescentExclusions00
import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions05
import PerfectPower.Generated.DescentExclusions07
import PerfectPower.Generated.DescentExclusions08
import PerfectPower.Generated.DescentExclusions11
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions13
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels05
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0125_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((2)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0536
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0782
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0125_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(2))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (2) x y hx hp
  exact ⟨d,u,v,w,model_0125_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0126_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((3)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0389
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0781
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0126_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(3))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (3) x y hx hp
  exact ⟨d,u,v,w,model_0126_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0127_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((4)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0535
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0780
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1131
      u v w hu hcop hw)

theorem model_0127_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(4))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (4) x y hx hp
  exact ⟨d,u,v,w,model_0127_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0128_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((5)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0309
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0779
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0128_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(5))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (5) x y hx hp
  exact ⟨d,u,v,w,model_0128_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0129_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (6)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((6)/d)*v^4) :
    d ∈ ([1,2,3,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (6) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0240
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0388
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0534
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0778
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0129_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(6))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,3,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (6) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((6)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (6) x y hx hp
  exact ⟨d,u,v,w,model_0129_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0130_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((7)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0198
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0777
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0130_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(7))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (7) x y hx hp
  exact ⟨d,u,v,w,model_0130_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0131_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((8)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0533
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0776
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0131_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(8))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (8) x y hx hp
  exact ⟨d,u,v,w,model_0131_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0132_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((9)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0387
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0775
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0132_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(9))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (9) x y hx hp
  exact ⟨d,u,v,w,model_0132_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0133_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((10)/d)*v^4) :
    d ∈ ([1,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0162
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0308
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0532
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0774
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1132
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1335
      u v w hu hcop hw)
  · simp

theorem model_0133_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(10))) :
    ∃ d u v w : ℤ, d ∈ ([1,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (10) x y hx hp
  exact ⟨d,u,v,w,model_0133_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0134_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((11)/d)*v^4) :
    d ∈ ([1,11]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0132
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0773
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0134_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(11))) :
    ∃ d u v w : ℤ, d ∈ ([1,11]:List ℤ) ∧ Squarefree d ∧ d ∣ (11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (11) x y hx hp
  exact ⟨d,u,v,w,model_0134_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0135_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-5)*u^2*v^2+((12)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0239
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0386
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0531
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions07.cover_0772
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1133
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1373
      u v w hu hcop hw)

theorem model_0135_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-5)*x+(12))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-5)*u^2*v^2+((12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-5) (12) x y hx hp
  exact ⟨d,u,v,w,model_0135_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0136_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-44)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-44)/d)*v^4) :
    d ∈ ([-11,-2,1,22]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-44) (by decide) ([-22,-11,-2,-1,1,2,11,22]:List ℤ) ([2,11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0061
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0818
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1134
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1432
      u v w hu hcop hw)
  · simp

theorem model_0136_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-44))) :
    ∃ d u v w : ℤ, d ∈ ([-11,-2,1,22]:List ℤ) ∧ Squarefree d ∧ d ∣ (-44) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-44)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-44) x y hx hp
  exact ⟨d,u,v,w,model_0136_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0137_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-40)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-40)/d)*v^4) :
    d ∈ ([-10,-5,-2,-1,1,2,5,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-40) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
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

theorem model_0137_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-40))) :
    ∃ d u v w : ℤ, d ∈ ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (-40) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-40)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-40) x y hx hp
  exact ⟨d,u,v,w,model_0137_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0138_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-36)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-36)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-36) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0247
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0399
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1261
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1374
      u v w hu hcop hw)

theorem model_0138_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-36))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-36) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-36)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-36) x y hx hp
  exact ⟨d,u,v,w,model_0138_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0139_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-32)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-32)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-32) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0139_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-32))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-32) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-32)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-32) x y hx hp
  exact ⟨d,u,v,w,model_0139_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0140_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-28)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-28)/d)*v^4) :
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

theorem model_0140_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-28))) :
    ∃ d u v w : ℤ, d ∈ ([-14,-7,-2,-1,1,2,7,14]:List ℤ) ∧ Squarefree d ∧ d ∣ (-28) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-28)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-28) x y hx hp
  exact ⟨d,u,v,w,model_0140_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0141_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-24)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-24)/d)*v^4) :
    d ∈ ([-6,-3,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-24) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0556
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0817
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1262
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1375
      u v w hu hcop hw)

theorem model_0141_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-24))) :
    ∃ d u v w : ℤ, d ∈ ([-6,-3,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-24) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-24)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-24) x y hx hp
  exact ⟨d,u,v,w,model_0141_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0142_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-20)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-20)/d)*v^4) :
    d ∈ ([-5,-2,1,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-20) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0166
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0816
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1135
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1336
      u v w hu hcop hw)
  · simp

theorem model_0142_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-20))) :
    ∃ d u v w : ℤ, d ∈ ([-5,-2,1,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (-20) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-20)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-20) x y hx hp
  exact ⟨d,u,v,w,model_0142_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0143_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-16)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-16)/d)*v^4) :
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

theorem model_0143_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-16))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-16) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-16)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-16) x y hx hp
  exact ⟨d,u,v,w,model_0143_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0144_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-12)/d)*v^4) :
    d ∈ ([-6,-3,-2,-1,1,2,3,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
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

theorem model_0144_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-12))) :
    ∃ d u v w : ℤ, d ∈ ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (-12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-12) x y hx hp
  exact ⟨d,u,v,w,model_0144_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0145_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-11)/d)*v^4) :
    d ∈ ([-11,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0815
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1433
      u v w hu hcop hw)

theorem model_0145_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-11))) :
    ∃ d u v w : ℤ, d ∈ ([-11,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-11) x y hx hp
  exact ⟨d,u,v,w,model_0145_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0146_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-10)/d)*v^4) :
    d ∈ ([-10,-5,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions05.cover_0555
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0814
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1337
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1421
      u v w hu hcop hw)

theorem model_0146_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-10))) :
    ∃ d u v w : ℤ, d ∈ ([-10,-5,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (-10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-10) x y hx hp
  exact ⟨d,u,v,w,model_0146_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0147_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-9)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0398
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1263
      u v w hu hcop hw)

theorem model_0147_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-9))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-9) x y hx hp
  exact ⟨d,u,v,w,model_0147_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0148_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-8)/d)*v^4) :
    d ∈ ([-2,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0813
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1136
      u v w hu hcop hw)

theorem model_0148_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-8))) :
    ∃ d u v w : ℤ, d ∈ ([-2,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-8) x y hx hp
  exact ⟨d,u,v,w,model_0148_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0149_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(-4)*u^2*v^2+((-7)/d)*v^4) :
    d ∈ ([-7,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions08.cover_0812
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1409
      u v w hu hcop hw)

theorem model_0149_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(-4)*x+(-7))) :
    ∃ d u v w : ℤ, d ∈ ([-7,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(-4)*u^2*v^2+((-7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (-4) (-7) x y hx hp
  exact ⟨d,u,v,w,model_0149_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels05
