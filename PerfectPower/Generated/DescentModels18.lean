import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions04
import PerfectPower.Generated.DescentExclusions06
import PerfectPower.Generated.DescentExclusions10
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions13
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels18
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0450_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((-2)/d)*v^4) :
    d ∈ ([-2,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1015
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1210
      u v w hu hcop hw)

theorem model_0450_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(-2))) :
    ∃ d u v w : ℤ, d ∈ ([-2,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((-2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (-2) x y hx hp
  exact ⟨d,u,v,w,model_0450_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0451_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((-1)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · simp
  · simp

theorem model_0451_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(-1))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((-1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (-1) x y hx hp
  exact ⟨d,u,v,w,model_0451_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0452_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((1)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1014
      u v w hu hcop hw)
  · simp

theorem model_0452_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(1))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (1) x y hx hp
  exact ⟨d,u,v,w,model_0452_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0453_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((2)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0643
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1013
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0453_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(2))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (2) x y hx hp
  exact ⟨d,u,v,w,model_0453_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0454_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((3)/d)*v^4) :
    d ∈ ([-3,-1,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0454_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(3))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (3) x y hx hp
  exact ⟨d,u,v,w,model_0454_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0455_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((4)/d)*v^4) :
    d ∈ ([-2,-1,1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0455_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(4))) :
    ∃ d u v w : ℤ, d ∈ ([-2,-1,1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (4) x y hx hp
  exact ⟨d,u,v,w,model_0455_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0456_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((5)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0344
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1012
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0456_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(5))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (5) x y hx hp
  exact ⟨d,u,v,w,model_0456_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0457_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (6)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((6)/d)*v^4) :
    d ∈ ([-3,-2,1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (6) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0279
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1011
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1211
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1311
      u v w hu hcop hw)
  · simp

theorem model_0457_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(6))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-2,1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (6) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((6)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (6) x y hx hp
  exact ⟨d,u,v,w,model_0457_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0458_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((7)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0216
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1010
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0458_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(7))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (7) x y hx hp
  exact ⟨d,u,v,w,model_0458_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0459_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((8)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0642
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1009
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0459_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(8))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (8) x y hx hp
  exact ⟨d,u,v,w,model_0459_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0460_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((9)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0457
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1008
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1312
      u v w hu hcop hw)

theorem model_0460_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(9))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (9) x y hx hp
  exact ⟨d,u,v,w,model_0460_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0461_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((10)/d)*v^4) :
    d ∈ ([1,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0180
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0343
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0641
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1007
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1212
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1358
      u v w hu hcop hw)
  · simp

theorem model_0461_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(10))) :
    ∃ d u v w : ℤ, d ∈ ([1,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (10) x y hx hp
  exact ⟨d,u,v,w,model_0461_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0462_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((11)/d)*v^4) :
    d ∈ ([1,11]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0147
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1006
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0462_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(11))) :
    ∃ d u v w : ℤ, d ∈ ([1,11]:List ℤ) ∧ Squarefree d ∧ d ∣ (11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (11) x y hx hp
  exact ⟨d,u,v,w,model_0462_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0463_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(5)*u^2*v^2+((12)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0278
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0456
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0640
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1005
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1213
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1398
      u v w hu hcop hw)

theorem model_0463_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(5)*x+(12))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(5)*u^2*v^2+((12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (5) (12) x y hx hp
  exact ⟨d,u,v,w,model_0463_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0464_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-39)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-39)/d)*v^4) :
    d ∈ ([-39,-3,1,13]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-39) (by decide) ([-39,-13,-3,-1,1,3,13,39]:List ℤ) ([3,13]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0122
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1048
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1313
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1473
      u v w hu hcop hw)

theorem model_0464_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-39))) :
    ∃ d u v w : ℤ, d ∈ ([-39,-3,1,13]:List ℤ) ∧ Squarefree d ∧ d ∣ (-39) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-39)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-39) x y hx hp
  exact ⟨d,u,v,w,model_0464_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0465_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-35)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-35)/d)*v^4) :
    d ∈ ([-35,-7,-5,-1,1,5,7,35]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-35) (by decide) ([-35,-7,-5,-1,1,5,7,35]:List ℤ) ([5,7]:List ℤ)
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

theorem model_0465_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-35))) :
    ∃ d u v w : ℤ, d ∈ ([-35,-7,-5,-1,1,5,7,35]:List ℤ) ∧ Squarefree d ∧ d ∣ (-35) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-35)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-35) x y hx hp
  exact ⟨d,u,v,w,model_0465_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0466_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-31)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-31)/d)*v^4) :
    d ∈ ([-31,-1,1,31]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-31) (by decide) ([-31,-1,1,31]:List ℤ) ([31]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0466_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-31))) :
    ∃ d u v w : ℤ, d ∈ ([-31,-1,1,31]:List ℤ) ∧ Squarefree d ∧ d ∣ (-31) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-31)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-31) x y hx hp
  exact ⟨d,u,v,w,model_0466_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0467_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-27)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-27)/d)*v^4) :
    d ∈ ([-3,-1,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-27) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0467_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-27))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-27) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-27)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-27) x y hx hp
  exact ⟨d,u,v,w,model_0467_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0468_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-23)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-23)/d)*v^4) :
    d ∈ ([-23,-1,1,23]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-23) (by decide) ([-23,-1,1,23]:List ℤ) ([23]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp

theorem model_0468_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-23))) :
    ∃ d u v w : ℤ, d ∈ ([-23,-1,1,23]:List ℤ) ∧ Squarefree d ∧ d ∣ (-23) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-23)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-23) x y hx hp
  exact ⟨d,u,v,w,model_0468_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0469_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-19)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-19)/d)*v^4) :
    d ∈ ([-19,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-19) (by decide) ([-19,-1,1,19]:List ℤ) ([19]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1047
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1459
      u v w hu hcop hw)

theorem model_0469_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-19))) :
    ∃ d u v w : ℤ, d ∈ ([-19,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-19) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-19)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-19) x y hx hp
  exact ⟨d,u,v,w,model_0469_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0470_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-15)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-15)/d)*v^4) :
    d ∈ ([-15,-5,1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-15) (by decide) ([-15,-5,-3,-1,1,3,5,15]:List ℤ) ([3,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0467
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1046
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1359
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1457
      u v w hu hcop hw)

theorem model_0470_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-15))) :
    ∃ d u v w : ℤ, d ∈ ([-15,-5,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-15) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-15)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-15) x y hx hp
  exact ⟨d,u,v,w,model_0470_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0471_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-12)/d)*v^4) :
    d ∈ ([-3,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0282
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0652
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1045
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1214
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1314
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1399
      u v w hu hcop hw)

theorem model_0471_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-12))) :
    ∃ d u v w : ℤ, d ∈ ([-3,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-12) x y hx hp
  exact ⟨d,u,v,w,model_0471_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0472_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-11)/d)*v^4) :
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

theorem model_0472_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-11))) :
    ∃ d u v w : ℤ, d ∈ ([-11,-1,1,11]:List ℤ) ∧ Squarefree d ∧ d ∣ (-11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-11) x y hx hp
  exact ⟨d,u,v,w,model_0472_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0473_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-10)/d)*v^4) :
    d ∈ ([-10,-2,1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0349
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions10.cover_1044
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1215
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1429
      u v w hu hcop hw)

theorem model_0473_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-10))) :
    ∃ d u v w : ℤ, d ∈ ([-10,-2,1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (-10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-10) x y hx hp
  exact ⟨d,u,v,w,model_0473_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0474_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(6)*u^2*v^2+((-9)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0466
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1315
      u v w hu hcop hw)

theorem model_0474_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(6)*x+(-9))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(6)*u^2*v^2+((-9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (6) (-9) x y hx hp
  exact ⟨d,u,v,w,model_0474_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels18
