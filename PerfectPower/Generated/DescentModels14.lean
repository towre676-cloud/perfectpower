import PerfectPower.Generated.DescentExclusions00
import PerfectPower.Generated.DescentExclusions01
import PerfectPower.Generated.DescentExclusions02
import PerfectPower.Generated.DescentExclusions03
import PerfectPower.Generated.DescentExclusions04
import PerfectPower.Generated.DescentExclusions06
import PerfectPower.Generated.DescentExclusions09
import PerfectPower.Generated.DescentExclusions11
import PerfectPower.Generated.DescentExclusions12
import PerfectPower.Generated.DescentExclusions13
import PerfectPower.Generated.DescentExclusions14

namespace PerfectPower.Generated.DescentModels14
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem model_0350_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((-4)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0612
      u v w hu hcop hw)
  · simp
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1185
      u v w hu hcop hw)

theorem model_0350_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(-4))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((-4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (-4) x y hx hp
  exact ⟨d,u,v,w,model_0350_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0351_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((-3)/d)*v^4) :
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

theorem model_0351_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(-3))) :
    ∃ d u v w : ℤ, d ∈ ([-3,-1,1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (-3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((-3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (-3) x y hx hp
  exact ⟨d,u,v,w,model_0351_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0352_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((-2)/d)*v^4) :
    d ∈ ([-2,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0954
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1186
      u v w hu hcop hw)

theorem model_0352_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(-2))) :
    ∃ d u v w : ℤ, d ∈ ([-2,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((-2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (-2) x y hx hp
  exact ⟨d,u,v,w,model_0352_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0353_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (-1)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((-1)/d)*v^4) :
    d ∈ ([-1,1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (-1) (by decide) ([-1,1]:List ℤ) ([]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl
  · simp
  · simp

theorem model_0353_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(-1))) :
    ∃ d u v w : ℤ, d ∈ ([-1,1]:List ℤ) ∧ Squarefree d ∧ d ∣ (-1) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((-1)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (-1) x y hx hp
  exact ⟨d,u,v,w,model_0353_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0354_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (2)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((2)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (2) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0611
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0953
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0354_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(2))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (2) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((2)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (2) x y hx hp
  exact ⟨d,u,v,w,model_0354_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0355_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (3)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((3)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (3) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0440
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0952
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0355_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(3))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (3) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((3)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (3) x y hx hp
  exact ⟨d,u,v,w,model_0355_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0356_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (4)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((4)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (4) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0610
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0951
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1187
      u v w hu hcop hw)

theorem model_0356_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(4))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (4) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((4)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (4) x y hx hp
  exact ⟨d,u,v,w,model_0356_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0357_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (5)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((5)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (5) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0335
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0950
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0357_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(5))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (5) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((5)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (5) x y hx hp
  exact ⟨d,u,v,w,model_0357_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0358_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (6)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((6)/d)*v^4) :
    d ∈ ([1,6]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (6) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0268
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0439
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0609
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0949
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1188
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1297
      u v w hu hcop hw)
  · simp

theorem model_0358_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(6))) :
    ∃ d u v w : ℤ, d ∈ ([1,6]:List ℤ) ∧ Squarefree d ∧ d ∣ (6) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((6)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (6) x y hx hp
  exact ⟨d,u,v,w,model_0358_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0359_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (7)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((7)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (7) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0212
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0948
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0359_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(7))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (7) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((7)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (7) x y hx hp
  exact ⟨d,u,v,w,model_0359_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0360_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (8)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((8)/d)*v^4) :
    d ∈ ([1,2]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (8) (by decide) ([-2,-1,1,2]:List ℤ) ([2]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0608
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0947
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0360_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(8))) :
    ∃ d u v w : ℤ, d ∈ ([1,2]:List ℤ) ∧ Squarefree d ∧ d ∣ (8) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((8)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (8) x y hx hp
  exact ⟨d,u,v,w,model_0360_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0361_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (9)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((9)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (9) (by decide) ([-3,-1,1,3]:List ℤ) ([3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0438
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0946
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1298
      u v w hu hcop hw)

theorem model_0361_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(9))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (9) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((9)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (9) x y hx hp
  exact ⟨d,u,v,w,model_0361_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0362_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (10)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((10)/d)*v^4) :
    d ∈ ([1,2,5,10]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (10) (by decide) ([-10,-5,-2,-1,1,2,5,10]:List ℤ) ([2,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0174
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0334
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0607
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0945
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0362_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(10))) :
    ∃ d u v w : ℤ, d ∈ ([1,2,5,10]:List ℤ) ∧ Squarefree d ∧ d ∣ (10) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((10)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (10) x y hx hp
  exact ⟨d,u,v,w,model_0362_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0363_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (11)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((11)/d)*v^4) :
    d ∈ ([1,11]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (11) (by decide) ([-11,-1,1,11]:List ℤ) ([11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0143
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0944
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0363_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(11))) :
    ∃ d u v w : ℤ, d ∈ ([1,11]:List ℤ) ∧ Squarefree d ∧ d ∣ (11) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((11)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (11) x y hx hp
  exact ⟨d,u,v,w,model_0363_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0364_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (12)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((12)/d)*v^4) :
    d ∈ ([1,3]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (12) (by decide) ([-6,-3,-2,-1,1,2,3,6]:List ℤ) ([2,3]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0267
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0437
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions06.cover_0606
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0943
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions11.cover_1189
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1393
      u v w hu hcop hw)

theorem model_0364_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(12))) :
    ∃ d u v w : ℤ, d ∈ ([1,3]:List ℤ) ∧ Squarefree d ∧ d ∣ (12) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((12)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (12) x y hx hp
  exact ⟨d,u,v,w,model_0364_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0365_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (13)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((13)/d)*v^4) :
    d ∈ ([1,13]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (13) (by decide) ([-13,-1,1,13]:List ℤ) ([13]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0118
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0942
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0365_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(13))) :
    ∃ d u v w : ℤ, d ∈ ([1,13]:List ℤ) ∧ Squarefree d ∧ d ∣ (13) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((13)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (13) x y hx hp
  exact ⟨d,u,v,w,model_0365_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0366_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (17)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((17)/d)*v^4) :
    d ∈ ([1,17]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (17) (by decide) ([-17,-1,1,17]:List ℤ) ([17]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0084
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0941
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0366_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(17))) :
    ∃ d u v w : ℤ, d ∈ ([1,17]:List ℤ) ∧ Squarefree d ∧ d ∣ (17) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((17)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (17) x y hx hp
  exact ⟨d,u,v,w,model_0366_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0367_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (21)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((21)/d)*v^4) :
    d ∈ ([1,21]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (21) (by decide) ([-21,-7,-3,-1,1,3,7,21]:List ℤ) ([3,7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0071
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0211
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0436
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0940
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions12.cover_1299
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1415
      u v w hu hcop hw)
  · simp

theorem model_0367_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(21))) :
    ∃ d u v w : ℤ, d ∈ ([1,21]:List ℤ) ∧ Squarefree d ∧ d ∣ (21) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((21)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (21) x y hx hp
  exact ⟨d,u,v,w,model_0367_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0368_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (25)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((25)/d)*v^4) :
    d ∈ ([1]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (25) (by decide) ([-5,-1,1,5]:List ℤ) ([5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0333
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0939
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1351
      u v w hu hcop hw)

theorem model_0368_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(25))) :
    ∃ d u v w : ℤ, d ∈ ([1]:List ℤ) ∧ Squarefree d ∧ d ∣ (25) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((25)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (25) x y hx hp
  exact ⟨d,u,v,w,model_0368_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0369_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (29)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((29)/d)*v^4) :
    d ∈ ([1,29]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (29) (by decide) ([-29,-1,1,29]:List ℤ) ([29]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0047
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0938
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0369_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(29))) :
    ∃ d u v w : ℤ, d ∈ ([1,29]:List ℤ) ∧ Squarefree d ∧ d ∣ (29) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((29)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (29) x y hx hp
  exact ⟨d,u,v,w,model_0369_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0370_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (33)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((33)/d)*v^4) :
    d ∈ ([1,3,11,33]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (33) (by decide) ([-33,-11,-3,-1,1,3,11,33]:List ℤ) ([3,11]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0037
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions01.cover_0142
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0435
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0937
      u v w hu hcop hw)
  · simp
  · simp
  · simp
  · simp

theorem model_0370_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(33))) :
    ∃ d u v w : ℤ, d ∈ ([1,3,11,33]:List ℤ) ∧ Squarefree d ∧ d ∣ (33) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((33)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (33) x y hx hp
  exact ⟨d,u,v,w,model_0370_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0371_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (37)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((37)/d)*v^4) :
    d ∈ ([1,37]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (37) (by decide) ([-37,-1,1,37]:List ℤ) ([37]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0029
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0936
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0371_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(37))) :
    ∃ d u v w : ℤ, d ∈ ([1,37]:List ℤ) ∧ Squarefree d ∧ d ∣ (37) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((37)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (37) x y hx hp
  exact ⟨d,u,v,w,model_0371_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0372_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (41)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((41)/d)*v^4) :
    d ∈ ([1,41]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (41) (by decide) ([-41,-1,1,41]:List ℤ) ([41]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0021
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0935
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0372_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(41))) :
    ∃ d u v w : ℤ, d ∈ ([1,41]:List ℤ) ∧ Squarefree d ∧ d ∣ (41) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((41)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (41) x y hx hp
  exact ⟨d,u,v,w,model_0372_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0373_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (45)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((45)/d)*v^4) :
    d ∈ ([1,5]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (45) (by decide) ([-15,-5,-3,-1,1,3,5,15]:List ℤ) ([3,5]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions00.cover_0092
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions03.cover_0332
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions04.cover_0434
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0934
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions13.cover_1300
      u v w hu hcop hw)
  · simp
  · exact False.elim (PerfectPower.Generated.DescentExclusions14.cover_1456
      u v w hu hcop hw)

theorem model_0373_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(45))) :
    ∃ d u v w : ℤ, d ∈ ([1,5]:List ℤ) ∧ Squarefree d ∧ d ∣ (45) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((45)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (45) x y hx hp
  exact ⟨d,u,v,w,model_0373_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

theorem model_0374_support (d u v w : ℤ) (hd : Squarefree d)
    (hdb : d ∣ (49)) (hu : u ≠ 0) (hcop : IsRelPrime u v)
    (hw : w^2=d*u^4+(2)*u^2*v^2+((49)/d)*v^4) :
    d ∈ ([1,7]:List ℤ) := by
  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table
    (49) (by decide) ([-7,-1,1,7]:List ℤ) ([7]:List ℤ)
    (by decide) (by decide) d hd hdb
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact False.elim (PerfectPower.Generated.DescentExclusions02.cover_0210
      u v w hu hcop hw)
  · exact False.elim (PerfectPower.Generated.DescentExclusions09.cover_0933
      u v w hu hcop hw)
  · simp
  · simp

theorem model_0374_rational_cover (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(2)*x+(49))) :
    ∃ d u v w : ℤ, d ∈ ([1,7]:List ℤ) ∧ Squarefree d ∧ d ∣ (49) ∧
      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+(2)*u^2*v^2+((49)/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=
    PerfectPower.TwoDescentBridges.rational_point_cover_complete (2) (49) x y hx hp
  exact ⟨d,u,v,w,model_0374_support d u v w hd hdb hu hcop hw,
    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

end PerfectPower.Generated.DescentModels14
