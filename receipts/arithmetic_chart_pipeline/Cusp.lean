import PerfectPower.BranchingResidueCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Branching_e98fae427c4c8b4b
open PerfectPower.BranchingResidueCharts
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^2 + (-1) * (x)^3 * (y)^0
def G0 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^3 * (v)^0
theorem identity0 (u v : ℤ) : F (0+1*u) (0+1*v) = (1)*G0 u v := by unfold F G0; ring
def chart0 : Chart F := ⟨0,0,1,1,G0,by norm_num,by norm_num,identity0⟩
theorem zeros0 (u v : ℤ) : F (0+1*u) (0+1*v)=0 ↔ G0 u v=0 := chart0.zero_iff u v
#print axioms identity0
#print axioms zeros0
def G1 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-2) * (u)^3 * (v)^0
theorem identity1 (u v : ℤ) : F (0+2*u) (0+2*v) = (4)*G1 u v := by unfold F G1; ring
def chart1 : Chart F := ⟨0,0,2,4,G1,by norm_num,by norm_num,identity1⟩
theorem zeros1 (u v : ℤ) : F (0+2*u) (0+2*v)=0 ↔ G1 u v=0 := chart1.zero_iff u v
#print axioms identity1
#print axioms zeros1
def G2 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-4) * (u)^3 * (v)^0
theorem identity2 (u v : ℤ) : F (0+4*u) (0+4*v) = (16)*G2 u v := by unfold F G2; ring
def chart2 : Chart F := ⟨0,0,4,16,G2,by norm_num,by norm_num,identity2⟩
theorem zeros2 (u v : ℤ) : F (0+4*u) (0+4*v)=0 ↔ G2 u v=0 := chart2.zero_iff u v
#print axioms identity2
#print axioms zeros2
def G3 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-8) * (u)^3 * (v)^0
theorem identity3 (u v : ℤ) : F (0+8*u) (0+8*v) = (64)*G3 u v := by unfold F G3; ring
def chart3 : Chart F := ⟨0,0,8,64,G3,by norm_num,by norm_num,identity3⟩
theorem zeros3 (u v : ℤ) : F (0+8*u) (0+8*v)=0 ↔ G3 u v=0 := chart3.zero_iff u v
#print axioms identity3
#print axioms zeros3
def G4 (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^0 + (1) * (u)^0 * (v)^2 + (-6) * (u)^1 * (v)^0 + (-12) * (u)^2 * (v)^0 + (-8) * (u)^3 * (v)^0
theorem identity4 (u v : ℤ) : F (4+8*u) (0+8*v) = (64)*G4 u v := by unfold F G4; ring
def chart4 : Chart F := ⟨4,0,8,64,G4,by norm_num,by norm_num,identity4⟩
theorem zeros4 (u v : ℤ) : F (4+8*u) (0+8*v)=0 ↔ G4 u v=0 := chart4.zero_iff u v
#print axioms identity4
#print axioms zeros4
def G5 (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^0 + (2) * (u)^0 * (v)^2 + (-6) * (u)^1 * (v)^0 + (-12) * (u)^2 * (v)^0 + (-8) * (u)^3 * (v)^0
theorem identity5 (u v : ℤ) : F (2+4*u) (0+4*v) = (8)*G5 u v := by unfold F G5; ring
def chart5 : Chart F := ⟨2,0,4,8,G5,by norm_num,by norm_num,identity5⟩
theorem zeros5 (u v : ℤ) : F (2+4*u) (0+4*v)=0 ↔ G5 u v=0 := chart5.zero_iff u v
#print axioms identity5
#print axioms zeros5
def G6 (u v : ℤ) : ℤ := (2) * (u)^0 * (v)^1 + (2) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-6) * (u)^2 * (v)^0 + (-4) * (u)^3 * (v)^0
theorem identity6 (u v : ℤ) : F (1+2*u) (1+2*v) = (2)*G6 u v := by unfold F G6; ring
def chart6 : Chart F := ⟨1,1,2,2,G6,by norm_num,by norm_num,identity6⟩
theorem zeros6 (u v : ℤ) : F (1+2*u) (1+2*v)=0 ↔ G6 u v=0 := chart6.zero_iff u v
#print axioms identity6
#print axioms zeros6
def G7 (u v : ℤ) : ℤ := (2) * (u)^0 * (v)^1 + (4) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-12) * (u)^2 * (v)^0 + (-16) * (u)^3 * (v)^0
theorem identity7 (u v : ℤ) : F (1+4*u) (1+4*v) = (4)*G7 u v := by unfold F G7; ring
def chart7 : Chart F := ⟨1,1,4,4,G7,by norm_num,by norm_num,identity7⟩
theorem zeros7 (u v : ℤ) : F (1+4*u) (1+4*v)=0 ↔ G7 u v=0 := chart7.zero_iff u v
#print axioms identity7
#print axioms zeros7
def G8 (u v : ℤ) : ℤ := (2) * (u)^0 * (v)^1 + (8) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-24) * (u)^2 * (v)^0 + (-64) * (u)^3 * (v)^0
theorem identity8 (u v : ℤ) : F (1+8*u) (1+8*v) = (8)*G8 u v := by unfold F G8; ring
def chart8 : Chart F := ⟨1,1,8,8,G8,by norm_num,by norm_num,identity8⟩
theorem zeros8 (u v : ℤ) : F (1+8*u) (1+8*v)=0 ↔ G8 u v=0 := chart8.zero_iff u v
#print axioms identity8
#print axioms zeros8
def G9 (u v : ℤ) : ℤ := (3) * (u)^0 * (v)^0 + (10) * (u)^0 * (v)^1 + (8) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-24) * (u)^2 * (v)^0 + (-64) * (u)^3 * (v)^0
theorem identity9 (u v : ℤ) : F (1+8*u) (5+8*v) = (8)*G9 u v := by unfold F G9; ring
def chart9 : Chart F := ⟨1,5,8,8,G9,by norm_num,by norm_num,identity9⟩
theorem zeros9 (u v : ℤ) : F (1+8*u) (5+8*v)=0 ↔ G9 u v=0 := chart9.zero_iff u v
#print axioms identity9
#print axioms zeros9
def G10 (u v : ℤ) : ℤ := (2) * (u)^0 * (v)^0 + (6) * (u)^0 * (v)^1 + (4) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-12) * (u)^2 * (v)^0 + (-16) * (u)^3 * (v)^0
theorem identity10 (u v : ℤ) : F (1+4*u) (3+4*v) = (4)*G10 u v := by unfold F G10; ring
def chart10 : Chart F := ⟨1,3,4,4,G10,by norm_num,by norm_num,identity10⟩
theorem zeros10 (u v : ℤ) : F (1+4*u) (3+4*v)=0 ↔ G10 u v=0 := chart10.zero_iff u v
#print axioms identity10
#print axioms zeros10
def G11 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^0 + (6) * (u)^0 * (v)^1 + (8) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-24) * (u)^2 * (v)^0 + (-64) * (u)^3 * (v)^0
theorem identity11 (u v : ℤ) : F (1+8*u) (3+8*v) = (8)*G11 u v := by unfold F G11; ring
def chart11 : Chart F := ⟨1,3,8,8,G11,by norm_num,by norm_num,identity11⟩
theorem zeros11 (u v : ℤ) : F (1+8*u) (3+8*v)=0 ↔ G11 u v=0 := chart11.zero_iff u v
#print axioms identity11
#print axioms zeros11
def G12 (u v : ℤ) : ℤ := (6) * (u)^0 * (v)^0 + (14) * (u)^0 * (v)^1 + (8) * (u)^0 * (v)^2 + (-3) * (u)^1 * (v)^0 + (-24) * (u)^2 * (v)^0 + (-64) * (u)^3 * (v)^0
theorem identity12 (u v : ℤ) : F (1+8*u) (7+8*v) = (8)*G12 u v := by unfold F G12; ring
def chart12 : Chart F := ⟨1,7,8,8,G12,by norm_num,by norm_num,identity12⟩
theorem zeros12 (u v : ℤ) : F (1+8*u) (7+8*v)=0 ↔ G12 u v=0 := chart12.zero_iff u v
#print axioms identity12
#print axioms zeros12
def bounds : PerfectPower.ResidueAtlas.Bounds := ((-8,8),(-8,8))
def points : Finset (ℤ×ℤ) := {(0,0), (1,-1), (1,1), (4,-8), (4,8)}
theorem points_checked : boxZeros F bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -8≤x ∧ x≤8 ∧ -8≤y ∧ y≤8 ∧ F x y=0 := by
  rw [← points_checked];exact boxZeros_complete F bounds x y
#print axioms points_checked
#print axioms points_complete
end Branching_e98fae427c4c8b4b
