import PerfectPower.BranchingResidueCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Branching_a57be3b9c3967b7c
open PerfectPower.BranchingResidueCharts
def F (x y : ℤ) : ℤ := (1) * (x)^1 * (y)^1
def G0 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^1
theorem identity0 (u v : ℤ) : F (0+1*u) (0+1*v) = (1)*G0 u v := by unfold F G0; ring
def chart0 : Chart F := ⟨0,0,1,1,G0,by norm_num,by norm_num,identity0⟩
theorem zeros0 (u v : ℤ) : F (0+1*u) (0+1*v)=0 ↔ G0 u v=0 := chart0.zero_iff u v
#print axioms identity0
#print axioms zeros0
def G1 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^1
theorem identity1 (u v : ℤ) : F (0+2*u) (0+2*v) = (4)*G1 u v := by unfold F G1; ring
def chart1 : Chart F := ⟨0,0,2,4,G1,by norm_num,by norm_num,identity1⟩
theorem zeros1 (u v : ℤ) : F (0+2*u) (0+2*v)=0 ↔ G1 u v=0 := chart1.zero_iff u v
#print axioms identity1
#print axioms zeros1
def G2 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^1
theorem identity2 (u v : ℤ) : F (0+4*u) (0+4*v) = (16)*G2 u v := by unfold F G2; ring
def chart2 : Chart F := ⟨0,0,4,16,G2,by norm_num,by norm_num,identity2⟩
theorem zeros2 (u v : ℤ) : F (0+4*u) (0+4*v)=0 ↔ G2 u v=0 := chart2.zero_iff u v
#print axioms identity2
#print axioms zeros2
def G3 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^1
theorem identity3 (u v : ℤ) : F (0+8*u) (0+8*v) = (64)*G3 u v := by unfold F G3; ring
def chart3 : Chart F := ⟨0,0,8,64,G3,by norm_num,by norm_num,identity3⟩
theorem zeros3 (u v : ℤ) : F (0+8*u) (0+8*v)=0 ↔ G3 u v=0 := chart3.zero_iff u v
#print axioms identity3
#print axioms zeros3
def G4 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^0 + (2) * (u)^1 * (v)^1
theorem identity4 (u v : ℤ) : F (0+8*u) (4+8*v) = (32)*G4 u v := by unfold F G4; ring
def chart4 : Chart F := ⟨0,4,8,32,G4,by norm_num,by norm_num,identity4⟩
theorem zeros4 (u v : ℤ) : F (0+8*u) (4+8*v)=0 ↔ G4 u v=0 := chart4.zero_iff u v
#print axioms identity4
#print axioms zeros4
def G5 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^1 + (2) * (u)^1 * (v)^1
theorem identity5 (u v : ℤ) : F (4+8*u) (0+8*v) = (32)*G5 u v := by unfold F G5; ring
def chart5 : Chart F := ⟨4,0,8,32,G5,by norm_num,by norm_num,identity5⟩
theorem zeros5 (u v : ℤ) : F (4+8*u) (0+8*v)=0 ↔ G5 u v=0 := chart5.zero_iff u v
#print axioms identity5
#print axioms zeros5
def G6 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^0 + (2) * (u)^1 * (v)^1
theorem identity6 (u v : ℤ) : F (0+4*u) (2+4*v) = (8)*G6 u v := by unfold F G6; ring
def chart6 : Chart F := ⟨0,2,4,8,G6,by norm_num,by norm_num,identity6⟩
theorem zeros6 (u v : ℤ) : F (0+4*u) (2+4*v)=0 ↔ G6 u v=0 := chart6.zero_iff u v
#print axioms identity6
#print axioms zeros6
def G7 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^0 + (4) * (u)^1 * (v)^1
theorem identity7 (u v : ℤ) : F (0+8*u) (2+8*v) = (16)*G7 u v := by unfold F G7; ring
def chart7 : Chart F := ⟨0,2,8,16,G7,by norm_num,by norm_num,identity7⟩
theorem zeros7 (u v : ℤ) : F (0+8*u) (2+8*v)=0 ↔ G7 u v=0 := chart7.zero_iff u v
#print axioms identity7
#print axioms zeros7
def G8 (u v : ℤ) : ℤ := (3) * (u)^1 * (v)^0 + (4) * (u)^1 * (v)^1
theorem identity8 (u v : ℤ) : F (0+8*u) (6+8*v) = (16)*G8 u v := by unfold F G8; ring
def chart8 : Chart F := ⟨0,6,8,16,G8,by norm_num,by norm_num,identity8⟩
theorem zeros8 (u v : ℤ) : F (0+8*u) (6+8*v)=0 ↔ G8 u v=0 := chart8.zero_iff u v
#print axioms identity8
#print axioms zeros8
def G9 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^1 + (2) * (u)^1 * (v)^1
theorem identity9 (u v : ℤ) : F (2+4*u) (0+4*v) = (8)*G9 u v := by unfold F G9; ring
def chart9 : Chart F := ⟨2,0,4,8,G9,by norm_num,by norm_num,identity9⟩
theorem zeros9 (u v : ℤ) : F (2+4*u) (0+4*v)=0 ↔ G9 u v=0 := chart9.zero_iff u v
#print axioms identity9
#print axioms zeros9
def G10 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^1 + (4) * (u)^1 * (v)^1
theorem identity10 (u v : ℤ) : F (2+8*u) (0+8*v) = (16)*G10 u v := by unfold F G10; ring
def chart10 : Chart F := ⟨2,0,8,16,G10,by norm_num,by norm_num,identity10⟩
theorem zeros10 (u v : ℤ) : F (2+8*u) (0+8*v)=0 ↔ G10 u v=0 := chart10.zero_iff u v
#print axioms identity10
#print axioms zeros10
def G11 (u v : ℤ) : ℤ := (3) * (u)^0 * (v)^1 + (4) * (u)^1 * (v)^1
theorem identity11 (u v : ℤ) : F (6+8*u) (0+8*v) = (16)*G11 u v := by unfold F G11; ring
def chart11 : Chart F := ⟨6,0,8,16,G11,by norm_num,by norm_num,identity11⟩
theorem zeros11 (u v : ℤ) : F (6+8*u) (0+8*v)=0 ↔ G11 u v=0 := chart11.zero_iff u v
#print axioms identity11
#print axioms zeros11
def G12 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^0 + (2) * (u)^1 * (v)^1
theorem identity12 (u v : ℤ) : F (0+2*u) (1+2*v) = (2)*G12 u v := by unfold F G12; ring
def chart12 : Chart F := ⟨0,1,2,2,G12,by norm_num,by norm_num,identity12⟩
theorem zeros12 (u v : ℤ) : F (0+2*u) (1+2*v)=0 ↔ G12 u v=0 := chart12.zero_iff u v
#print axioms identity12
#print axioms zeros12
def G13 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^0 + (4) * (u)^1 * (v)^1
theorem identity13 (u v : ℤ) : F (0+4*u) (1+4*v) = (4)*G13 u v := by unfold F G13; ring
def chart13 : Chart F := ⟨0,1,4,4,G13,by norm_num,by norm_num,identity13⟩
theorem zeros13 (u v : ℤ) : F (0+4*u) (1+4*v)=0 ↔ G13 u v=0 := chart13.zero_iff u v
#print axioms identity13
#print axioms zeros13
def G14 (u v : ℤ) : ℤ := (1) * (u)^1 * (v)^0 + (8) * (u)^1 * (v)^1
theorem identity14 (u v : ℤ) : F (0+8*u) (1+8*v) = (8)*G14 u v := by unfold F G14; ring
def chart14 : Chart F := ⟨0,1,8,8,G14,by norm_num,by norm_num,identity14⟩
theorem zeros14 (u v : ℤ) : F (0+8*u) (1+8*v)=0 ↔ G14 u v=0 := chart14.zero_iff u v
#print axioms identity14
#print axioms zeros14
def G15 (u v : ℤ) : ℤ := (5) * (u)^1 * (v)^0 + (8) * (u)^1 * (v)^1
theorem identity15 (u v : ℤ) : F (0+8*u) (5+8*v) = (8)*G15 u v := by unfold F G15; ring
def chart15 : Chart F := ⟨0,5,8,8,G15,by norm_num,by norm_num,identity15⟩
theorem zeros15 (u v : ℤ) : F (0+8*u) (5+8*v)=0 ↔ G15 u v=0 := chart15.zero_iff u v
#print axioms identity15
#print axioms zeros15
def G16 (u v : ℤ) : ℤ := (3) * (u)^1 * (v)^0 + (4) * (u)^1 * (v)^1
theorem identity16 (u v : ℤ) : F (0+4*u) (3+4*v) = (4)*G16 u v := by unfold F G16; ring
def chart16 : Chart F := ⟨0,3,4,4,G16,by norm_num,by norm_num,identity16⟩
theorem zeros16 (u v : ℤ) : F (0+4*u) (3+4*v)=0 ↔ G16 u v=0 := chart16.zero_iff u v
#print axioms identity16
#print axioms zeros16
def G17 (u v : ℤ) : ℤ := (3) * (u)^1 * (v)^0 + (8) * (u)^1 * (v)^1
theorem identity17 (u v : ℤ) : F (0+8*u) (3+8*v) = (8)*G17 u v := by unfold F G17; ring
def chart17 : Chart F := ⟨0,3,8,8,G17,by norm_num,by norm_num,identity17⟩
theorem zeros17 (u v : ℤ) : F (0+8*u) (3+8*v)=0 ↔ G17 u v=0 := chart17.zero_iff u v
#print axioms identity17
#print axioms zeros17
def G18 (u v : ℤ) : ℤ := (7) * (u)^1 * (v)^0 + (8) * (u)^1 * (v)^1
theorem identity18 (u v : ℤ) : F (0+8*u) (7+8*v) = (8)*G18 u v := by unfold F G18; ring
def chart18 : Chart F := ⟨0,7,8,8,G18,by norm_num,by norm_num,identity18⟩
theorem zeros18 (u v : ℤ) : F (0+8*u) (7+8*v)=0 ↔ G18 u v=0 := chart18.zero_iff u v
#print axioms identity18
#print axioms zeros18
def G19 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^1 + (2) * (u)^1 * (v)^1
theorem identity19 (u v : ℤ) : F (1+2*u) (0+2*v) = (2)*G19 u v := by unfold F G19; ring
def chart19 : Chart F := ⟨1,0,2,2,G19,by norm_num,by norm_num,identity19⟩
theorem zeros19 (u v : ℤ) : F (1+2*u) (0+2*v)=0 ↔ G19 u v=0 := chart19.zero_iff u v
#print axioms identity19
#print axioms zeros19
def G20 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^1 + (4) * (u)^1 * (v)^1
theorem identity20 (u v : ℤ) : F (1+4*u) (0+4*v) = (4)*G20 u v := by unfold F G20; ring
def chart20 : Chart F := ⟨1,0,4,4,G20,by norm_num,by norm_num,identity20⟩
theorem zeros20 (u v : ℤ) : F (1+4*u) (0+4*v)=0 ↔ G20 u v=0 := chart20.zero_iff u v
#print axioms identity20
#print axioms zeros20
def G21 (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^1 + (8) * (u)^1 * (v)^1
theorem identity21 (u v : ℤ) : F (1+8*u) (0+8*v) = (8)*G21 u v := by unfold F G21; ring
def chart21 : Chart F := ⟨1,0,8,8,G21,by norm_num,by norm_num,identity21⟩
theorem zeros21 (u v : ℤ) : F (1+8*u) (0+8*v)=0 ↔ G21 u v=0 := chart21.zero_iff u v
#print axioms identity21
#print axioms zeros21
def G22 (u v : ℤ) : ℤ := (5) * (u)^0 * (v)^1 + (8) * (u)^1 * (v)^1
theorem identity22 (u v : ℤ) : F (5+8*u) (0+8*v) = (8)*G22 u v := by unfold F G22; ring
def chart22 : Chart F := ⟨5,0,8,8,G22,by norm_num,by norm_num,identity22⟩
theorem zeros22 (u v : ℤ) : F (5+8*u) (0+8*v)=0 ↔ G22 u v=0 := chart22.zero_iff u v
#print axioms identity22
#print axioms zeros22
def G23 (u v : ℤ) : ℤ := (3) * (u)^0 * (v)^1 + (4) * (u)^1 * (v)^1
theorem identity23 (u v : ℤ) : F (3+4*u) (0+4*v) = (4)*G23 u v := by unfold F G23; ring
def chart23 : Chart F := ⟨3,0,4,4,G23,by norm_num,by norm_num,identity23⟩
theorem zeros23 (u v : ℤ) : F (3+4*u) (0+4*v)=0 ↔ G23 u v=0 := chart23.zero_iff u v
#print axioms identity23
#print axioms zeros23
def G24 (u v : ℤ) : ℤ := (3) * (u)^0 * (v)^1 + (8) * (u)^1 * (v)^1
theorem identity24 (u v : ℤ) : F (3+8*u) (0+8*v) = (8)*G24 u v := by unfold F G24; ring
def chart24 : Chart F := ⟨3,0,8,8,G24,by norm_num,by norm_num,identity24⟩
theorem zeros24 (u v : ℤ) : F (3+8*u) (0+8*v)=0 ↔ G24 u v=0 := chart24.zero_iff u v
#print axioms identity24
#print axioms zeros24
def G25 (u v : ℤ) : ℤ := (7) * (u)^0 * (v)^1 + (8) * (u)^1 * (v)^1
theorem identity25 (u v : ℤ) : F (7+8*u) (0+8*v) = (8)*G25 u v := by unfold F G25; ring
def chart25 : Chart F := ⟨7,0,8,8,G25,by norm_num,by norm_num,identity25⟩
theorem zeros25 (u v : ℤ) : F (7+8*u) (0+8*v)=0 ↔ G25 u v=0 := chart25.zero_iff u v
#print axioms identity25
#print axioms zeros25
def bounds : PerfectPower.ResidueAtlas.Bounds := ((-8,8),(-8,8))
def points : Finset (ℤ×ℤ) := {(-8,0), (-7,0), (-6,0), (-5,0), (-4,0), (-3,0), (-2,0), (-1,0), (0,-8), (0,-7), (0,-6), (0,-5), (0,-4), (0,-3), (0,-2), (0,-1), (0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0), (8,0)}
theorem points_checked : boxZeros F bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -8≤x ∧ x≤8 ∧ -8≤y ∧ y≤8 ∧ F x y=0 := by
  rw [← points_checked];exact boxZeros_complete F bounds x y
#print axioms points_checked
#print axioms points_complete
end Branching_a57be3b9c3967b7c
