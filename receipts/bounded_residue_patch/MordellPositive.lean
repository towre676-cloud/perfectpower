import PerfectPower.BoundedResiduePatch
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Patch_a61d1cd22fa5b32a
open PerfectPower.BoundedResiduePatch
def F (x y : ℤ) : ℤ := (2) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^2 + (-1) * (x)^3 * (y)^0
def R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-9) * (u)^2 * (v)^0 + (-7) * (u)^3 * (v)^0
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((0,35),(-220,220))
def points : Finset (ℤ × ℤ) := {(3,5)}
def candidates : Finset (ℤ × ℤ) := {(3,-191), (3,-142), (3,-93), (3,-44), (3,5), (3,54), (3,103), (3,152), (3,201), (10,-177), (10,-128), (10,-79), (10,-30), (10,19), (10,68), (10,117), (10,166), (10,215), (17,-212), (17,-163), (17,-114), (17,-65), (17,-16), (17,33), (17,82), (17,131), (17,180), (24,-198), (24,-149), (24,-100), (24,-51), (24,-2), (24,47), (24,96), (24,145), (24,194), (31,-184), (31,-135), (31,-86), (31,-37), (31,12), (31,61), (31,110), (31,159), (31,208)}
theorem taylor_identity (u v : ℤ) : F (3+7*u) (5+7*v) =
    7*(0+(-27)*u+(10)*v)+7^2*R u v := by
  unfold F R; ring
theorem vertical_unit : IsCoprime (7 : ℤ) (10 : ℤ) := by
  refine ⟨-7, 5, ?_⟩; decide +kernel
def taylor : TaylorPacket F 7 3 5 :=
  ⟨0, -27, 10, R, taylor_identity, vertical_unit⟩
theorem prime_checked : Nat.Prime 7 := by norm_num
theorem candidate_list_checked : lifts F bounds 7 3 5 = candidates := by decide +kernel
theorem point_list_checked : solutions F bounds 7 3 5 = points := by decide +kernel
def cover : CoverPacket F bounds 7 3 5 := ⟨points, point_list_checked⟩
theorem complete (x y : ℤ) : (x,y) ∈ points ↔
    (0 ≤ x ∧ x ≤ 35 ∧ -220 ≤ y ∧ y ≤ 220 ∧
     (7 : ℤ) ∣ x-3 ∧ (7 : ℤ) ∣ y-5 ∧ F x y = 0) := cover.complete x y
#print axioms taylor_identity
#print axioms vertical_unit
#print axioms prime_checked
#print axioms candidate_list_checked
#print axioms point_list_checked
#print axioms complete
def auxiliary0 (x y : ℤ) : ℤ := (115) * (x-(0))^0 * (y-(0))^0 + (-3) * (x-(0))^1 * (y-(0))^0 + (-5) * (x-(0))^0 * (y-(0))^1 + (-9) * (x-(0))^2 * (y-(0))^0
theorem auxiliary0_values : ∀ z ∈ points, auxiliary0 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary0_covers (x y : ℤ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 35) (hy0 : -220 ≤ y) (hy1 : y ≤ 220)
    (hxp : (7 : ℤ) ∣ x-3) (hyp : (7 : ℤ) ∣ y-5) (hF : F x y = 0) :
    auxiliary0 x y = 0 :=
  relation_on_box cover auxiliary0 auxiliary0_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary0_covers
def auxiliary1 (x y : ℤ) : ℤ := (3) * (x-(0))^0 * (y-(0))^0 + (-107) * (x-(0))^1 * (y-(0))^0 + (15) * (x-(0))^0 * (y-(0))^1 + (27) * (x-(0))^2 * (y-(0))^0
theorem auxiliary1_values : ∀ z ∈ points, auxiliary1 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary1_covers (x y : ℤ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 35) (hy0 : -220 ≤ y) (hy1 : y ≤ 220)
    (hxp : (7 : ℤ) ∣ x-3) (hyp : (7 : ℤ) ∣ y-5) (hF : F x y = 0) :
    auxiliary1 x y = 0 :=
  relation_on_box cover auxiliary1 auxiliary1_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary1_covers
def auxiliary2 (x y : ℤ) : ℤ := (5) * (x-(0))^0 * (y-(0))^0 + (15) * (x-(0))^1 * (y-(0))^0 + (-91) * (x-(0))^0 * (y-(0))^1 + (45) * (x-(0))^2 * (y-(0))^0
theorem auxiliary2_values : ∀ z ∈ points, auxiliary2 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary2_covers (x y : ℤ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 35) (hy0 : -220 ≤ y) (hy1 : y ≤ 220)
    (hxp : (7 : ℤ) ∣ x-3) (hyp : (7 : ℤ) ∣ y-5) (hF : F x y = 0) :
    auxiliary2 x y = 0 :=
  relation_on_box cover auxiliary2 auxiliary2_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary2_covers
def auxiliary3 (x y : ℤ) : ℤ := (9) * (x-(0))^0 * (y-(0))^0 + (27) * (x-(0))^1 * (y-(0))^0 + (45) * (x-(0))^0 * (y-(0))^1 + (-35) * (x-(0))^2 * (y-(0))^0
theorem auxiliary3_values : ∀ z ∈ points, auxiliary3 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary3_covers (x y : ℤ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 35) (hy0 : -220 ≤ y) (hy1 : y ≤ 220)
    (hxp : (7 : ℤ) ∣ x-3) (hyp : (7 : ℤ) ∣ y-5) (hF : F x y = 0) :
    auxiliary3 x y = 0 :=
  relation_on_box cover auxiliary3 auxiliary3_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary3_covers
end Patch_a61d1cd22fa5b32a
