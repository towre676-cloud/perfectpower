import PerfectPower.BoundedResiduePatch
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Patch_a917e754addd6052
open PerfectPower.BoundedResiduePatch
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^2 + (-1) * (x)^4 * (y)^0
def R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-6) * (u)^2 * (v)^0 + (-12) * (u)^3 * (v)^0 + (-9) * (u)^4 * (v)^0
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-8,8),(-70,70))
def points : Finset (ℤ × ℤ) := {(-8,64), (-5,25), (-2,4), (1,1), (4,16), (7,49)}
def candidates : Finset (ℤ × ℤ) := {(-8,-62), (-8,-53), (-8,-44), (-8,-35), (-8,-26), (-8,-17), (-8,-8), (-8,1), (-8,10), (-8,19), (-8,28), (-8,37), (-8,46), (-8,55), (-8,64), (-5,-65), (-5,-56), (-5,-47), (-5,-38), (-5,-29), (-5,-20), (-5,-11), (-5,-2), (-5,7), (-5,16), (-5,25), (-5,34), (-5,43), (-5,52), (-5,61), (-5,70), (-2,-68), (-2,-59), (-2,-50), (-2,-41), (-2,-32), (-2,-23), (-2,-14), (-2,-5), (-2,4), (-2,13), (-2,22), (-2,31), (-2,40), (-2,49), (-2,58), (-2,67), (1,-62), (1,-53), (1,-44), (1,-35), (1,-26), (1,-17), (1,-8), (1,1), (1,10), (1,19), (1,28), (1,37), (1,46), (1,55), (1,64), (4,-65), (4,-56), (4,-47), (4,-38), (4,-29), (4,-20), (4,-11), (4,-2), (4,7), (4,16), (4,25), (4,34), (4,43), (4,52), (4,61), (4,70), (7,-68), (7,-59), (7,-50), (7,-41), (7,-32), (7,-23), (7,-14), (7,-5), (7,4), (7,13), (7,22), (7,31), (7,40), (7,49), (7,58), (7,67)}
theorem taylor_identity (u v : ℤ) : F (1+3*u) (1+3*v) =
    3*(0+(-4)*u+(2)*v)+3^2*R u v := by
  unfold F R; ring
theorem vertical_unit : IsCoprime (3 : ℤ) (2 : ℤ) := by
  refine ⟨-1, 2, ?_⟩; decide +kernel
def taylor : TaylorPacket F 3 1 1 :=
  ⟨0, -4, 2, R, taylor_identity, vertical_unit⟩
theorem prime_checked : Nat.Prime 3 := by norm_num
theorem candidate_list_checked : lifts F bounds 3 1 1 = candidates := by decide +kernel
theorem point_list_checked : solutions F bounds 3 1 1 = points := by decide +kernel
def cover : CoverPacket F bounds 3 1 1 := ⟨points, point_list_checked⟩
theorem complete (x y : ℤ) : (x,y) ∈ points ↔
    (-8 ≤ x ∧ x ≤ 8 ∧ -70 ≤ y ∧ y ≤ 70 ∧
     (3 : ℤ) ∣ x-1 ∧ (3 : ℤ) ∣ y-1 ∧ F x y = 0) := cover.complete x y
#print axioms taylor_identity
#print axioms vertical_unit
#print axioms prime_checked
#print axioms candidate_list_checked
#print axioms point_list_checked
#print axioms complete
def auxiliary0 (x y : ℤ) : ℤ := (1) * (x-(0))^4 * (y-(0))^0 + (-1) * (x-(0))^0 * (y-(0))^2
theorem auxiliary0_values : ∀ z ∈ points, auxiliary0 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary0_covers (x y : ℤ)
    (hx0 : -8 ≤ x) (hx1 : x ≤ 8) (hy0 : -70 ≤ y) (hy1 : y ≤ 70)
    (hxp : (3 : ℤ) ∣ x-1) (hyp : (3 : ℤ) ∣ y-1) (hF : F x y = 0) :
    auxiliary0 x y = 0 :=
  relation_on_box cover auxiliary0 auxiliary0_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary0_covers
end Patch_a917e754addd6052
