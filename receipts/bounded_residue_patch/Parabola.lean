import PerfectPower.BoundedResiduePatch
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Patch_0aa81338e19792f6
open PerfectPower.BoundedResiduePatch
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (-1) * (x)^2 * (y)^0
def R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-10,10),(0,100))
def points : Finset (ℤ × ℤ) := {(-9,81), (-4,16), (1,1), (6,36)}
def candidates : Finset (ℤ × ℤ) := {(-9,6), (-9,31), (-9,56), (-9,81), (-4,16), (-4,41), (-4,66), (-4,91), (1,1), (1,26), (1,51), (1,76), (6,11), (6,36), (6,61), (6,86)}
theorem taylor_identity (u v : ℤ) : F (1+5*u) (1+5*v) =
    5*(0+(-2)*u+(1)*v)+5^2*R u v := by
  unfold F R; ring
theorem vertical_unit : IsCoprime (5 : ℤ) (1 : ℤ) := by
  refine ⟨0, 1, ?_⟩; decide +kernel
def taylor : TaylorPacket F 5 1 1 :=
  ⟨0, -2, 1, R, taylor_identity, vertical_unit⟩
theorem prime_checked : Nat.Prime 5 := by norm_num
theorem candidate_list_checked : lifts F bounds 5 1 1 = candidates := by decide +kernel
theorem point_list_checked : solutions F bounds 5 1 1 = points := by decide +kernel
def cover : CoverPacket F bounds 5 1 1 := ⟨points, point_list_checked⟩
theorem complete (x y : ℤ) : (x,y) ∈ points ↔
    (-10 ≤ x ∧ x ≤ 10 ∧ 0 ≤ y ∧ y ≤ 100 ∧
     (5 : ℤ) ∣ x-1 ∧ (5 : ℤ) ∣ y-1 ∧ F x y = 0) := cover.complete x y
#print axioms taylor_identity
#print axioms vertical_unit
#print axioms prime_checked
#print axioms candidate_list_checked
#print axioms point_list_checked
#print axioms complete
def auxiliary0 (x y : ℤ) : ℤ := (1) * (x-(0))^0 * (y-(0))^1 + (-1) * (x-(0))^2 * (y-(0))^0
theorem auxiliary0_values : ∀ z ∈ points, auxiliary0 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary0_covers (x y : ℤ)
    (hx0 : -10 ≤ x) (hx1 : x ≤ 10) (hy0 : 0 ≤ y) (hy1 : y ≤ 100)
    (hxp : (5 : ℤ) ∣ x-1) (hyp : (5 : ℤ) ∣ y-1) (hF : F x y = 0) :
    auxiliary0 x y = 0 :=
  relation_on_box cover auxiliary0 auxiliary0_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary0_covers
end Patch_0aa81338e19792f6
