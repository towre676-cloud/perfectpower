import PerfectPower.BoundedResiduePatch
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Patch_599e4a8825bed45a
open PerfectPower.BoundedResiduePatch
def F (x y : ℤ) : ℤ := (2) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^2 + (-1) * (x)^3 * (y)^0
def R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-9) * (u)^2 * (v)^0 + (-7) * (u)^3 * (v)^0
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((10,20),(-20,20))
def points : Finset (ℤ × ℤ) := ∅
def candidates : Finset (ℤ × ℤ) := {(10,19), (17,-16)}
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
    (10 ≤ x ∧ x ≤ 20 ∧ -20 ≤ y ∧ y ≤ 20 ∧
     (7 : ℤ) ∣ x-3 ∧ (7 : ℤ) ∣ y-5 ∧ F x y = 0) := cover.complete x y
#print axioms taylor_identity
#print axioms vertical_unit
#print axioms prime_checked
#print axioms candidate_list_checked
#print axioms point_list_checked
#print axioms complete
theorem no_solution (x y : ℤ)
    (hx0 : 10 ≤ x) (hx1 : x ≤ 20) (hy0 : -20 ≤ y) (hy1 : y ≤ 20)
    (hxp : (7 : ℤ) ∣ x-3) (hyp : (7 : ℤ) ∣ y-5) : F x y ≠ 0 :=
  empty_box cover rfl x y hx0 hx1 hy0 hy1 hxp hyp
#print axioms no_solution
end Patch_599e4a8825bed45a
