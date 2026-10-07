import PerfectPower.BoundedResiduePatch
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Patch_bf06898f4a9888fb
open PerfectPower.BoundedResiduePatch
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^3 + (-1) * (x)^2 * (y)^0
def R (u v : ℤ) : ℤ := (3) * (u)^0 * (v)^2 + (5) * (u)^0 * (v)^3 + (-1) * (u)^2 * (v)^0
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-20,20),(-10,10))
def points : Finset (ℤ × ℤ) := {(0,1)}
def candidates : Finset (ℤ × ℤ) := {(-20,1), (-15,1), (-10,1), (-5,1), (0,1), (5,1), (10,1), (15,1), (20,1)}
theorem taylor_identity (u v : ℤ) : F (0+5*u) (1+5*v) =
    5*(0+(0)*u+(3)*v)+5^2*R u v := by
  unfold F R; ring
theorem vertical_unit : IsCoprime (5 : ℤ) (3 : ℤ) := by
  refine ⟨-1, 2, ?_⟩; decide +kernel
def taylor : TaylorPacket F 5 0 1 :=
  ⟨0, 0, 3, R, taylor_identity, vertical_unit⟩
theorem prime_checked : Nat.Prime 5 := by norm_num
theorem candidate_list_checked : lifts F bounds 5 0 1 = candidates := by decide +kernel
theorem point_list_checked : solutions F bounds 5 0 1 = points := by decide +kernel
def cover : CoverPacket F bounds 5 0 1 := ⟨points, point_list_checked⟩
theorem complete (x y : ℤ) : (x,y) ∈ points ↔
    (-20 ≤ x ∧ x ≤ 20 ∧ -10 ≤ y ∧ y ≤ 10 ∧
     (5 : ℤ) ∣ x-0 ∧ (5 : ℤ) ∣ y-1 ∧ F x y = 0) := cover.complete x y
#print axioms taylor_identity
#print axioms vertical_unit
#print axioms prime_checked
#print axioms candidate_list_checked
#print axioms point_list_checked
#print axioms complete
def auxiliary0 (x y : ℤ) : ℤ := (1) * (x-(0))^0 * (y-(0))^0 + (-1) * (x-(0))^0 * (y-(0))^1
theorem auxiliary0_values : ∀ z ∈ points, auxiliary0 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary0_covers (x y : ℤ)
    (hx0 : -20 ≤ x) (hx1 : x ≤ 20) (hy0 : -10 ≤ y) (hy1 : y ≤ 10)
    (hxp : (5 : ℤ) ∣ x-0) (hyp : (5 : ℤ) ∣ y-1) (hF : F x y = 0) :
    auxiliary0 x y = 0 :=
  relation_on_box cover auxiliary0 auxiliary0_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary0_covers
def auxiliary1 (x y : ℤ) : ℤ := (1) * (x-(0))^1 * (y-(0))^0
theorem auxiliary1_values : ∀ z ∈ points, auxiliary1 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary1_covers (x y : ℤ)
    (hx0 : -20 ≤ x) (hx1 : x ≤ 20) (hy0 : -10 ≤ y) (hy1 : y ≤ 10)
    (hxp : (5 : ℤ) ∣ x-0) (hyp : (5 : ℤ) ∣ y-1) (hF : F x y = 0) :
    auxiliary1 x y = 0 :=
  relation_on_box cover auxiliary1 auxiliary1_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary1_covers
def auxiliary2 (x y : ℤ) : ℤ := (1) * (x-(0))^2 * (y-(0))^0
theorem auxiliary2_values : ∀ z ∈ points, auxiliary2 z.1 z.2 = 0 := by decide +kernel
theorem auxiliary2_covers (x y : ℤ)
    (hx0 : -20 ≤ x) (hx1 : x ≤ 20) (hy0 : -10 ≤ y) (hy1 : y ≤ 10)
    (hxp : (5 : ℤ) ∣ x-0) (hyp : (5 : ℤ) ∣ y-1) (hF : F x y = 0) :
    auxiliary2 x y = 0 :=
  relation_on_box cover auxiliary2 auxiliary2_values x y hx0 hx1 hy0 hy1 hxp hyp hF
#print axioms auxiliary2_covers
end Patch_bf06898f4a9888fb
