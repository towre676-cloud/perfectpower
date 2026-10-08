import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_012846d540e19d19
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,3), (2,2), (3,1)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := 0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(1)*u+(1)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,1,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := 0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((1)+(1)*u+(1)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨1,1,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (1)+(1)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,3), (3,1)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-8,8),(-8,8))
theorem count_checked : (candidates atlas2 bounds).card = 73 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-8,8), (-7,7), (-6,6), (-5,5), (-4,4), (-3,3), (-2,2), (-1,1), (0,0), (1,-1), (2,-2), (3,-3), (4,-4), (5,-5), (6,-6), (7,-7), (8,-8)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -8 ≤ x ∧ x ≤ 8 ∧ -8 ≤ y ∧ y ≤ 8 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_012846d540e19d19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_2aab847060209566
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^2 + (-1) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,2), (1,1), (1,3), (2,0), (2,2), (3,1), (3,3)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(0)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,0,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2), (2,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(-2)*u+(2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,-2,2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(-2)*u+(2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3), (3,1), (3,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def roots3 : Finset (ℤ × ℤ) := {(0,0), (0,4), (1,1), (1,3), (1,5), (1,7), (2,2), (2,6), (3,1), (3,3), (3,5), (3,7), (4,0), (4,4), (5,1), (5,3), (5,5), (5,7), (6,2), (6,6), (7,1), (7,3), (7,5), (7,7)}
theorem periodic3 (x y : ℤ) : F x y % 8 = F (x % 8) (y % 8) % 8 := by
  change Int.ModEq 8 (F x y) (F (x % 8) (y % 8))
  have hx : Int.ModEq 8 x (x % 8) := (Int.mod_modEq x 8).symm
  have hy : Int.ModEq 8 y (y % 8) := (Int.mod_modEq y 8).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked3 : rootTable F 8 = roots3 := by decide +kernel
def atlas3 : AtlasPacket F 8 := ⟨by norm_num, roots3, checked3, periodic3⟩
theorem complete3 (x y : ℤ) : (x % 8,y % 8) ∈ roots3 ↔ F x y % 8 = 0 := atlas3.complete x y
#print axioms periodic3
#print axioms checked3
#print axioms complete3
def lift3_0R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_0_identity (u v : ℤ) : F (0+4*u) (0+4*v) =
    4*((0)+(0)*u+(0)*v)+4^2*lift3_0R u v := by unfold F lift3_0R; ring
def lift3_0 : LiftPacket F 2 4 0 0 := ⟨0,0,0,lift3_0R,lift3_0_identity⟩
theorem lift3_0_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift3_0.step (by norm_num) (by norm_num) u v
theorem lift3_0_children : childTable F 2 4 0 0 = {(0,0), (0,4), (4,0), (4,4)} := by decide +kernel
#print axioms lift3_0_identity
#print axioms lift3_0_complete
#print axioms lift3_0_children
def lift3_1R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_1_identity (u v : ℤ) : F (0+4*u) (2+4*v) =
    4*((1)+(0)*u+(4)*v)+4^2*lift3_1R u v := by unfold F lift3_1R; ring
def lift3_1 : LiftPacket F 2 4 0 2 := ⟨1,0,4,lift3_1R,lift3_1_identity⟩
theorem lift3_1_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (1)+(0)*u+(4)*v := lift3_1.step (by norm_num) (by norm_num) u v
theorem lift3_1_children : childTable F 2 4 0 2 = ∅ := by decide +kernel
#print axioms lift3_1_identity
#print axioms lift3_1_complete
#print axioms lift3_1_children
def lift3_2R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_2_identity (u v : ℤ) : F (1+4*u) (1+4*v) =
    4*((0)+(-2)*u+(2)*v)+4^2*lift3_2R u v := by unfold F lift3_2R; ring
def lift3_2 : LiftPacket F 2 4 1 1 := ⟨0,-2,2,lift3_2R,lift3_2_identity⟩
theorem lift3_2_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (0)+(-2)*u+(2)*v := lift3_2.step (by norm_num) (by norm_num) u v
theorem lift3_2_children : childTable F 2 4 1 1 = {(1,1), (1,5), (5,1), (5,5)} := by decide +kernel
#print axioms lift3_2_identity
#print axioms lift3_2_complete
#print axioms lift3_2_children
def lift3_3R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_3_identity (u v : ℤ) : F (1+4*u) (3+4*v) =
    4*((2)+(-2)*u+(6)*v)+4^2*lift3_3R u v := by unfold F lift3_3R; ring
def lift3_3 : LiftPacket F 2 4 1 3 := ⟨2,-2,6,lift3_3R,lift3_3_identity⟩
theorem lift3_3_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (3+4*v) ↔
    (2 : ℤ) ∣ (2)+(-2)*u+(6)*v := lift3_3.step (by norm_num) (by norm_num) u v
theorem lift3_3_children : childTable F 2 4 1 3 = {(1,3), (1,7), (5,3), (5,7)} := by decide +kernel
#print axioms lift3_3_identity
#print axioms lift3_3_complete
#print axioms lift3_3_children
def lift3_4R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_4_identity (u v : ℤ) : F (2+4*u) (0+4*v) =
    4*((-1)+(-4)*u+(0)*v)+4^2*lift3_4R u v := by unfold F lift3_4R; ring
def lift3_4 : LiftPacket F 2 4 2 0 := ⟨-1,-4,0,lift3_4R,lift3_4_identity⟩
theorem lift3_4_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (-1)+(-4)*u+(0)*v := lift3_4.step (by norm_num) (by norm_num) u v
theorem lift3_4_children : childTable F 2 4 2 0 = ∅ := by decide +kernel
#print axioms lift3_4_identity
#print axioms lift3_4_complete
#print axioms lift3_4_children
def lift3_5R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_5_identity (u v : ℤ) : F (2+4*u) (2+4*v) =
    4*((0)+(-4)*u+(4)*v)+4^2*lift3_5R u v := by unfold F lift3_5R; ring
def lift3_5 : LiftPacket F 2 4 2 2 := ⟨0,-4,4,lift3_5R,lift3_5_identity⟩
theorem lift3_5_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (0)+(-4)*u+(4)*v := lift3_5.step (by norm_num) (by norm_num) u v
theorem lift3_5_children : childTable F 2 4 2 2 = {(2,2), (2,6), (6,2), (6,6)} := by decide +kernel
#print axioms lift3_5_identity
#print axioms lift3_5_complete
#print axioms lift3_5_children
def lift3_6R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_6_identity (u v : ℤ) : F (3+4*u) (1+4*v) =
    4*((-2)+(-6)*u+(2)*v)+4^2*lift3_6R u v := by unfold F lift3_6R; ring
def lift3_6 : LiftPacket F 2 4 3 1 := ⟨-2,-6,2,lift3_6R,lift3_6_identity⟩
theorem lift3_6_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (3+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (-2)+(-6)*u+(2)*v := lift3_6.step (by norm_num) (by norm_num) u v
theorem lift3_6_children : childTable F 2 4 3 1 = {(3,1), (3,5), (7,1), (7,5)} := by decide +kernel
#print axioms lift3_6_identity
#print axioms lift3_6_complete
#print axioms lift3_6_children
def lift3_7R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift3_7_identity (u v : ℤ) : F (3+4*u) (3+4*v) =
    4*((0)+(-6)*u+(6)*v)+4^2*lift3_7R u v := by unfold F lift3_7R; ring
def lift3_7 : LiftPacket F 2 4 3 3 := ⟨0,-6,6,lift3_7R,lift3_7_identity⟩
theorem lift3_7_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (3+4*u) (3+4*v) ↔
    (2 : ℤ) ∣ (0)+(-6)*u+(6)*v := lift3_7.step (by norm_num) (by norm_num) u v
theorem lift3_7_children : childTable F 2 4 3 3 = {(3,3), (3,7), (7,3), (7,7)} := by decide +kernel
#print axioms lift3_7_identity
#print axioms lift3_7_complete
#print axioms lift3_7_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-8,8),(-8,8))
theorem count_checked : (candidates atlas3 bounds).card = 105 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 8,y % 8) ∈ roots3 := atlas3.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-8,-8), (-8,8), (-7,-7), (-7,7), (-6,-6), (-6,6), (-5,-5), (-5,5), (-4,-4), (-4,4), (-3,-3), (-3,3), (-2,-2), (-2,2), (-1,-1), (-1,1), (0,0), (1,-1), (1,1), (2,-2), (2,2), (3,-3), (3,3), (4,-4), (4,4), (5,-5), (5,5), (6,-6), (6,6), (7,-7), (7,7), (8,-8), (8,8)}
theorem points_checked : solutions atlas3 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -8 ≤ x ∧ x ≤ 8 ∧ -8 ≤ y ∧ y ≤ 8 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas3 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_2aab847060209566
namespace Intersection_38d264812f7a543f
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_012846d540e19d19.F x y % 4 = 0) 4 := ofAtlas Atlas_012846d540e19d19.atlas2
def local1 : CoverPacket (fun x y => Atlas_2aab847060209566.F x y % 8 = 0) 8 := ofAtlas Atlas_2aab847060209566.atlas3
def group0_0 : CoverPacket (fun x y => Atlas_2aab847060209566.F x y % 8 = 0) 8 := local1
def group0_1 : CoverPacket (fun x y => (Atlas_2aab847060209566.F x y % 8 = 0) ∧ (Atlas_012846d540e19d19.F x y % 4 = 0)) 8 := nested group0_0 local0 (by norm_num)
theorem group_roots0 : group0_1.roots = {(0,0), (0,4), (1,3), (1,7), (2,2), (2,6), (3,1), (3,5), (4,0), (4,4), (5,3), (5,7), (6,2), (6,6), (7,1), (7,5)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => (Atlas_2aab847060209566.F x y % 8 = 0) ∧ (Atlas_012846d540e19d19.F x y % 4 = 0)) 8 := group0_1
def bounds : Bounds := ((-8,8),(-8,8))
def S (x y : ℤ) : Prop := Atlas_012846d540e19d19.F x y = 0 ∧ Atlas_2aab847060209566.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 8,y % 8) ∈ stage0.roots ↔ (Atlas_2aab847060209566.F x y % 8 = 0) ∧ (Atlas_012846d540e19d19.F x y % 4 = 0) := stage0.complete x y
theorem roots_count : stage0.roots.card = 16 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 73 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : (Atlas_2aab847060209566.F x y % 8 = 0) ∧ (Atlas_012846d540e19d19.F x y % 4 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1⟩
  simp only [h0, h1, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 8,y % 8) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-8,8), (-7,7), (-6,6), (-5,5), (-4,4), (-3,3), (-2,2), (-1,1), (0,0), (1,-1), (2,-2), (3,-3), (4,-4), (5,-5), (6,-6), (7,-7), (8,-8)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -8≤x ∧ x≤8 ∧ -8≤y ∧ y≤8 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_38d264812f7a543f
