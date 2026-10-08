import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_c0fbf715c4dbd83b
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^3 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (1,2)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,3), (0,6), (1,1), (1,8), (3,0), (3,3), (3,6), (4,1), (4,8), (6,0), (6,3), (6,6), (7,1), (7,8)}
theorem periodic2 (x y : ℤ) : F x y % 9 = F (x % 9) (y % 9) % 9 := by
  change Int.ModEq 9 (F x y) (F (x % 9) (y % 9))
  have hx : Int.ModEq 9 x (x % 9) := (Int.mod_modEq x 9).symm
  have hy : Int.ModEq 9 y (y % 9) := (Int.mod_modEq y 9).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 9 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 9 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 9,y % 9) ∈ roots2 ↔ F x y % 9 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (3) * (u)^3 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+3*u) (0+3*v) =
    3*((0)+(0)*u+(0)*v)+3^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 3 3 0 0 := ⟨0,0,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (0+3*u) (0+3*v) ↔
    (3 : ℤ) ∣ (0)+(0)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 3 3 0 0 = {(0,0), (0,3), (0,6), (3,0), (3,3), (3,6), (6,0), (6,3), (6,6)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (3) * (u)^2 * (v)^0 + (3) * (u)^3 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+3*u) (1+3*v) =
    3*((0)+(3)*u+(-2)*v)+3^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 3 3 1 1 := ⟨0,3,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (1+3*u) (1+3*v) ↔
    (3 : ℤ) ∣ (0)+(3)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 3 3 1 1 = {(1,1), (4,1), (7,1)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def lift2_2R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (3) * (u)^2 * (v)^0 + (3) * (u)^3 * (v)^0
theorem lift2_2_identity (u v : ℤ) : F (1+3*u) (2+3*v) =
    3*((-1)+(3)*u+(-4)*v)+3^2*lift2_2R u v := by unfold F lift2_2R; ring
def lift2_2 : LiftPacket F 3 3 1 2 := ⟨-1,3,-4,lift2_2R,lift2_2_identity⟩
theorem lift2_2_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (1+3*u) (2+3*v) ↔
    (3 : ℤ) ∣ (-1)+(3)*u+(-4)*v := lift2_2.step (by norm_num) (by norm_num) u v
theorem lift2_2_children : childTable F 3 3 1 2 = {(1,8), (4,8), (7,8)} := by decide +kernel
#print axioms lift2_2_identity
#print axioms lift2_2_complete
#print axioms lift2_2_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-5,5),(-5,5))
theorem count_checked : (candidates atlas2 bounds).card = 17 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 9,y % 9) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -5 ≤ x ∧ x ≤ 5 ∧ -5 ≤ y ∧ y ≤ 5 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_c0fbf715c4dbd83b
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_a00a21d7f9cdc589
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^3 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,2), (1,1), (1,3), (2,0), (2,2)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (2) * (u)^3 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(0)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,0,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2), (2,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (3) * (u)^2 * (v)^0 + (2) * (u)^3 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(3)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,3,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(3)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def roots3 : Finset (ℤ × ℤ) := {(0,0), (0,4), (1,1), (1,3), (1,5), (1,7), (2,0), (2,4), (4,0), (4,4), (6,0), (6,4)}
theorem periodic3 (x y : ℤ) : F x y % 8 = F (x % 8) (y % 8) % 8 := by
  change Int.ModEq 8 (F x y) (F (x % 8) (y % 8))
  have hx : Int.ModEq 8 x (x % 8) := (Int.mod_modEq x 8).symm
  have hy : Int.ModEq 8 y (y % 8) := (Int.mod_modEq y 8).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked3 : rootTable F 8 = roots3 := by decide +kernel
def atlas3 : AtlasPacket F 8 := ⟨by norm_num, roots3, checked3, periodic3⟩
theorem complete3 (x y : ℤ) : (x % 8,y % 8) ∈ roots3 ↔ F x y % 8 = 0 := atlas3.complete x y
#print axioms periodic3
#print axioms checked3
#print axioms complete3
def lift3_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (4) * (u)^3 * (v)^0
theorem lift3_0_identity (u v : ℤ) : F (0+4*u) (0+4*v) =
    4*((0)+(0)*u+(0)*v)+4^2*lift3_0R u v := by unfold F lift3_0R; ring
def lift3_0 : LiftPacket F 2 4 0 0 := ⟨0,0,0,lift3_0R,lift3_0_identity⟩
theorem lift3_0_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift3_0.step (by norm_num) (by norm_num) u v
theorem lift3_0_children : childTable F 2 4 0 0 = {(0,0), (0,4), (4,0), (4,4)} := by decide +kernel
#print axioms lift3_0_identity
#print axioms lift3_0_complete
#print axioms lift3_0_children
def lift3_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (4) * (u)^3 * (v)^0
theorem lift3_1_identity (u v : ℤ) : F (0+4*u) (2+4*v) =
    4*((-1)+(0)*u+(-4)*v)+4^2*lift3_1R u v := by unfold F lift3_1R; ring
def lift3_1 : LiftPacket F 2 4 0 2 := ⟨-1,0,-4,lift3_1R,lift3_1_identity⟩
theorem lift3_1_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (-1)+(0)*u+(-4)*v := lift3_1.step (by norm_num) (by norm_num) u v
theorem lift3_1_children : childTable F 2 4 0 2 = ∅ := by decide +kernel
#print axioms lift3_1_identity
#print axioms lift3_1_complete
#print axioms lift3_1_children
def lift3_2R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (3) * (u)^2 * (v)^0 + (4) * (u)^3 * (v)^0
theorem lift3_2_identity (u v : ℤ) : F (1+4*u) (1+4*v) =
    4*((0)+(3)*u+(-2)*v)+4^2*lift3_2R u v := by unfold F lift3_2R; ring
def lift3_2 : LiftPacket F 2 4 1 1 := ⟨0,3,-2,lift3_2R,lift3_2_identity⟩
theorem lift3_2_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (0)+(3)*u+(-2)*v := lift3_2.step (by norm_num) (by norm_num) u v
theorem lift3_2_children : childTable F 2 4 1 1 = {(1,1), (1,5)} := by decide +kernel
#print axioms lift3_2_identity
#print axioms lift3_2_complete
#print axioms lift3_2_children
def lift3_3R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (3) * (u)^2 * (v)^0 + (4) * (u)^3 * (v)^0
theorem lift3_3_identity (u v : ℤ) : F (1+4*u) (3+4*v) =
    4*((-2)+(3)*u+(-6)*v)+4^2*lift3_3R u v := by unfold F lift3_3R; ring
def lift3_3 : LiftPacket F 2 4 1 3 := ⟨-2,3,-6,lift3_3R,lift3_3_identity⟩
theorem lift3_3_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (3+4*v) ↔
    (2 : ℤ) ∣ (-2)+(3)*u+(-6)*v := lift3_3.step (by norm_num) (by norm_num) u v
theorem lift3_3_children : childTable F 2 4 1 3 = {(1,3), (1,7)} := by decide +kernel
#print axioms lift3_3_identity
#print axioms lift3_3_complete
#print axioms lift3_3_children
def lift3_4R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (6) * (u)^2 * (v)^0 + (4) * (u)^3 * (v)^0
theorem lift3_4_identity (u v : ℤ) : F (2+4*u) (0+4*v) =
    4*((2)+(12)*u+(0)*v)+4^2*lift3_4R u v := by unfold F lift3_4R; ring
def lift3_4 : LiftPacket F 2 4 2 0 := ⟨2,12,0,lift3_4R,lift3_4_identity⟩
theorem lift3_4_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (2)+(12)*u+(0)*v := lift3_4.step (by norm_num) (by norm_num) u v
theorem lift3_4_children : childTable F 2 4 2 0 = {(2,0), (2,4), (6,0), (6,4)} := by decide +kernel
#print axioms lift3_4_identity
#print axioms lift3_4_complete
#print axioms lift3_4_children
def lift3_5R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (6) * (u)^2 * (v)^0 + (4) * (u)^3 * (v)^0
theorem lift3_5_identity (u v : ℤ) : F (2+4*u) (2+4*v) =
    4*((1)+(12)*u+(-4)*v)+4^2*lift3_5R u v := by unfold F lift3_5R; ring
def lift3_5 : LiftPacket F 2 4 2 2 := ⟨1,12,-4,lift3_5R,lift3_5_identity⟩
theorem lift3_5_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (1)+(12)*u+(-4)*v := lift3_5.step (by norm_num) (by norm_num) u v
theorem lift3_5_children : childTable F 2 4 2 2 = ∅ := by decide +kernel
#print axioms lift3_5_identity
#print axioms lift3_5_complete
#print axioms lift3_5_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-5,5),(-5,5))
theorem count_checked : (candidates atlas3 bounds).card = 21 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 8,y % 8) ∈ roots3 := atlas3.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : solutions atlas3 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -5 ≤ x ∧ x ≤ 5 ∧ -5 ≤ y ∧ y ≤ 5 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas3 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_a00a21d7f9cdc589
namespace Intersection_7f09ec33c05a99ac
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_c0fbf715c4dbd83b.F x y % 9 = 0) 9 := ofAtlas Atlas_c0fbf715c4dbd83b.atlas2
def local1 : CoverPacket (fun x y => Atlas_a00a21d7f9cdc589.F x y % 8 = 0) 8 := ofAtlas Atlas_a00a21d7f9cdc589.atlas3
def group0_0 : CoverPacket (fun x y => Atlas_a00a21d7f9cdc589.F x y % 8 = 0) 8 := local1
theorem group_roots0 : group0_0.roots = {(0,0), (0,4), (1,1), (1,3), (1,5), (1,7), (2,0), (2,4), (4,0), (4,4), (6,0), (6,4)} := by decide +kernel
#print axioms group_roots0
def group1_0 : CoverPacket (fun x y => Atlas_c0fbf715c4dbd83b.F x y % 9 = 0) 9 := local0
theorem group_roots1 : group1_0.roots = {(0,0), (0,3), (0,6), (1,1), (1,8), (3,0), (3,3), (3,6), (4,1), (4,8), (6,0), (6,3), (6,6), (7,1), (7,8)} := by decide +kernel
#print axioms group_roots1
def stage0 : CoverPacket (fun x y => Atlas_a00a21d7f9cdc589.F x y % 8 = 0) 8 := group0_0
theorem coprime1 : (8 : ℤ).natAbs.Coprime (9 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (8 : ℤ)*8+(-7)*9=1 := by decide +kernel
def stage1 : CoverPacket (fun x y => (Atlas_a00a21d7f9cdc589.F x y % 8 = 0) ∧ (Atlas_c0fbf715c4dbd83b.F x y % 9 = 0)) 72 := merge stage0 group1_0 8 (-7) coprime1 bezout1
#print axioms coprime1
#print axioms bezout1
def bounds : Bounds := ((-5,5),(-5,5))
def S (x y : ℤ) : Prop := Atlas_c0fbf715c4dbd83b.F x y = 0 ∧ Atlas_a00a21d7f9cdc589.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 72,y % 72) ∈ stage1.roots ↔ (Atlas_a00a21d7f9cdc589.F x y % 8 = 0) ∧ (Atlas_c0fbf715c4dbd83b.F x y % 9 = 0) := stage1.complete x y
theorem roots_count : stage1.roots.card = 180 := by decide +kernel
theorem count_checked : (candidates stage1 bounds).card = 3 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : (Atlas_a00a21d7f9cdc589.F x y % 8 = 0) ∧ (Atlas_c0fbf715c4dbd83b.F x y % 9 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1⟩
  simp only [h0, h1, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 72,y % 72) ∈ stage1.roots := (stage1.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : solutions stage1 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -5≤x ∧ x≤5 ∧ -5≤y ∧ y≤5 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage1 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_7f09ec33c05a99ac
namespace PowerCharts_3a4c15f43f0e3a7b
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^3 * (y)^0
def bounds : Bounds := ((-5,5),(-5,5))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (1) * (n)^3 * (y)^0
theorem identity0 (n y : ℤ) : F (0+1*n) y=1*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 1 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+1*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 1*m ∣ F (0+1*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_7f09ec33c05a99ac.stage1 bounds 1 0
theorem count0 : candidates0.card=3 := by
  rw [candidates0,chart_count Intersection_7f09ec33c05a99ac.stage1 bounds 1 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def residue (i : Fin 1) : ℤ := 0
def P (i : Fin 1) (x y : ℤ) : Prop := ((Atlas_a00a21d7f9cdc589.F x y % 8 = 0) ∧ (Atlas_c0fbf715c4dbd83b.F x y % 9 = 0))
def cover : (i : Fin 1) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 72 := Fin.cases Intersection_7f09ec33c05a99ac.stage1 ((fun i => Fin.elim0 i))
theorem residue_canonical : ∀ i : Fin 1, 0≤residue i ∧ residue i<1 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 1 residue
theorem population_checked : allCandidates.card=3 := by
  rw [allCandidates,family_count cover bounds 1 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (True)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-5) (5)).product (Finset.Icc (-5) (5))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -5≤x ∧ x≤5 ∧ -5≤y ∧ y≤5 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
def auxiliary0 (x y : ℤ) : ℤ := (1) * (x-(0))^1 * (y-(0))^0 + (-1) * (x-(0))^2 * (y-(0))^0
theorem auxiliary0_values : ∀ z ∈ points, auxiliary0 z.1 z.2=0 := by decide +kernel
theorem auxiliary0_covers (x y : ℤ) (h : -5≤x ∧ x≤5 ∧ -5≤y ∧ y≤5 ∧ accepts x y) : auxiliary0 x y=0 := auxiliary0_values (x,y) ((points_complete x y).mpr h)
#print axioms auxiliary0_values
#print axioms auxiliary0_covers
end PowerCharts_3a4c15f43f0e3a7b
