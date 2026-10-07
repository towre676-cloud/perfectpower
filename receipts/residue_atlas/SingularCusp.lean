import PerfectPower.ResidueAtlas
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_0c849f02429ccb98
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^2 + (-1) * (x)^3 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
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
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-2) * (u)^3 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(0)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,0,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2), (2,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-3) * (u)^2 * (v)^0 + (-2) * (u)^3 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(-3)*u+(2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,-3,2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(-3)*u+(2)*v := lift2_1.step (by norm_num) (by norm_num) u v
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
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 3 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked3 : rootTable F 8 = roots3 := by decide +kernel
def atlas3 : AtlasPacket F 8 := ⟨by norm_num, roots3, checked3, periodic3⟩
theorem complete3 (x y : ℤ) : (x % 8,y % 8) ∈ roots3 ↔ F x y % 8 = 0 := atlas3.complete x y
#print axioms periodic3
#print axioms checked3
#print axioms complete3
def lift3_0R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-4) * (u)^3 * (v)^0
theorem lift3_0_identity (u v : ℤ) : F (0+4*u) (0+4*v) =
    4*((0)+(0)*u+(0)*v)+4^2*lift3_0R u v := by unfold F lift3_0R; ring
def lift3_0 : LiftPacket F 2 4 0 0 := ⟨0,0,0,lift3_0R,lift3_0_identity⟩
theorem lift3_0_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift3_0.step (by norm_num) (by norm_num) u v
theorem lift3_0_children : childTable F 2 4 0 0 = {(0,0), (0,4), (4,0), (4,4)} := by decide +kernel
#print axioms lift3_0_identity
#print axioms lift3_0_complete
#print axioms lift3_0_children
def lift3_1R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-4) * (u)^3 * (v)^0
theorem lift3_1_identity (u v : ℤ) : F (0+4*u) (2+4*v) =
    4*((1)+(0)*u+(4)*v)+4^2*lift3_1R u v := by unfold F lift3_1R; ring
def lift3_1 : LiftPacket F 2 4 0 2 := ⟨1,0,4,lift3_1R,lift3_1_identity⟩
theorem lift3_1_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (1)+(0)*u+(4)*v := lift3_1.step (by norm_num) (by norm_num) u v
theorem lift3_1_children : childTable F 2 4 0 2 = ∅ := by decide +kernel
#print axioms lift3_1_identity
#print axioms lift3_1_complete
#print axioms lift3_1_children
def lift3_2R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-3) * (u)^2 * (v)^0 + (-4) * (u)^3 * (v)^0
theorem lift3_2_identity (u v : ℤ) : F (1+4*u) (1+4*v) =
    4*((0)+(-3)*u+(2)*v)+4^2*lift3_2R u v := by unfold F lift3_2R; ring
def lift3_2 : LiftPacket F 2 4 1 1 := ⟨0,-3,2,lift3_2R,lift3_2_identity⟩
theorem lift3_2_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (0)+(-3)*u+(2)*v := lift3_2.step (by norm_num) (by norm_num) u v
theorem lift3_2_children : childTable F 2 4 1 1 = {(1,1), (1,5)} := by decide +kernel
#print axioms lift3_2_identity
#print axioms lift3_2_complete
#print axioms lift3_2_children
def lift3_3R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-3) * (u)^2 * (v)^0 + (-4) * (u)^3 * (v)^0
theorem lift3_3_identity (u v : ℤ) : F (1+4*u) (3+4*v) =
    4*((2)+(-3)*u+(6)*v)+4^2*lift3_3R u v := by unfold F lift3_3R; ring
def lift3_3 : LiftPacket F 2 4 1 3 := ⟨2,-3,6,lift3_3R,lift3_3_identity⟩
theorem lift3_3_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (3+4*v) ↔
    (2 : ℤ) ∣ (2)+(-3)*u+(6)*v := lift3_3.step (by norm_num) (by norm_num) u v
theorem lift3_3_children : childTable F 2 4 1 3 = {(1,3), (1,7)} := by decide +kernel
#print axioms lift3_3_identity
#print axioms lift3_3_complete
#print axioms lift3_3_children
def lift3_4R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-6) * (u)^2 * (v)^0 + (-4) * (u)^3 * (v)^0
theorem lift3_4_identity (u v : ℤ) : F (2+4*u) (0+4*v) =
    4*((-2)+(-12)*u+(0)*v)+4^2*lift3_4R u v := by unfold F lift3_4R; ring
def lift3_4 : LiftPacket F 2 4 2 0 := ⟨-2,-12,0,lift3_4R,lift3_4_identity⟩
theorem lift3_4_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (-2)+(-12)*u+(0)*v := lift3_4.step (by norm_num) (by norm_num) u v
theorem lift3_4_children : childTable F 2 4 2 0 = {(2,0), (2,4), (6,0), (6,4)} := by decide +kernel
#print axioms lift3_4_identity
#print axioms lift3_4_complete
#print axioms lift3_4_children
def lift3_5R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-6) * (u)^2 * (v)^0 + (-4) * (u)^3 * (v)^0
theorem lift3_5_identity (u v : ℤ) : F (2+4*u) (2+4*v) =
    4*((-1)+(-12)*u+(4)*v)+4^2*lift3_5R u v := by unfold F lift3_5R; ring
def lift3_5 : LiftPacket F 2 4 2 2 := ⟨-1,-12,4,lift3_5R,lift3_5_identity⟩
theorem lift3_5_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (-1)+(-12)*u+(4)*v := lift3_5.step (by norm_num) (by norm_num) u v
theorem lift3_5_children : childTable F 2 4 2 2 = ∅ := by decide +kernel
#print axioms lift3_5_identity
#print axioms lift3_5_complete
#print axioms lift3_5_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-10,10),(-10,10))
theorem count_checked : (candidates atlas3 bounds).card = 85 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 8,y % 8) ∈ roots3 := atlas3.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1), (4,-8), (4,8)}
theorem points_checked : solutions atlas3 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -10 ≤ x ∧ x ≤ 10 ∧ -10 ≤ y ∧ y ≤ 10 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas3 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_0c849f02429ccb98
