import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_596ff67dd92f374a
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (-1) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 5 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,4), (3,4), (4,1)}
theorem periodic1 (x y : ℤ) : F x y % 5 = F (x % 5) (y % 5) % 5 := by
  change Int.ModEq 5 (F x y) (F (x % 5) (y % 5))
  have hx : Int.ModEq 5 x (x % 5) := (Int.mod_modEq x 5).symm
  have hy : Int.ModEq 5 y (y % 5) := (Int.mod_modEq y 5).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 5 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 5 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 5,y % 5) ∈ roots1 ↔ F x y % 5 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas1 bounds).card = 80000000000000000000000000000000000000008000000000000000000000000000000000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 5,y % 5) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
end Atlas_596ff67dd92f374a
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_c156fed1b8ab5d7e
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (-1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,2), (3,3)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := 0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(-1)*u+(1)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,-1,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(-1)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := 0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(-1)*u+(1)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,-1,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(-1)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (3,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 100000000000000000000000000000000000000010000000000000000000000000000000000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
end Atlas_c156fed1b8ab5d7e
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_538b30a2afaf1a40
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (-1) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,1)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,4), (3,0), (4,7), (5,7), (6,0), (7,4), (8,1)}
theorem periodic2 (x y : ℤ) : F x y % 9 = F (x % 9) (y % 9) % 9 := by
  change Int.ModEq 9 (F x y) (F (x % 9) (y % 9))
  have hx : Int.ModEq 9 x (x % 9) := (Int.mod_modEq x 9).symm
  have hy : Int.ModEq 9 y (y % 9) := (Int.mod_modEq y 9).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 9 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 9 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 9,y % 9) ∈ roots2 ↔ F x y % 9 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+3*u) (0+3*v) =
    3*((0)+(0)*u+(1)*v)+3^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 3 3 0 0 := ⟨0,0,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (0+3*u) (0+3*v) ↔
    (3 : ℤ) ∣ (0)+(0)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 3 3 0 0 = {(0,0), (3,0), (6,0)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+3*u) (1+3*v) =
    3*((0)+(-2)*u+(1)*v)+3^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 3 3 1 1 := ⟨0,-2,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (1+3*u) (1+3*v) ↔
    (3 : ℤ) ∣ (0)+(-2)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 3 3 1 1 = {(1,1), (4,7), (7,4)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def lift2_2R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_2_identity (u v : ℤ) : F (2+3*u) (1+3*v) =
    3*((-1)+(-4)*u+(1)*v)+3^2*lift2_2R u v := by unfold F lift2_2R; ring
def lift2_2 : LiftPacket F 3 3 2 1 := ⟨-1,-4,1,lift2_2R,lift2_2_identity⟩
theorem lift2_2_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (2+3*u) (1+3*v) ↔
    (3 : ℤ) ∣ (-1)+(-4)*u+(1)*v := lift2_2.step (by norm_num) (by norm_num) u v
theorem lift2_2_children : childTable F 3 3 2 1 = {(2,4), (5,7), (8,1)} := by decide +kernel
#print axioms lift2_2_identity
#print axioms lift2_2_complete
#print axioms lift2_2_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 44444444444444444444444444444444444444453333333333333333333333333333333333333335 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 9,y % 9) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
end Atlas_538b30a2afaf1a40
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_bb7361d83d1946b1
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (-1) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,0), (3,1)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(0)*u+(1)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,0,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (2,0)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(-2)*u+(1)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,-2,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(-2)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (3,1)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def roots3 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,4), (3,1), (4,0), (5,1), (6,4), (7,1)}
theorem periodic3 (x y : ℤ) : F x y % 8 = F (x % 8) (y % 8) % 8 := by
  change Int.ModEq 8 (F x y) (F (x % 8) (y % 8))
  have hx : Int.ModEq 8 x (x % 8) := (Int.mod_modEq x 8).symm
  have hy : Int.ModEq 8 y (y % 8) := (Int.mod_modEq y 8).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked3 : rootTable F 8 = roots3 := by decide +kernel
def atlas3 : AtlasPacket F 8 := ⟨by norm_num, roots3, checked3, periodic3⟩
theorem complete3 (x y : ℤ) : (x % 8,y % 8) ∈ roots3 ↔ F x y % 8 = 0 := atlas3.complete x y
#print axioms periodic3
#print axioms checked3
#print axioms complete3
def lift3_0R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift3_0_identity (u v : ℤ) : F (0+4*u) (0+4*v) =
    4*((0)+(0)*u+(1)*v)+4^2*lift3_0R u v := by unfold F lift3_0R; ring
def lift3_0 : LiftPacket F 2 4 0 0 := ⟨0,0,1,lift3_0R,lift3_0_identity⟩
theorem lift3_0_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(1)*v := lift3_0.step (by norm_num) (by norm_num) u v
theorem lift3_0_children : childTable F 2 4 0 0 = {(0,0), (4,0)} := by decide +kernel
#print axioms lift3_0_identity
#print axioms lift3_0_complete
#print axioms lift3_0_children
def lift3_1R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift3_1_identity (u v : ℤ) : F (1+4*u) (1+4*v) =
    4*((0)+(-2)*u+(1)*v)+4^2*lift3_1R u v := by unfold F lift3_1R; ring
def lift3_1 : LiftPacket F 2 4 1 1 := ⟨0,-2,1,lift3_1R,lift3_1_identity⟩
theorem lift3_1_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (0)+(-2)*u+(1)*v := lift3_1.step (by norm_num) (by norm_num) u v
theorem lift3_1_children : childTable F 2 4 1 1 = {(1,1), (5,1)} := by decide +kernel
#print axioms lift3_1_identity
#print axioms lift3_1_complete
#print axioms lift3_1_children
def lift3_2R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift3_2_identity (u v : ℤ) : F (2+4*u) (0+4*v) =
    4*((-1)+(-4)*u+(1)*v)+4^2*lift3_2R u v := by unfold F lift3_2R; ring
def lift3_2 : LiftPacket F 2 4 2 0 := ⟨-1,-4,1,lift3_2R,lift3_2_identity⟩
theorem lift3_2_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (2+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (-1)+(-4)*u+(1)*v := lift3_2.step (by norm_num) (by norm_num) u v
theorem lift3_2_children : childTable F 2 4 2 0 = {(2,4), (6,4)} := by decide +kernel
#print axioms lift3_2_identity
#print axioms lift3_2_complete
#print axioms lift3_2_children
def lift3_3R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift3_3_identity (u v : ℤ) : F (3+4*u) (1+4*v) =
    4*((-2)+(-6)*u+(1)*v)+4^2*lift3_3R u v := by unfold F lift3_3R; ring
def lift3_3 : LiftPacket F 2 4 3 1 := ⟨-2,-6,1,lift3_3R,lift3_3_identity⟩
theorem lift3_3_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (3+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (-2)+(-6)*u+(1)*v := lift3_3.step (by norm_num) (by norm_num) u v
theorem lift3_3_children : childTable F 2 4 3 1 = {(3,1), (7,1)} := by decide +kernel
#print axioms lift3_3_identity
#print axioms lift3_3_complete
#print axioms lift3_3_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas3 bounds).card = 50000000000000000000000000000000000000007500000000000000000000000000000000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 8,y % 8) ∈ roots3 := atlas3.source_survives x y hF
#print axioms source_survives
end Atlas_bb7361d83d1946b1
namespace Intersection_9ce721f6bd34defa
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_596ff67dd92f374a.F x y % 5 = 0) 5 := ofAtlas Atlas_596ff67dd92f374a.atlas1
def local1 : CoverPacket (fun x y => Atlas_c156fed1b8ab5d7e.F x y % 4 = 0) 4 := ofAtlas Atlas_c156fed1b8ab5d7e.atlas2
def local2 : CoverPacket (fun x y => Atlas_538b30a2afaf1a40.F x y % 9 = 0) 9 := ofAtlas Atlas_538b30a2afaf1a40.atlas2
def local3 : CoverPacket (fun x y => Atlas_bb7361d83d1946b1.F x y % 8 = 0) 8 := ofAtlas Atlas_bb7361d83d1946b1.atlas3
def group0_0 : CoverPacket (fun x y => Atlas_bb7361d83d1946b1.F x y % 8 = 0) 8 := local3
def group0_1 : CoverPacket (fun x y => (Atlas_bb7361d83d1946b1.F x y % 8 = 0) ∧ (Atlas_c156fed1b8ab5d7e.F x y % 4 = 0)) 8 := nested group0_0 local1 (by norm_num)
theorem group_roots0 : group0_1.roots = {(0,0), (1,1), (4,0), (5,1)} := by decide +kernel
#print axioms group_roots0
def group1_0 : CoverPacket (fun x y => Atlas_538b30a2afaf1a40.F x y % 9 = 0) 9 := local2
theorem group_roots1 : group1_0.roots = {(0,0), (1,1), (2,4), (3,0), (4,7), (5,7), (6,0), (7,4), (8,1)} := by decide +kernel
#print axioms group_roots1
def group2_0 : CoverPacket (fun x y => Atlas_596ff67dd92f374a.F x y % 5 = 0) 5 := local0
theorem group_roots2 : group2_0.roots = {(0,0), (1,1), (2,4), (3,4), (4,1)} := by decide +kernel
#print axioms group_roots2
def stage0 : CoverPacket (fun x y => (Atlas_bb7361d83d1946b1.F x y % 8 = 0) ∧ (Atlas_c156fed1b8ab5d7e.F x y % 4 = 0)) 8 := group0_1
theorem coprime1 : (8 : ℤ).natAbs.Coprime (9 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (8 : ℤ)*8+(-7)*9=1 := by decide +kernel
def stage1 : CoverPacket (fun x y => ((Atlas_bb7361d83d1946b1.F x y % 8 = 0) ∧ (Atlas_c156fed1b8ab5d7e.F x y % 4 = 0)) ∧ (Atlas_538b30a2afaf1a40.F x y % 9 = 0)) 72 := merge stage0 group1_0 8 (-7) coprime1 bezout1
#print axioms coprime1
#print axioms bezout1
theorem coprime2 : (72 : ℤ).natAbs.Coprime (5 : ℤ).natAbs := by decide +kernel
theorem bezout2 : (3 : ℤ)*72+(-43)*5=1 := by decide +kernel
def stage2 : CoverPacket (fun x y => (((Atlas_bb7361d83d1946b1.F x y % 8 = 0) ∧ (Atlas_c156fed1b8ab5d7e.F x y % 4 = 0)) ∧ (Atlas_538b30a2afaf1a40.F x y % 9 = 0)) ∧ (Atlas_596ff67dd92f374a.F x y % 5 = 0)) 360 := merge stage1 group2_0 3 (-43) coprime2 bezout2
#print axioms coprime2
#print axioms bezout2
def bounds : Bounds := ((-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
def S (x y : ℤ) : Prop := Atlas_596ff67dd92f374a.F x y = 0 ∧ Atlas_c156fed1b8ab5d7e.F x y = 0 ∧ Atlas_538b30a2afaf1a40.F x y = 0 ∧ Atlas_bb7361d83d1946b1.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 360,y % 360) ∈ stage2.roots ↔ (((Atlas_bb7361d83d1946b1.F x y % 8 = 0) ∧ (Atlas_c156fed1b8ab5d7e.F x y % 4 = 0)) ∧ (Atlas_538b30a2afaf1a40.F x y % 9 = 0)) ∧ (Atlas_596ff67dd92f374a.F x y % 5 = 0) := stage2.complete x y
theorem roots_count : stage2.roots.card = 180 := by decide +kernel
theorem count_checked : (candidates stage2 bounds).card = 555555555555555555555555555555555555555944444444444444444444444444444444444445 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : (((Atlas_bb7361d83d1946b1.F x y % 8 = 0) ∧ (Atlas_c156fed1b8ab5d7e.F x y % 4 = 0)) ∧ (Atlas_538b30a2afaf1a40.F x y % 9 = 0)) ∧ (Atlas_596ff67dd92f374a.F x y % 5 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1,h2,h3⟩
  simp only [h0, h1, h2, h3, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 360,y % 360) ∈ stage2.roots := (stage2.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
end Intersection_9ce721f6bd34defa
