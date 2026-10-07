import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasCRT
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_96fd8e69568bcedf
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
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem count_checked : (candidates atlas3 bounds).card = 500000000000750000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 8,y % 8) ∈ roots3 := atlas3.source_survives x y hF
#print axioms source_survives
end Atlas_96fd8e69568bcedf
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_fe4f1f7fe0f9852d
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
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 444444444445333333333335 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 9,y % 9) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
end Atlas_fe4f1f7fe0f9852d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_0d3f0fda0446828b
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
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,4), (3,9), (4,16), (5,0), (6,11), (7,24), (8,14), (9,6), (10,0), (11,21), (12,19), (13,19), (14,21), (15,0), (16,6), (17,14), (18,24), (19,11), (20,0), (21,16), (22,9), (23,4), (24,1)}
theorem periodic2 (x y : ℤ) : F x y % 25 = F (x % 25) (y % 25) % 25 := by
  change Int.ModEq 25 (F x y) (F (x % 25) (y % 25))
  have hx : Int.ModEq 25 x (x % 25) := (Int.mod_modEq x 25).symm
  have hy : Int.ModEq 25 y (y % 25) := (Int.mod_modEq y 25).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 25 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 25 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 25,y % 25) ∈ roots2 ↔ F x y % 25 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+5*u) (0+5*v) =
    5*((0)+(0)*u+(1)*v)+5^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 5 5 0 0 := ⟨0,0,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (5*5 : ℤ) ∣ F (0+5*u) (0+5*v) ↔
    (5 : ℤ) ∣ (0)+(0)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 5 5 0 0 = {(0,0), (5,0), (10,0), (15,0), (20,0)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+5*u) (1+5*v) =
    5*((0)+(-2)*u+(1)*v)+5^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 5 5 1 1 := ⟨0,-2,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (5*5 : ℤ) ∣ F (1+5*u) (1+5*v) ↔
    (5 : ℤ) ∣ (0)+(-2)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 5 5 1 1 = {(1,1), (6,11), (11,21), (16,6), (21,16)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def lift2_2R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_2_identity (u v : ℤ) : F (2+5*u) (4+5*v) =
    5*((0)+(-4)*u+(1)*v)+5^2*lift2_2R u v := by unfold F lift2_2R; ring
def lift2_2 : LiftPacket F 5 5 2 4 := ⟨0,-4,1,lift2_2R,lift2_2_identity⟩
theorem lift2_2_complete (u v : ℤ) : (5*5 : ℤ) ∣ F (2+5*u) (4+5*v) ↔
    (5 : ℤ) ∣ (0)+(-4)*u+(1)*v := lift2_2.step (by norm_num) (by norm_num) u v
theorem lift2_2_children : childTable F 5 5 2 4 = {(2,4), (7,24), (12,19), (17,14), (22,9)} := by decide +kernel
#print axioms lift2_2_identity
#print axioms lift2_2_complete
#print axioms lift2_2_children
def lift2_3R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_3_identity (u v : ℤ) : F (3+5*u) (4+5*v) =
    5*((-1)+(-6)*u+(1)*v)+5^2*lift2_3R u v := by unfold F lift2_3R; ring
def lift2_3 : LiftPacket F 5 5 3 4 := ⟨-1,-6,1,lift2_3R,lift2_3_identity⟩
theorem lift2_3_complete (u v : ℤ) : (5*5 : ℤ) ∣ F (3+5*u) (4+5*v) ↔
    (5 : ℤ) ∣ (-1)+(-6)*u+(1)*v := lift2_3.step (by norm_num) (by norm_num) u v
theorem lift2_3_children : childTable F 5 5 3 4 = {(3,9), (8,14), (13,19), (18,24), (23,4)} := by decide +kernel
#print axioms lift2_3_identity
#print axioms lift2_3_complete
#print axioms lift2_3_children
def lift2_4R (u v : ℤ) : ℤ := (-1) * (u)^2 * (v)^0
theorem lift2_4_identity (u v : ℤ) : F (4+5*u) (1+5*v) =
    5*((-3)+(-8)*u+(1)*v)+5^2*lift2_4R u v := by unfold F lift2_4R; ring
def lift2_4 : LiftPacket F 5 5 4 1 := ⟨-3,-8,1,lift2_4R,lift2_4_identity⟩
theorem lift2_4_complete (u v : ℤ) : (5*5 : ℤ) ∣ F (4+5*u) (1+5*v) ↔
    (5 : ℤ) ∣ (-3)+(-8)*u+(1)*v := lift2_4.step (by norm_num) (by norm_num) u v
theorem lift2_4_children : childTable F 5 5 4 1 = {(4,16), (9,6), (14,21), (19,11), (24,1)} := by decide +kernel
#print axioms lift2_4_identity
#print axioms lift2_4_complete
#print axioms lift2_4_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 160000000000480000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 25,y % 25) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
end Atlas_0d3f0fda0446828b
namespace Product_c232e439d6221945
open PerfectPower.ResidueAtlas PerfectPower.ResidueAtlasCRT
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (-1) * (x)^2 * (y)^0
def stage0 : AtlasPacket F 8 := Atlas_96fd8e69568bcedf.atlas3
theorem roots_count0 : stage0.roots.card = 8 := by decide +kernel
#print axioms roots_count0
def local1 : AtlasPacket F 9 := Atlas_fe4f1f7fe0f9852d.atlas2
theorem coprime1 : (8 : ℤ).natAbs.Coprime (9 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (8 : ℤ)*8+(-7)*9=1 := by decide +kernel
def stage1 : AtlasPacket F 72 := merge stage0 local1 8 (-7) coprime1 bezout1
theorem roots_count1 : stage1.roots.card = 72 := by
  change (roots stage0 local1 8 (-7)).card = 72
  rw [roots_card _ _ _ _ bezout1, roots_count0]; decide +kernel
#print axioms coprime1
#print axioms bezout1
#print axioms roots_count1
def local2 : AtlasPacket F 25 := Atlas_0d3f0fda0446828b.atlas2
theorem coprime2 : (72 : ℤ).natAbs.Coprime (25 : ℤ).natAbs := by decide +kernel
theorem bezout2 : (8 : ℤ)*72+(-23)*25=1 := by decide +kernel
def stage2 : AtlasPacket F 1800 := merge stage1 local2 8 (-23) coprime2 bezout2
theorem roots_count2 : stage2.roots.card = 1800 := by
  change (roots stage1 local2 8 (-23)).card = 1800
  rw [roots_card _ _ _ _ bezout2, roots_count1]; decide +kernel
#print axioms coprime2
#print axioms bezout2
#print axioms roots_count2
def bounds : Bounds := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem complete (x y : ℤ) : (x % 1800,y % 1800) ∈ stage2.roots ↔ F x y % 1800=0 := stage2.complete x y
theorem count_checked : (candidates stage2 bounds).card = 2222222222216666666667 := by
  change (candidates (merge stage1 local2 8 (-23) coprime2 bezout2) bounds).card = 2222222222216666666667
  rw [merged_count]; decide +kernel
theorem source_survives (x y : ℤ) (hF : F x y=0) : (x % 1800,y % 1800) ∈ stage2.roots := stage2.source_survives x y hF
#print axioms complete
#print axioms count_checked
#print axioms source_survives
end Product_c232e439d6221945
