import PerfectPower.ResidueAtlas
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_c265e369cae34ea3
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,2), (1,1), (1,3)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(1)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,1,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(1)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,1,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def roots3 : Finset (ℤ × ℤ) := {(0,0), (0,4), (1,1), (1,3), (1,5), (1,7), (4,2), (4,6)}
theorem periodic3 (x y : ℤ) : F x y % 8 = F (x % 8) (y % 8) % 8 := by
  change Int.ModEq 8 (F x y) (F (x % 8) (y % 8))
  have hx : Int.ModEq 8 x (x % 8) := (Int.mod_modEq x 8).symm
  have hy : Int.ModEq 8 y (y % 8) := (Int.mod_modEq y 8).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked3 : rootTable F 8 = roots3 := by decide +kernel
def atlas3 : AtlasPacket F 8 := ⟨by norm_num, roots3, checked3, periodic3⟩
theorem complete3 (x y : ℤ) : (x % 8,y % 8) ∈ roots3 ↔ F x y % 8 = 0 := atlas3.complete x y
#print axioms periodic3
#print axioms checked3
#print axioms complete3
def lift3_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_0_identity (u v : ℤ) : F (0+4*u) (0+4*v) =
    4*((0)+(1)*u+(0)*v)+4^2*lift3_0R u v := by unfold F lift3_0R; ring
def lift3_0 : LiftPacket F 2 4 0 0 := ⟨0,1,0,lift3_0R,lift3_0_identity⟩
theorem lift3_0_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift3_0.step (by norm_num) (by norm_num) u v
theorem lift3_0_children : childTable F 2 4 0 0 = {(0,0), (0,4)} := by decide +kernel
#print axioms lift3_0_identity
#print axioms lift3_0_complete
#print axioms lift3_0_children
def lift3_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_1_identity (u v : ℤ) : F (0+4*u) (2+4*v) =
    4*((-1)+(1)*u+(-4)*v)+4^2*lift3_1R u v := by unfold F lift3_1R; ring
def lift3_1 : LiftPacket F 2 4 0 2 := ⟨-1,1,-4,lift3_1R,lift3_1_identity⟩
theorem lift3_1_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (-1)+(1)*u+(-4)*v := lift3_1.step (by norm_num) (by norm_num) u v
theorem lift3_1_children : childTable F 2 4 0 2 = {(4,2), (4,6)} := by decide +kernel
#print axioms lift3_1_identity
#print axioms lift3_1_complete
#print axioms lift3_1_children
def lift3_2R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_2_identity (u v : ℤ) : F (1+4*u) (1+4*v) =
    4*((0)+(1)*u+(-2)*v)+4^2*lift3_2R u v := by unfold F lift3_2R; ring
def lift3_2 : LiftPacket F 2 4 1 1 := ⟨0,1,-2,lift3_2R,lift3_2_identity⟩
theorem lift3_2_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-2)*v := lift3_2.step (by norm_num) (by norm_num) u v
theorem lift3_2_children : childTable F 2 4 1 1 = {(1,1), (1,5)} := by decide +kernel
#print axioms lift3_2_identity
#print axioms lift3_2_complete
#print axioms lift3_2_children
def lift3_3R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_3_identity (u v : ℤ) : F (1+4*u) (3+4*v) =
    4*((-2)+(1)*u+(-6)*v)+4^2*lift3_3R u v := by unfold F lift3_3R; ring
def lift3_3 : LiftPacket F 2 4 1 3 := ⟨-2,1,-6,lift3_3R,lift3_3_identity⟩
theorem lift3_3_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (3+4*v) ↔
    (2 : ℤ) ∣ (-2)+(1)*u+(-6)*v := lift3_3.step (by norm_num) (by norm_num) u v
theorem lift3_3_children : childTable F 2 4 1 3 = {(1,3), (1,7)} := by decide +kernel
#print axioms lift3_3_identity
#print axioms lift3_3_complete
#print axioms lift3_3_children
def roots4 : Finset (ℤ × ℤ) := {(0,0), (0,4), (0,8), (0,12), (1,1), (1,7), (1,9), (1,15), (4,2), (4,6), (4,10), (4,14), (9,3), (9,5), (9,11), (9,13)}
theorem periodic4 (x y : ℤ) : F x y % 16 = F (x % 16) (y % 16) % 16 := by
  change Int.ModEq 16 (F x y) (F (x % 16) (y % 16))
  have hx : Int.ModEq 16 x (x % 16) := (Int.mod_modEq x 16).symm
  have hy : Int.ModEq 16 y (y % 16) := (Int.mod_modEq y 16).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked4 : rootTable F 16 = roots4 := by decide +kernel
def atlas4 : AtlasPacket F 16 := ⟨by norm_num, roots4, checked4, periodic4⟩
theorem complete4 (x y : ℤ) : (x % 16,y % 16) ∈ roots4 ↔ F x y % 16 = 0 := atlas4.complete x y
#print axioms periodic4
#print axioms checked4
#print axioms complete4
def lift4_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_0_identity (u v : ℤ) : F (0+8*u) (0+8*v) =
    8*((0)+(1)*u+(0)*v)+8^2*lift4_0R u v := by unfold F lift4_0R; ring
def lift4_0 : LiftPacket F 2 8 0 0 := ⟨0,1,0,lift4_0R,lift4_0_identity⟩
theorem lift4_0_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (0+8*u) (0+8*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift4_0.step (by norm_num) (by norm_num) u v
theorem lift4_0_children : childTable F 2 8 0 0 = {(0,0), (0,8)} := by decide +kernel
#print axioms lift4_0_identity
#print axioms lift4_0_complete
#print axioms lift4_0_children
def lift4_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_1_identity (u v : ℤ) : F (0+8*u) (4+8*v) =
    8*((-2)+(1)*u+(-8)*v)+8^2*lift4_1R u v := by unfold F lift4_1R; ring
def lift4_1 : LiftPacket F 2 8 0 4 := ⟨-2,1,-8,lift4_1R,lift4_1_identity⟩
theorem lift4_1_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (0+8*u) (4+8*v) ↔
    (2 : ℤ) ∣ (-2)+(1)*u+(-8)*v := lift4_1.step (by norm_num) (by norm_num) u v
theorem lift4_1_children : childTable F 2 8 0 4 = {(0,4), (0,12)} := by decide +kernel
#print axioms lift4_1_identity
#print axioms lift4_1_complete
#print axioms lift4_1_children
def lift4_2R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_2_identity (u v : ℤ) : F (1+8*u) (1+8*v) =
    8*((0)+(1)*u+(-2)*v)+8^2*lift4_2R u v := by unfold F lift4_2R; ring
def lift4_2 : LiftPacket F 2 8 1 1 := ⟨0,1,-2,lift4_2R,lift4_2_identity⟩
theorem lift4_2_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (1+8*u) (1+8*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-2)*v := lift4_2.step (by norm_num) (by norm_num) u v
theorem lift4_2_children : childTable F 2 8 1 1 = {(1,1), (1,9)} := by decide +kernel
#print axioms lift4_2_identity
#print axioms lift4_2_complete
#print axioms lift4_2_children
def lift4_3R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_3_identity (u v : ℤ) : F (1+8*u) (3+8*v) =
    8*((-1)+(1)*u+(-6)*v)+8^2*lift4_3R u v := by unfold F lift4_3R; ring
def lift4_3 : LiftPacket F 2 8 1 3 := ⟨-1,1,-6,lift4_3R,lift4_3_identity⟩
theorem lift4_3_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (1+8*u) (3+8*v) ↔
    (2 : ℤ) ∣ (-1)+(1)*u+(-6)*v := lift4_3.step (by norm_num) (by norm_num) u v
theorem lift4_3_children : childTable F 2 8 1 3 = {(9,3), (9,11)} := by decide +kernel
#print axioms lift4_3_identity
#print axioms lift4_3_complete
#print axioms lift4_3_children
def lift4_4R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_4_identity (u v : ℤ) : F (1+8*u) (5+8*v) =
    8*((-3)+(1)*u+(-10)*v)+8^2*lift4_4R u v := by unfold F lift4_4R; ring
def lift4_4 : LiftPacket F 2 8 1 5 := ⟨-3,1,-10,lift4_4R,lift4_4_identity⟩
theorem lift4_4_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (1+8*u) (5+8*v) ↔
    (2 : ℤ) ∣ (-3)+(1)*u+(-10)*v := lift4_4.step (by norm_num) (by norm_num) u v
theorem lift4_4_children : childTable F 2 8 1 5 = {(9,5), (9,13)} := by decide +kernel
#print axioms lift4_4_identity
#print axioms lift4_4_complete
#print axioms lift4_4_children
def lift4_5R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_5_identity (u v : ℤ) : F (1+8*u) (7+8*v) =
    8*((-6)+(1)*u+(-14)*v)+8^2*lift4_5R u v := by unfold F lift4_5R; ring
def lift4_5 : LiftPacket F 2 8 1 7 := ⟨-6,1,-14,lift4_5R,lift4_5_identity⟩
theorem lift4_5_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (1+8*u) (7+8*v) ↔
    (2 : ℤ) ∣ (-6)+(1)*u+(-14)*v := lift4_5.step (by norm_num) (by norm_num) u v
theorem lift4_5_children : childTable F 2 8 1 7 = {(1,7), (1,15)} := by decide +kernel
#print axioms lift4_5_identity
#print axioms lift4_5_complete
#print axioms lift4_5_children
def lift4_6R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_6_identity (u v : ℤ) : F (4+8*u) (2+8*v) =
    8*((0)+(1)*u+(-4)*v)+8^2*lift4_6R u v := by unfold F lift4_6R; ring
def lift4_6 : LiftPacket F 2 8 4 2 := ⟨0,1,-4,lift4_6R,lift4_6_identity⟩
theorem lift4_6_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (4+8*u) (2+8*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-4)*v := lift4_6.step (by norm_num) (by norm_num) u v
theorem lift4_6_children : childTable F 2 8 4 2 = {(4,2), (4,10)} := by decide +kernel
#print axioms lift4_6_identity
#print axioms lift4_6_complete
#print axioms lift4_6_children
def lift4_7R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift4_7_identity (u v : ℤ) : F (4+8*u) (6+8*v) =
    8*((-4)+(1)*u+(-12)*v)+8^2*lift4_7R u v := by unfold F lift4_7R; ring
def lift4_7 : LiftPacket F 2 8 4 6 := ⟨-4,1,-12,lift4_7R,lift4_7_identity⟩
theorem lift4_7_complete (u v : ℤ) : (8*2 : ℤ) ∣ F (4+8*u) (6+8*v) ↔
    (2 : ℤ) ∣ (-4)+(1)*u+(-12)*v := lift4_7.step (by norm_num) (by norm_num) u v
theorem lift4_7_children : childTable F 2 8 4 6 = {(4,6), (4,14)} := by decide +kernel
#print axioms lift4_7_identity
#print axioms lift4_7_complete
#print axioms lift4_7_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem count_checked : (candidates atlas4 bounds).card = 250000000000625000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 16,y % 16) ∈ roots4 := atlas4.source_survives x y hF
#print axioms source_survives
end Atlas_c265e369cae34ea3
