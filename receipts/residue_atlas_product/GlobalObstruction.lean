import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasCRT
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_71ae3aa832246986
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^2 + (-1) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact (((((Int.ModEq.refl (-2)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := ∅
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact (((((Int.ModEq.refl (-2)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((-1)+(0)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨-1,0,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (-1)+(0)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = ∅ := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((-1)+(-2)*u+(2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨-1,-2,2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (-1)+(-2)*u+(2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = ∅ := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 0 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
theorem no_integer_solution (x y : ℤ) : F x y ≠ 0 := atlas2.empty_obstruction rfl x y
#print axioms no_integer_solution
end Atlas_71ae3aa832246986
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_40cc56a5fc9b9d20
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^2 + (-1) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(1,0), (2,0)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact (((((Int.ModEq.refl (-2)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(4,0), (4,3), (4,6), (5,0), (5,3), (5,6)}
theorem periodic2 (x y : ℤ) : F x y % 9 = F (x % 9) (y % 9) % 9 := by
  change Int.ModEq 9 (F x y) (F (x % 9) (y % 9))
  have hx : Int.ModEq 9 x (x % 9) := (Int.mod_modEq x 9).symm
  have hy : Int.ModEq 9 y (y % 9) := (Int.mod_modEq y 9).symm
  unfold F
  exact (((((Int.ModEq.refl (-2)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 9 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 9 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 9,y % 9) ∈ roots2 ↔ F x y % 9 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (1+3*u) (0+3*v) =
    3*((-1)+(-2)*u+(0)*v)+3^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 3 3 1 0 := ⟨-1,-2,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (1+3*u) (0+3*v) ↔
    (3 : ℤ) ∣ (-1)+(-2)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 3 3 1 0 = {(4,0), (4,3), (4,6)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (1) * (u)^0 * (v)^2 + (-1) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (2+3*u) (0+3*v) =
    3*((-2)+(-4)*u+(0)*v)+3^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 3 3 2 0 := ⟨-2,-4,0,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (2+3*u) (0+3*v) ↔
    (3 : ℤ) ∣ (-2)+(-4)*u+(0)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 3 3 2 0 = {(5,0), (5,3), (5,6)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 296296296296148148148148 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 9,y % 9) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
end Atlas_40cc56a5fc9b9d20
namespace Product_253b034bda94c230
open PerfectPower.ResidueAtlas PerfectPower.ResidueAtlasCRT
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^2 + (-1) * (x)^2 * (y)^0
def stage0 : AtlasPacket F 4 := Atlas_71ae3aa832246986.atlas2
theorem roots_count0 : stage0.roots.card = 0 := by decide +kernel
#print axioms roots_count0
def local1 : AtlasPacket F 9 := Atlas_40cc56a5fc9b9d20.atlas2
theorem coprime1 : (4 : ℤ).natAbs.Coprime (9 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (7 : ℤ)*4+(-3)*9=1 := by decide +kernel
def stage1 : AtlasPacket F 36 := merge stage0 local1 7 (-3) coprime1 bezout1
theorem roots_count1 : stage1.roots.card = 0 := by
  change (roots stage0 local1 7 (-3)).card = 0
  rw [roots_card _ _ _ _ bezout1, roots_count0]; decide +kernel
#print axioms coprime1
#print axioms bezout1
#print axioms roots_count1
def bounds : Bounds := ((-1000000000000,1000000000000),(-1000000000000,1000000000000))
theorem complete (x y : ℤ) : (x % 36,y % 36) ∈ stage1.roots ↔ F x y % 36=0 := stage1.complete x y
theorem count_checked : (candidates stage1 bounds).card = 0 := by
  change (candidates (merge stage0 local1 7 (-3) coprime1 bezout1) bounds).card = 0
  rw [merged_count]; decide +kernel
theorem source_survives (x y : ℤ) (hF : F x y=0) : (x % 36,y % 36) ∈ stage1.roots := stage1.source_survives x y hF
#print axioms complete
#print axioms count_checked
#print axioms source_survives
theorem no_integer_solution (x y : ℤ) : F x y ≠ 0 := stage1.empty_obstruction (by decide +kernel) x y
#print axioms no_integer_solution
end Product_253b034bda94c230
