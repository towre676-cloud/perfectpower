import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_99786141983d2738
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (9) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (9)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
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
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (9)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (9) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(0)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,0,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2), (2,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (9) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((4)+(18)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨4,18,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (4)+(18)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3), (3,1), (3,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((0,0),(-2,2))
theorem count_checked : (candidates atlas2 bounds).card = 3 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    0 ≤ x ∧ x ≤ 0 ∧ -2 ≤ y ∧ y ≤ 2 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_99786141983d2738
namespace Intersection_272c108311f33024
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_99786141983d2738.F x y % 4 = 0) 4 := ofAtlas Atlas_99786141983d2738.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_99786141983d2738.F x y % 4 = 0) 4 := local0
theorem group_roots0 : group0_0.roots = {(0,0), (0,2), (1,1), (1,3), (2,0), (2,2), (3,1), (3,3)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => Atlas_99786141983d2738.F x y % 4 = 0) 4 := group0_0
def bounds : Bounds := ((0,0),(-2,2))
def S (x y : ℤ) : Prop := Atlas_99786141983d2738.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 4,y % 4) ∈ stage0.roots ↔ Atlas_99786141983d2738.F x y % 4 = 0 := stage0.complete x y
theorem roots_count : stage0.roots.card = 8 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 3 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : Atlas_99786141983d2738.F x y % 4 = 0 := by
  simp only [S] at h
  have h0 := h
  simp only [h0, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 4,y % 4) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ 0≤x ∧ x≤0 ∧ -2≤y ∧ y≤2 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_272c108311f33024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_b8bc9b56afa4c7cc
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^0 + (-1) * (x)^0 * (y)^2 + (6) * (x)^1 * (y)^0 + (9) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,1), (1,0)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (6)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (9)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,1), (0,3), (1,0), (1,2), (2,1), (2,3), (3,0), (3,2)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (6)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (9)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (9) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (1+2*v) =
    2*((0)+(6)*u+(-2)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 1 := ⟨0,6,-2,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(6)*u+(-2)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 1 = {(0,1), (0,3), (2,1), (2,3)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (9) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (0+2*v) =
    2*((8)+(24)*u+(0)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 0 := ⟨8,24,0,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (8)+(24)*u+(0)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 0 = {(1,0), (1,2), (3,0), (3,2)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1,0),(-2,2))
theorem count_checked : (candidates atlas2 bounds).card = 5 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-2), (-1,2), (0,-1), (0,1)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -1 ≤ x ∧ x ≤ 0 ∧ -2 ≤ y ∧ y ≤ 2 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_b8bc9b56afa4c7cc
namespace Intersection_038c9c8221f06c3e
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_b8bc9b56afa4c7cc.F x y % 4 = 0) 4 := ofAtlas Atlas_b8bc9b56afa4c7cc.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_b8bc9b56afa4c7cc.F x y % 4 = 0) 4 := local0
theorem group_roots0 : group0_0.roots = {(0,1), (0,3), (1,0), (1,2), (2,1), (2,3), (3,0), (3,2)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => Atlas_b8bc9b56afa4c7cc.F x y % 4 = 0) 4 := group0_0
def bounds : Bounds := ((-1,0),(-2,2))
def S (x y : ℤ) : Prop := Atlas_b8bc9b56afa4c7cc.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 4,y % 4) ∈ stage0.roots ↔ Atlas_b8bc9b56afa4c7cc.F x y % 4 = 0 := stage0.complete x y
theorem roots_count : stage0.roots.card = 8 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 5 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : Atlas_b8bc9b56afa4c7cc.F x y % 4 = 0 := by
  simp only [S] at h
  have h0 := h
  simp only [h0, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 4,y % 4) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-2), (-1,2), (0,-1), (0,1)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -1≤x ∧ x≤0 ∧ -2≤y ∧ y≤2 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_038c9c8221f06c3e
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_cc7939537bb7925c
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (4) * (x)^0 * (y)^0 + (-1) * (x)^0 * (y)^2 + (12) * (x)^1 * (y)^0 + (9) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((((Int.ModEq.refl (4)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (12)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (9)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
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
  exact ((((((Int.ModEq.refl (4)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (12)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (9)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (9) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((2)+(12)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨2,12,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (2)+(12)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2), (2,0), (2,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (9) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((12)+(30)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨12,30,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (12)+(30)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3), (3,1), (3,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1,0),(-2,2))
theorem count_checked : (candidates atlas2 bounds).card = 5 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (-1,1), (0,-2), (0,2)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -1 ≤ x ∧ x ≤ 0 ∧ -2 ≤ y ∧ y ≤ 2 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_cc7939537bb7925c
namespace Intersection_5a4112585aa5463d
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_cc7939537bb7925c.F x y % 4 = 0) 4 := ofAtlas Atlas_cc7939537bb7925c.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_cc7939537bb7925c.F x y % 4 = 0) 4 := local0
theorem group_roots0 : group0_0.roots = {(0,0), (0,2), (1,1), (1,3), (2,0), (2,2), (3,1), (3,3)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => Atlas_cc7939537bb7925c.F x y % 4 = 0) 4 := group0_0
def bounds : Bounds := ((-1,0),(-2,2))
def S (x y : ℤ) : Prop := Atlas_cc7939537bb7925c.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 4,y % 4) ∈ stage0.roots ↔ Atlas_cc7939537bb7925c.F x y % 4 = 0 := stage0.complete x y
theorem roots_count : stage0.roots.card = 8 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 5 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : Atlas_cc7939537bb7925c.F x y % 4 = 0 := by
  simp only [S] at h
  have h0 := h
  simp only [h0, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 4,y % 4) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (-1,1), (0,-2), (0,2)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -1≤x ∧ x≤0 ∧ -2≤y ∧ y≤2 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_5a4112585aa5463d
namespace PowerCharts_6e3173a36702742b
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-9) * (x)^0 * (y)^2 + (1) * (x)^2 * (y)^0
def bounds : Bounds := ((-6,6),(-2,2))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (9) * (n)^2 * (y)^0
theorem identity0 (n y : ℤ) : F (0+9*n) y=9*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 9 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+9*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 9*m ∣ F (0+9*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_272c108311f33024.stage0 bounds 9 0
theorem count0 : candidates0.card=3 := by
  rw [candidates0,chart_count Intersection_272c108311f33024.stage0 bounds 9 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def G1 (n y : ℤ) : ℤ := (1) * (n)^0 * (y)^0 + (-1) * (n)^0 * (y)^2 + (6) * (n)^1 * (y)^0 + (9) * (n)^2 * (y)^0
theorem identity1 (n y : ℤ) : F (3+9*n) y=9*G1 n y := by unfold F G1; ring
def chart1 : ChartPacket F G1 9 3 := ⟨by norm_num,identity1⟩
theorem source_transport1 (n y : ℤ) : F (3+9*n) y=0 ↔ G1 n y=0 := chart1.source_iff n y
theorem denominator_transport1 (m n y : ℤ) : 9*m ∣ F (3+9*n) y ↔ m ∣ G1 n y := chart1.congruence_iff m n y
def candidates1 := chartCandidates Intersection_038c9c8221f06c3e.stage0 bounds 9 3
theorem count1 : candidates1.card=5 := by
  rw [candidates1,chart_count Intersection_038c9c8221f06c3e.stage0 bounds 9 3 (by norm_num)]; decide +kernel
#print axioms identity1
#print axioms source_transport1
#print axioms denominator_transport1
#print axioms count1
def G2 (n y : ℤ) : ℤ := (4) * (n)^0 * (y)^0 + (-1) * (n)^0 * (y)^2 + (12) * (n)^1 * (y)^0 + (9) * (n)^2 * (y)^0
theorem identity2 (n y : ℤ) : F (6+9*n) y=9*G2 n y := by unfold F G2; ring
def chart2 : ChartPacket F G2 9 6 := ⟨by norm_num,identity2⟩
theorem source_transport2 (n y : ℤ) : F (6+9*n) y=0 ↔ G2 n y=0 := chart2.source_iff n y
theorem denominator_transport2 (m n y : ℤ) : 9*m ∣ F (6+9*n) y ↔ m ∣ G2 n y := chart2.congruence_iff m n y
def candidates2 := chartCandidates Intersection_5a4112585aa5463d.stage0 bounds 9 6
theorem count2 : candidates2.card=5 := by
  rw [candidates2,chart_count Intersection_5a4112585aa5463d.stage0 bounds 9 6 (by norm_num)]; decide +kernel
#print axioms identity2
#print axioms source_transport2
#print axioms denominator_transport2
#print axioms count2
def residue (i : Fin 3) : ℤ := if i.val=0 then 0 else if i.val=1 then 3 else 6
def P (i : Fin 3) (x y : ℤ) : Prop := if i.val=0 then (Atlas_99786141983d2738.F x y % 4 = 0) else if i.val=1 then (Atlas_b8bc9b56afa4c7cc.F x y % 4 = 0) else (Atlas_cc7939537bb7925c.F x y % 4 = 0)
def cover : (i : Fin 3) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 4 := Fin.cases Intersection_272c108311f33024.stage0 (Fin.cases Intersection_038c9c8221f06c3e.stage0 (Fin.cases Intersection_5a4112585aa5463d.stage0 ((fun i => Fin.elim0 i))))
theorem residue_canonical : ∀ i : Fin 3, 0≤residue i ∧ residue i<9 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 9 residue
theorem population_checked : allCandidates.card=13 := by
  rw [allCandidates,family_count cover bounds 9 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (True)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-6) (6)).product (Finset.Icc (-2) (2))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := {(-6,-2), (-6,2), (-3,-1), (-3,1), (0,0), (3,-1), (3,1), (6,-2), (6,2)}
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -6≤x ∧ x≤6 ∧ -2≤y ∧ y≤2 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
end PowerCharts_6e3173a36702742b
