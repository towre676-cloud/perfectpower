import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_aa68e920280158db
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^0 + (1) * (x)^0 * (y)^1
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,1), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-8,8),(-8,8))
theorem count_checked : (candidates atlas1 bounds).card = 136 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 2,y % 2) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-8,1), (-7,1), (-6,1), (-5,1), (-4,1), (-3,1), (-2,1), (-1,1), (0,1), (1,1), (2,1), (3,1), (4,1), (5,1), (6,1), (7,1), (8,1)}
theorem points_checked : solutions atlas1 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -8 ≤ x ∧ x ≤ 8 ∧ -8 ≤ y ∧ y ≤ 8 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas1 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_aa68e920280158db
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_33c115870211040a
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,0)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,0), (2,0), (3,0)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := 0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(0)*u+(1)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,0,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (2,0)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := 0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (0+2*v) =
    2*((0)+(0)*u+(1)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 0 := ⟨0,0,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(0)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 0 = {(1,0), (3,0)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-8,8),(-8,8))
theorem count_checked : (candidates atlas2 bounds).card = 85 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-8,0), (-7,0), (-6,0), (-5,0), (-4,0), (-3,0), (-2,0), (-1,0), (0,0), (1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0), (8,0)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -8 ≤ x ∧ x ≤ 8 ∧ -8 ≤ y ∧ y ≤ 8 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_33c115870211040a
namespace Intersection_fc0f76096bfa09db
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_aa68e920280158db.F x y % 2 = 0) 2 := ofAtlas Atlas_aa68e920280158db.atlas1
def local1 : CoverPacket (fun x y => Atlas_33c115870211040a.F x y % 4 = 0) 4 := ofAtlas Atlas_33c115870211040a.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_33c115870211040a.F x y % 4 = 0) 4 := local1
def group0_1 : CoverPacket (fun x y => (Atlas_33c115870211040a.F x y % 4 = 0) ∧ (Atlas_aa68e920280158db.F x y % 2 = 0)) 4 := nested group0_0 local0 (by norm_num)
theorem group_roots0 : group0_1.roots = ∅ := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => (Atlas_33c115870211040a.F x y % 4 = 0) ∧ (Atlas_aa68e920280158db.F x y % 2 = 0)) 4 := group0_1
def bounds : Bounds := ((-8,8),(-8,8))
def S (x y : ℤ) : Prop := Atlas_aa68e920280158db.F x y = 0 ∧ Atlas_33c115870211040a.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 4,y % 4) ∈ stage0.roots ↔ (Atlas_33c115870211040a.F x y % 4 = 0) ∧ (Atlas_aa68e920280158db.F x y % 2 = 0) := stage0.complete x y
theorem roots_count : stage0.roots.card = 0 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 0 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : (Atlas_33c115870211040a.F x y % 4 = 0) ∧ (Atlas_aa68e920280158db.F x y % 2 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1⟩
  simp only [h0, h1, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 4,y % 4) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
theorem no_integer_solution (x y : ℤ) : ¬ S x y := fun h => stage0.empty_obstruction (by decide +kernel) x y (source_implies x y h)
#print axioms no_integer_solution
def points : Finset (ℤ × ℤ) := ∅
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -8≤x ∧ x≤8 ∧ -8≤y ∧ y≤8 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_fc0f76096bfa09db
