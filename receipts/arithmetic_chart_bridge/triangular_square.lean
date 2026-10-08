import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_0536060f51784196
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (-1) * (x)^1 * (y)^0 + (2) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (1,2), (2,0)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact (((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-4,4),(-4,4))
theorem count_checked : (candidates atlas1 bounds).card = 36 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 3,y % 3) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : solutions atlas1 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas1 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_0536060f51784196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_3ea877f009ac3893
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (-1) * (x)^1 * (y)^0 + (2) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact (((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
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
  exact (((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (2) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(-1)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,-1,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(-1)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (2) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(3)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,3,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(3)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-4,4),(-4,4))
theorem count_checked : (candidates atlas2 bounds).card = 23 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_3ea877f009ac3893
namespace Intersection_b73158b754f60384
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_0536060f51784196.F x y % 3 = 0) 3 := ofAtlas Atlas_0536060f51784196.atlas1
def local1 : CoverPacket (fun x y => Atlas_3ea877f009ac3893.F x y % 4 = 0) 4 := ofAtlas Atlas_3ea877f009ac3893.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_3ea877f009ac3893.F x y % 4 = 0) 4 := local1
theorem group_roots0 : group0_0.roots = {(0,0), (0,2), (1,1), (1,3)} := by decide +kernel
#print axioms group_roots0
def group1_0 : CoverPacket (fun x y => Atlas_0536060f51784196.F x y % 3 = 0) 3 := local0
theorem group_roots1 : group1_0.roots = {(0,0), (1,1), (1,2), (2,0)} := by decide +kernel
#print axioms group_roots1
def stage0 : CoverPacket (fun x y => Atlas_3ea877f009ac3893.F x y % 4 = 0) 4 := group0_0
theorem coprime1 : (4 : ℤ).natAbs.Coprime (3 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (1 : ℤ)*4+(-1)*3=1 := by decide +kernel
def stage1 : CoverPacket (fun x y => (Atlas_3ea877f009ac3893.F x y % 4 = 0) ∧ (Atlas_0536060f51784196.F x y % 3 = 0)) 12 := merge stage0 group1_0 1 (-1) coprime1 bezout1
#print axioms coprime1
#print axioms bezout1
def bounds : Bounds := ((-4,4),(-4,4))
def S (x y : ℤ) : Prop := Atlas_0536060f51784196.F x y = 0 ∧ Atlas_3ea877f009ac3893.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 12,y % 12) ∈ stage1.roots ↔ (Atlas_3ea877f009ac3893.F x y % 4 = 0) ∧ (Atlas_0536060f51784196.F x y % 3 = 0) := stage1.complete x y
theorem roots_count : stage1.roots.card = 16 := by decide +kernel
theorem count_checked : (candidates stage1 bounds).card = 10 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : (Atlas_3ea877f009ac3893.F x y % 4 = 0) ∧ (Atlas_0536060f51784196.F x y % 3 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1⟩
  simp only [h0, h1, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 12,y % 12) ∈ stage1.roots := (stage1.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1)}
theorem points_checked : solutions stage1 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -4≤x ∧ x≤4 ∧ -4≤y ∧ y≤4 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage1 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_b73158b754f60384
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_1030009a23712008
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0 + (2) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,0), (2,1), (2,2)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact (((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-4,4),(-4,4))
theorem count_checked : (candidates atlas1 bounds).card = 36 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 3,y % 3) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (-1,1), (0,0)}
theorem points_checked : solutions atlas1 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas1 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_1030009a23712008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_2c8a28364bdb4e64
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0 + (2) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact (((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,2), (3,1), (3,3)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact (((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (2) * (u)^2 * (v)^0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(1)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,1,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2 + (2) * (u)^2 * (v)^0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((1)+(5)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨1,5,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (1)+(5)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(3,1), (3,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-4,4),(-4,4))
theorem count_checked : (candidates atlas2 bounds).card = 23 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (-1,1), (0,0)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_2c8a28364bdb4e64
namespace Intersection_df3cd4377fc15428
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_1030009a23712008.F x y % 3 = 0) 3 := ofAtlas Atlas_1030009a23712008.atlas1
def local1 : CoverPacket (fun x y => Atlas_2c8a28364bdb4e64.F x y % 4 = 0) 4 := ofAtlas Atlas_2c8a28364bdb4e64.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_2c8a28364bdb4e64.F x y % 4 = 0) 4 := local1
theorem group_roots0 : group0_0.roots = {(0,0), (0,2), (3,1), (3,3)} := by decide +kernel
#print axioms group_roots0
def group1_0 : CoverPacket (fun x y => Atlas_1030009a23712008.F x y % 3 = 0) 3 := local0
theorem group_roots1 : group1_0.roots = {(0,0), (1,0), (2,1), (2,2)} := by decide +kernel
#print axioms group_roots1
def stage0 : CoverPacket (fun x y => Atlas_2c8a28364bdb4e64.F x y % 4 = 0) 4 := group0_0
theorem coprime1 : (4 : ℤ).natAbs.Coprime (3 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (1 : ℤ)*4+(-1)*3=1 := by decide +kernel
def stage1 : CoverPacket (fun x y => (Atlas_2c8a28364bdb4e64.F x y % 4 = 0) ∧ (Atlas_1030009a23712008.F x y % 3 = 0)) 12 := merge stage0 group1_0 1 (-1) coprime1 bezout1
#print axioms coprime1
#print axioms bezout1
def bounds : Bounds := ((-4,4),(-4,4))
def S (x y : ℤ) : Prop := Atlas_1030009a23712008.F x y = 0 ∧ Atlas_2c8a28364bdb4e64.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 12,y % 12) ∈ stage1.roots ↔ (Atlas_2c8a28364bdb4e64.F x y % 4 = 0) ∧ (Atlas_1030009a23712008.F x y % 3 = 0) := stage1.complete x y
theorem roots_count : stage1.roots.card = 16 := by decide +kernel
theorem count_checked : (candidates stage1 bounds).card = 10 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : (Atlas_2c8a28364bdb4e64.F x y % 4 = 0) ∧ (Atlas_1030009a23712008.F x y % 3 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1⟩
  simp only [h0, h1, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 12,y % 12) ∈ stage1.roots := (stage1.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (-1,1), (0,0)}
theorem points_checked : solutions stage1 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -4≤x ∧ x≤4 ∧ -4≤y ∧ y≤4 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage1 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_df3cd4377fc15428
namespace PowerCharts_b8a1375ce1a9a53c
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^2 + (-1) * (x)^1 * (y)^0 + (1) * (x)^2 * (y)^0
def bounds : Bounds := ((-8,9),(-4,4))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (-1) * (n)^1 * (y)^0 + (2) * (n)^2 * (y)^0
theorem identity0 (n y : ℤ) : F (0+2*n) y=2*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 2 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+2*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 2*m ∣ F (0+2*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_b73158b754f60384.stage1 bounds 2 0
theorem count0 : candidates0.card=10 := by
  rw [candidates0,chart_count Intersection_b73158b754f60384.stage1 bounds 2 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def G1 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (1) * (n)^1 * (y)^0 + (2) * (n)^2 * (y)^0
theorem identity1 (n y : ℤ) : F (1+2*n) y=2*G1 n y := by unfold F G1; ring
def chart1 : ChartPacket F G1 2 1 := ⟨by norm_num,identity1⟩
theorem source_transport1 (n y : ℤ) : F (1+2*n) y=0 ↔ G1 n y=0 := chart1.source_iff n y
theorem denominator_transport1 (m n y : ℤ) : 2*m ∣ F (1+2*n) y ↔ m ∣ G1 n y := chart1.congruence_iff m n y
def candidates1 := chartCandidates Intersection_df3cd4377fc15428.stage1 bounds 2 1
theorem count1 : candidates1.card=10 := by
  rw [candidates1,chart_count Intersection_df3cd4377fc15428.stage1 bounds 2 1 (by norm_num)]; decide +kernel
#print axioms identity1
#print axioms source_transport1
#print axioms denominator_transport1
#print axioms count1
def residue (i : Fin 2) : ℤ := if i.val=0 then 0 else 1
def P (i : Fin 2) (x y : ℤ) : Prop := if i.val=0 then ((Atlas_3ea877f009ac3893.F x y % 4 = 0) ∧ (Atlas_0536060f51784196.F x y % 3 = 0)) else ((Atlas_2c8a28364bdb4e64.F x y % 4 = 0) ∧ (Atlas_1030009a23712008.F x y % 3 = 0))
def cover : (i : Fin 2) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 12 := Fin.cases Intersection_b73158b754f60384.stage1 (Fin.cases Intersection_df3cd4377fc15428.stage1 ((fun i => Fin.elim0 i)))
theorem residue_canonical : ∀ i : Fin 2, 0≤residue i ∧ residue i<2 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 2 residue
theorem population_checked : allCandidates.card=20 := by
  rw [allCandidates,family_count cover bounds 2 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (True)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-8) (9)).product (Finset.Icc (-4) (4))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := {(-1,-1), (-1,1), (0,0), (1,0), (2,-1), (2,1)}
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -8≤x ∧ x≤9 ∧ -4≤y ∧ y≤4 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
end PowerCharts_b8a1375ce1a9a53c
