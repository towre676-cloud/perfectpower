import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_7b49fa904291dad0
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^3 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (2,2)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 3 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-3,4),(-3,3))
theorem count_checked : (candidates atlas1 bounds).card = 19 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 3,y % 3) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (0,0), (1,1)}
theorem points_checked : solutions atlas1 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -3 ≤ x ∧ x ≤ 4 ∧ -3 ≤ y ∧ y ≤ 3 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas1 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_7b49fa904291dad0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_58fbfb2ef10c83e4
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^1 + (2) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,0)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (1,2), (2,0), (3,2)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 1 hy)).add (((Int.ModEq.refl (2)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := 0
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(2)*u+(1)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,2,1,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(2)*u+(1)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (2,0)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := 0
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (0+2*v) =
    2*((1)+(2)*u+(1)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 0 := ⟨1,2,1,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (1)+(2)*u+(1)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 0 = {(1,2), (3,2)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-3,4),(-3,3))
theorem count_checked : (candidates atlas2 bounds).card = 12 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,2), (0,0), (1,-2)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -3 ≤ x ∧ x ≤ 4 ∧ -3 ≤ y ∧ y ≤ 3 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_58fbfb2ef10c83e4
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_e49fd7096232fa8e
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^3 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 3 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,2), (1,1), (3,3)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 3 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-2) * (u)^0 * (v)^3
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(1)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,1,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-3) * (u)^0 * (v)^2 + (-2) * (u)^0 * (v)^3
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(1)*u+(-3)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,1,-3,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-3)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (3,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-3,4),(-3,3))
theorem count_checked : (candidates atlas2 bounds).card = 14 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-1), (0,0), (1,1)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -3 ≤ x ∧ x ≤ 4 ∧ -3 ≤ y ∧ y ≤ 3 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_e49fd7096232fa8e
namespace Intersection_cbe793a99c283f59
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_7b49fa904291dad0.F x y % 3 = 0) 3 := ofAtlas Atlas_7b49fa904291dad0.atlas1
def local1 : CoverPacket (fun x y => Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) 4 := ofAtlas Atlas_58fbfb2ef10c83e4.atlas2
def local2 : CoverPacket (fun x y => Atlas_e49fd7096232fa8e.F x y % 4 = 0) 4 := ofAtlas Atlas_e49fd7096232fa8e.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) 4 := local1
def group0_1 : CoverPacket (fun x y => (Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) ∧ (Atlas_e49fd7096232fa8e.F x y % 4 = 0)) 4 := nested group0_0 local2 (by norm_num)
theorem group_roots0 : group0_1.roots = {(0,0)} := by decide +kernel
#print axioms group_roots0
def group1_0 : CoverPacket (fun x y => Atlas_7b49fa904291dad0.F x y % 3 = 0) 3 := local0
theorem group_roots1 : group1_0.roots = {(0,0), (1,1), (2,2)} := by decide +kernel
#print axioms group_roots1
def stage0 : CoverPacket (fun x y => (Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) ∧ (Atlas_e49fd7096232fa8e.F x y % 4 = 0)) 4 := group0_1
theorem coprime1 : (4 : ℤ).natAbs.Coprime (3 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (1 : ℤ)*4+(-1)*3=1 := by decide +kernel
def stage1 : CoverPacket (fun x y => ((Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) ∧ (Atlas_e49fd7096232fa8e.F x y % 4 = 0)) ∧ (Atlas_7b49fa904291dad0.F x y % 3 = 0)) 12 := merge stage0 group1_0 1 (-1) coprime1 bezout1
#print axioms coprime1
#print axioms bezout1
def bounds : Bounds := ((-3,4),(-3,3))
def S (x y : ℤ) : Prop := Atlas_7b49fa904291dad0.F x y = 0 ∧ Atlas_58fbfb2ef10c83e4.F x y = 0 ∧ Atlas_e49fd7096232fa8e.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 12,y % 12) ∈ stage1.roots ↔ ((Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) ∧ (Atlas_e49fd7096232fa8e.F x y % 4 = 0)) ∧ (Atlas_7b49fa904291dad0.F x y % 3 = 0) := stage1.complete x y
theorem roots_count : stage1.roots.card = 3 := by decide +kernel
theorem count_checked : (candidates stage1 bounds).card = 1 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : ((Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) ∧ (Atlas_e49fd7096232fa8e.F x y % 4 = 0)) ∧ (Atlas_7b49fa904291dad0.F x y % 3 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1,h2⟩
  simp only [h0, h1, h2, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 12,y % 12) ∈ stage1.roots := (stage1.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0)}
theorem points_checked : solutions stage1 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -3≤x ∧ x≤4 ∧ -3≤y ∧ y≤3 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage1 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_cbe793a99c283f59
namespace PowerCharts_fbe7db10e106509e
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^3 + (1) * (x)^1 * (y)^0
def bounds : Bounds := ((-6,9),(-3,3))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^3 + (1) * (n)^1 * (y)^0
theorem identity0 (n y : ℤ) : F (0+2*n) y=2*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 2 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+2*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 2*m ∣ F (0+2*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_cbe793a99c283f59.stage1 bounds 2 0
theorem count0 : candidates0.card=1 := by
  rw [candidates0,chart_count Intersection_cbe793a99c283f59.stage1 bounds 2 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def residue (i : Fin 1) : ℤ := 0
def P (i : Fin 1) (x y : ℤ) : Prop := (((Atlas_58fbfb2ef10c83e4.F x y % 4 = 0) ∧ (Atlas_e49fd7096232fa8e.F x y % 4 = 0)) ∧ (Atlas_7b49fa904291dad0.F x y % 3 = 0))
def cover : (i : Fin 1) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 12 := Fin.cases Intersection_cbe793a99c283f59.stage1 ((fun i => Fin.elim0 i))
theorem residue_canonical : ∀ i : Fin 1, 0≤residue i ∧ residue i<2 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 2 residue
theorem population_checked : allCandidates.card=1 := by
  rw [allCandidates,family_count cover bounds 2 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (((1) * (x)^0 * (y)^1 + (1) * (x)^1 * (y)^0) % 4=0)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-6) (9)).product (Finset.Icc (-3) (3))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := {(0,0)}
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -6≤x ∧ x≤9 ∧ -3≤y ∧ y≤3 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
def auxiliary0 (x y : ℤ) : ℤ := (1) * (x-(0))^1 * (y-(0))^0
theorem auxiliary0_values : ∀ z ∈ points, auxiliary0 z.1 z.2=0 := by decide +kernel
theorem auxiliary0_covers (x y : ℤ) (h : -6≤x ∧ x≤9 ∧ -3≤y ∧ y≤3 ∧ accepts x y) : auxiliary0 x y=0 := auxiliary0_values (x,y) ((points_complete x y).mpr h)
#print axioms auxiliary0_values
#print axioms auxiliary0_covers
def auxiliary1 (x y : ℤ) : ℤ := (1) * (x-(0))^0 * (y-(0))^1
theorem auxiliary1_values : ∀ z ∈ points, auxiliary1 z.1 z.2=0 := by decide +kernel
theorem auxiliary1_covers (x y : ℤ) (h : -6≤x ∧ x≤9 ∧ -3≤y ∧ y≤3 ∧ accepts x y) : auxiliary1 x y=0 := auxiliary1_values (x,y) ((points_complete x y).mpr h)
#print axioms auxiliary1_values
#print axioms auxiliary1_covers
def auxiliary2 (x y : ℤ) : ℤ := (1) * (x-(0))^2 * (y-(0))^0
theorem auxiliary2_values : ∀ z ∈ points, auxiliary2 z.1 z.2=0 := by decide +kernel
theorem auxiliary2_covers (x y : ℤ) (h : -6≤x ∧ x≤9 ∧ -3≤y ∧ y≤3 ∧ accepts x y) : auxiliary2 x y=0 := auxiliary2_values (x,y) ((points_complete x y).mpr h)
#print axioms auxiliary2_values
#print axioms auxiliary2_covers
end PowerCharts_fbe7db10e106509e
