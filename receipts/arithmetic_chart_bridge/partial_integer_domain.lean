import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_b6ab2c4bb17e0ae4
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (4) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (1,2), (2,1), (2,2)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (4)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-1,1),(-3,3))
theorem count_checked : (candidates atlas1 bounds).card = 11 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 3,y % 3) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-2), (-1,2), (0,0), (1,-2), (1,2)}
theorem points_checked : solutions atlas1 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -1 ≤ x ∧ x ≤ 1 ∧ -3 ≤ y ∧ y ≤ 3 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas1 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_b6ab2c4bb17e0ae4
namespace Intersection_dcb776484262e9dd
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_b6ab2c4bb17e0ae4.F x y % 3 = 0) 3 := ofAtlas Atlas_b6ab2c4bb17e0ae4.atlas1
def group0_0 : CoverPacket (fun x y => Atlas_b6ab2c4bb17e0ae4.F x y % 3 = 0) 3 := local0
theorem group_roots0 : group0_0.roots = {(0,0), (1,1), (1,2), (2,1), (2,2)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => Atlas_b6ab2c4bb17e0ae4.F x y % 3 = 0) 3 := group0_0
def bounds : Bounds := ((-1,1),(-3,3))
def S (x y : ℤ) : Prop := Atlas_b6ab2c4bb17e0ae4.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 3,y % 3) ∈ stage0.roots ↔ Atlas_b6ab2c4bb17e0ae4.F x y % 3 = 0 := stage0.complete x y
theorem roots_count : stage0.roots.card = 5 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 11 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : Atlas_b6ab2c4bb17e0ae4.F x y % 3 = 0 := by
  simp only [S] at h
  have h0 := h
  simp only [h0, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 3,y % 3) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-1,-2), (-1,2), (0,0), (1,-2), (1,2)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -1≤x ∧ x≤1 ∧ -3≤y ∧ y≤3 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_dcb776484262e9dd
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_1a440ed5999b9a8d
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^0 + (-1) * (x)^0 * (y)^2 + (4) * (x)^1 * (y)^0 + (4) * (x)^2 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,1), (0,2), (1,0), (2,1), (2,2)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact ((((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy))).add (((Int.ModEq.refl (4)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy))).add (((Int.ModEq.refl (4)).mul (Int.ModEq.pow 2 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-2,1),(-3,3))
theorem count_checked : (candidates atlas1 bounds).card = 14 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 3,y % 3) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-2,-3), (-2,3), (-1,-1), (-1,1), (0,-1), (0,1), (1,-3), (1,3)}
theorem points_checked : solutions atlas1 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -2 ≤ x ∧ x ≤ 1 ∧ -3 ≤ y ∧ y ≤ 3 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas1 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_1a440ed5999b9a8d
namespace Intersection_5aaf90f16f08043f
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_1a440ed5999b9a8d.F x y % 3 = 0) 3 := ofAtlas Atlas_1a440ed5999b9a8d.atlas1
def group0_0 : CoverPacket (fun x y => Atlas_1a440ed5999b9a8d.F x y % 3 = 0) 3 := local0
theorem group_roots0 : group0_0.roots = {(0,1), (0,2), (1,0), (2,1), (2,2)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => Atlas_1a440ed5999b9a8d.F x y % 3 = 0) 3 := group0_0
def bounds : Bounds := ((-2,1),(-3,3))
def S (x y : ℤ) : Prop := Atlas_1a440ed5999b9a8d.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 3,y % 3) ∈ stage0.roots ↔ Atlas_1a440ed5999b9a8d.F x y % 3 = 0 := stage0.complete x y
theorem roots_count : stage0.roots.card = 5 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 14 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : Atlas_1a440ed5999b9a8d.F x y % 3 = 0 := by
  simp only [S] at h
  have h0 := h
  simp only [h0, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 3,y % 3) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(-2,-3), (-2,3), (-1,-1), (-1,1), (0,-1), (0,1), (1,-3), (1,3)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -2≤x ∧ x≤1 ∧ -3≤y ∧ y≤3 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_5aaf90f16f08043f
namespace PowerCharts_8466f56502328c77
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-4) * (x)^0 * (y)^2 + (1) * (x)^2 * (y)^0
def bounds : Bounds := ((-6,6),(-3,3))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (4) * (n)^2 * (y)^0
theorem identity0 (n y : ℤ) : F (0+4*n) y=4*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 4 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+4*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 4*m ∣ F (0+4*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_dcb776484262e9dd.stage0 bounds 4 0
theorem count0 : candidates0.card=11 := by
  rw [candidates0,chart_count Intersection_dcb776484262e9dd.stage0 bounds 4 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def G1 (n y : ℤ) : ℤ := (1) * (n)^0 * (y)^0 + (-1) * (n)^0 * (y)^2 + (4) * (n)^1 * (y)^0 + (4) * (n)^2 * (y)^0
theorem identity1 (n y : ℤ) : F (2+4*n) y=4*G1 n y := by unfold F G1; ring
def chart1 : ChartPacket F G1 4 2 := ⟨by norm_num,identity1⟩
theorem source_transport1 (n y : ℤ) : F (2+4*n) y=0 ↔ G1 n y=0 := chart1.source_iff n y
theorem denominator_transport1 (m n y : ℤ) : 4*m ∣ F (2+4*n) y ↔ m ∣ G1 n y := chart1.congruence_iff m n y
def candidates1 := chartCandidates Intersection_5aaf90f16f08043f.stage0 bounds 4 2
theorem count1 : candidates1.card=14 := by
  rw [candidates1,chart_count Intersection_5aaf90f16f08043f.stage0 bounds 4 2 (by norm_num)]; decide +kernel
#print axioms identity1
#print axioms source_transport1
#print axioms denominator_transport1
#print axioms count1
def residue (i : Fin 2) : ℤ := if i.val=0 then 0 else 2
def P (i : Fin 2) (x y : ℤ) : Prop := if i.val=0 then (Atlas_b6ab2c4bb17e0ae4.F x y % 3 = 0) else (Atlas_1a440ed5999b9a8d.F x y % 3 = 0)
def cover : (i : Fin 2) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 3 := Fin.cases Intersection_dcb776484262e9dd.stage0 (Fin.cases Intersection_5aaf90f16f08043f.stage0 ((fun i => Fin.elim0 i)))
theorem residue_canonical : ∀ i : Fin 2, 0≤residue i ∧ residue i<4 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 4 residue
theorem population_checked : allCandidates.card=25 := by
  rw [allCandidates,family_count cover bounds 4 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (True)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-6) (6)).product (Finset.Icc (-3) (3))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := {(-6,-3), (-6,3), (-4,-2), (-4,2), (-2,-1), (-2,1), (0,0), (2,-1), (2,1), (4,-2), (4,2), (6,-3), (6,3)}
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -6≤x ∧ x≤6 ∧ -3≤y ∧ y≤3 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
end PowerCharts_8466f56502328c77
