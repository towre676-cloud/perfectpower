import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_04c4b621fe6e4bc0
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
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-4,4),(-4,4))
theorem count_checked : (candidates atlas2 bounds).card = 23 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 4,y % 4) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1), (4,-2), (4,2)}
theorem points_checked : solutions atlas2 bounds = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔
    -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4 ∧ F x y = 0 := by
  rw [← points_checked]; exact solutions_complete atlas2 bounds x y
#print axioms points_checked
#print axioms points_complete
end Atlas_04c4b621fe6e4bc0
namespace Intersection_58341097f5a519bb
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_04c4b621fe6e4bc0.F x y % 4 = 0) 4 := ofAtlas Atlas_04c4b621fe6e4bc0.atlas2
def group0_0 : CoverPacket (fun x y => Atlas_04c4b621fe6e4bc0.F x y % 4 = 0) 4 := local0
theorem group_roots0 : group0_0.roots = {(0,0), (0,2), (1,1), (1,3)} := by decide +kernel
#print axioms group_roots0
def stage0 : CoverPacket (fun x y => Atlas_04c4b621fe6e4bc0.F x y % 4 = 0) 4 := group0_0
def bounds : Bounds := ((-4,4),(-4,4))
def S (x y : ℤ) : Prop := Atlas_04c4b621fe6e4bc0.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 4,y % 4) ∈ stage0.roots ↔ Atlas_04c4b621fe6e4bc0.F x y % 4 = 0 := stage0.complete x y
theorem roots_count : stage0.roots.card = 4 := by decide +kernel
theorem count_checked : (candidates stage0 bounds).card = 23 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : Atlas_04c4b621fe6e4bc0.F x y % 4 = 0 := by
  simp only [S] at h
  have h0 := h
  simp only [h0, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 4,y % 4) ∈ stage0.roots := (stage0.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
def points : Finset (ℤ × ℤ) := {(0,0), (1,-1), (1,1), (4,-2), (4,2)}
theorem points_checked : solutions stage0 bounds S = points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -4≤x ∧ x≤4 ∧ -4≤y ∧ y≤4 ∧ S x y := by
  rw [← points_checked]; exact solutions_complete stage0 bounds S source_implies x y
#print axioms points_checked
#print axioms points_complete
end Intersection_58341097f5a519bb
namespace PowerCharts_0c4fa050321a56b9
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0
def bounds : Bounds := ((-8,8),(-4,4))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (1) * (n)^1 * (y)^0
theorem identity0 (n y : ℤ) : F (0+2*n) y=2*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 2 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+2*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 2*m ∣ F (0+2*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_58341097f5a519bb.stage0 bounds 2 0
theorem count0 : candidates0.card=23 := by
  rw [candidates0,chart_count Intersection_58341097f5a519bb.stage0 bounds 2 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def residue (i : Fin 1) : ℤ := 0
def P (i : Fin 1) (x y : ℤ) : Prop := (Atlas_04c4b621fe6e4bc0.F x y % 4 = 0)
def cover : (i : Fin 1) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 4 := Fin.cases Intersection_58341097f5a519bb.stage0 ((fun i => Fin.elim0 i))
theorem residue_canonical : ∀ i : Fin 1, 0≤residue i ∧ residue i<2 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 2 residue
theorem population_checked : allCandidates.card=23 := by
  rw [allCandidates,family_count cover bounds 2 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (True)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-8) (8)).product (Finset.Icc (-4) (4))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := {(0,0), (2,-1), (2,1), (8,-2), (8,2)}
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -8≤x ∧ x≤8 ∧ -4≤y ∧ y≤4 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
end PowerCharts_0c4fa050321a56b9
