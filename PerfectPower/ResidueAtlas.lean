import PerfectPower.ResiduePopulation
import Mathlib.RingTheory.Coprime.Basic

/-! Complete bivariate residue atlases, all-coordinate source survival and
nonenumerating rectangle counts. No global height assumption. -/
namespace PerfectPower.ResidueAtlas
open scoped BigOperators

theorem pow_mod (x m : ℤ) (n : ℕ) : x^n % m = (x % m)^n % m := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, Int.mul_emod, ih, Int.emod_emod]

def rootTable (F : ℤ → ℤ → ℤ) (m : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Ico 0 m).product (Finset.Ico 0 m)).filter fun z => F z.1 z.2 % m = 0

theorem rootTable_mem (F : ℤ → ℤ → ℤ) (m x y : ℤ) :
    (x,y) ∈ rootTable F m ↔ 0 ≤ x ∧ x < m ∧ 0 ≤ y ∧ y < m ∧ F x y % m = 0 := by
  simp [rootTable, Finset.product_eq_sprod, and_assoc]

structure AtlasPacket (F : ℤ → ℤ → ℤ) (m : ℤ) where
  positive : 0 < m
  roots : Finset (ℤ × ℤ)
  checked : rootTable F m = roots
  periodic : ∀ x y, F x y % m = F (x % m) (y % m) % m

theorem AtlasPacket.canonical {F m} (atlas : AtlasPacket F m) (z : ℤ × ℤ)
    (hz : z ∈ atlas.roots) : 0 ≤ z.1 ∧ z.1 < m ∧ 0 ≤ z.2 ∧ z.2 < m := by
  rw [← atlas.checked] at hz
  have h := (rootTable_mem F m z.1 z.2).mp hz
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem AtlasPacket.complete {F m} (atlas : AtlasPacket F m) (x y : ℤ) :
    (x % m,y % m) ∈ atlas.roots ↔ F x y % m = 0 := by
  rw [← atlas.checked, rootTable_mem, ← atlas.periodic]
  simp [Int.emod_nonneg _ (ne_of_gt atlas.positive), Int.emod_lt_of_pos _ atlas.positive]

theorem AtlasPacket.source_survives {F m} (atlas : AtlasPacket F m) (x y : ℤ)
    (hF : F x y = 0) : (x % m,y % m) ∈ atlas.roots := by
  apply (atlas.complete x y).mpr
  simp [hF]

theorem AtlasPacket.empty_obstruction {F m} (atlas : AtlasPacket F m)
    (hempty : atlas.roots = ∅) (x y : ℤ) : F x y ≠ 0 := by
  intro hF
  have h := atlas.source_survives x y hF
  rw [hempty] at h
  exact Finset.notMem_empty _ h

abbrev Bounds := (ℤ × ℤ) × (ℤ × ℤ)
def xcell (bounds : Bounds) (m : ℤ) (z : ℤ × ℤ) : PerfectPower.ResiduePopulation.Cell :=
  ⟨bounds.1.1,bounds.1.2,m,z.1⟩
def ycell (bounds : Bounds) (m : ℤ) (z : ℤ × ℤ) : PerfectPower.ResiduePopulation.Cell :=
  ⟨bounds.2.1,bounds.2.2,m,z.2⟩
def cellValues (bounds : Bounds) (m : ℤ) (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (PerfectPower.ResiduePopulation.values (xcell bounds m z)).product (PerfectPower.ResiduePopulation.values (ycell bounds m z))

theorem cellValues_mem (bounds : Bounds) (m : ℤ) (z : ℤ × ℤ) (x y : ℤ) :
    (x,y) ∈ cellValues bounds m z ↔
    bounds.1.1 ≤ x ∧ x ≤ bounds.1.2 ∧ bounds.2.1 ≤ y ∧ y ≤ bounds.2.2 ∧
      x % m = z.1 ∧ y % m = z.2 := by
  simp [cellValues, Finset.product_eq_sprod, PerfectPower.ResiduePopulation.mem_values, PerfectPower.ResiduePopulation.accepts, xcell, ycell]
  tauto

theorem cellValues_disjoint (bounds : Bounds) (m : ℤ) (z w : ℤ × ℤ) (hne : z ≠ w) :
    Disjoint (cellValues bounds m z) (cellValues bounds m w) := by
  apply Finset.disjoint_left.mpr
  intro xy hz hw
  have hz' := (cellValues_mem bounds m z xy.1 xy.2).mp hz
  have hw' := (cellValues_mem bounds m w xy.1 xy.2).mp hw
  exact hne (Prod.ext (hz'.2.2.2.2.1.symm.trans hw'.2.2.2.2.1)
    (hz'.2.2.2.2.2.symm.trans hw'.2.2.2.2.2))

def candidates {F m} (atlas : AtlasPacket F m) (bounds : Bounds) : Finset (ℤ × ℤ) :=
  atlas.roots.biUnion (cellValues bounds m)

theorem candidates_complete {F m} (atlas : AtlasPacket F m) (bounds : Bounds) (x y : ℤ) :
    (x,y) ∈ candidates atlas bounds ↔
    bounds.1.1 ≤ x ∧ x ≤ bounds.1.2 ∧ bounds.2.1 ≤ y ∧ y ≤ bounds.2.2 ∧ F x y % m = 0 := by
  simp only [candidates, Finset.mem_biUnion]
  constructor
  · rintro ⟨z,hz,hxy⟩
    have h := (cellValues_mem bounds m z x y).mp hxy
    have he : (x % m,y % m) = z := Prod.ext h.2.2.2.2.1 h.2.2.2.2.2
    have hroots : (x % m,y % m) ∈ atlas.roots := by simpa only [he] using hz
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,(atlas.complete x y).mp hroots⟩
  · rintro ⟨hx0,hx1,hy0,hy1,hF⟩
    exact ⟨(x % m,y % m),(atlas.complete x y).mpr hF,
      (cellValues_mem bounds m _ x y).mpr ⟨hx0,hx1,hy0,hy1,rfl,rfl⟩⟩

theorem card_cellValues (bounds : Bounds) (m : ℤ) (z : ℤ × ℤ)
    (hm : 0 < m) (hz : 0 ≤ z.1 ∧ z.1 < m ∧ 0 ≤ z.2 ∧ z.2 < m) :
    (cellValues bounds m z).card = PerfectPower.ResiduePopulation.count (xcell bounds m z) * PerfectPower.ResiduePopulation.count (ycell bounds m z) := by
  rw [cellValues, Finset.product_eq_sprod, Finset.card_product]
  rw [PerfectPower.ResiduePopulation.card_values _ hm hz.1 hz.2.1, PerfectPower.ResiduePopulation.card_values _ hm hz.2.2.1 hz.2.2.2]

theorem card_candidates {F m} (atlas : AtlasPacket F m) (bounds : Bounds) :
    (candidates atlas bounds).card =
      ∑ z ∈ atlas.roots, PerfectPower.ResiduePopulation.count (xcell bounds m z) * PerfectPower.ResiduePopulation.count (ycell bounds m z) := by
  rw [candidates, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro z hz
    exact card_cellValues bounds m z atlas.positive (atlas.canonical z hz)
  · intro z _ w _ hne
    exact cellValues_disjoint bounds m z w hne

def solutions {F m} (atlas : AtlasPacket F m) (bounds : Bounds) : Finset (ℤ × ℤ) :=
  (candidates atlas bounds).filter fun z => F z.1 z.2 = 0

theorem solutions_complete {F m} (atlas : AtlasPacket F m) (bounds : Bounds) (x y : ℤ) :
    (x,y) ∈ solutions atlas bounds ↔
    bounds.1.1 ≤ x ∧ x ≤ bounds.1.2 ∧ bounds.2.1 ≤ y ∧ y ≤ bounds.2.2 ∧ F x y = 0 := by
  simp only [solutions, Finset.mem_filter, candidates_complete]
  constructor
  · rintro ⟨⟨hx0,hx1,hy0,hy1,_⟩,hF⟩
    exact ⟨hx0,hx1,hy0,hy1,hF⟩
  · rintro ⟨hx0,hx1,hy0,hy1,hF⟩
    exact ⟨⟨hx0,hx1,hy0,hy1,by simp [hF]⟩,hF⟩

/-- Every child digit pair is retained exactly when the original source lifts. -/
def childTable (F : ℤ → ℤ → ℤ) (p m a b : ℤ) : Finset (ℤ × ℤ) :=
  (((Finset.Ico 0 p).product (Finset.Ico 0 p)).filter
    (fun z => F (a+m*z.1) (b+m*z.2) % (m*p) = 0)).image
    (fun z => (a+m*z.1,b+m*z.2))

/-- Exact first-order identity at an arbitrary already-lifted residue. -/
structure LiftPacket (F : ℤ → ℤ → ℤ) (p m a b : ℤ) where
  constant : ℤ
  dx : ℤ
  dy : ℤ
  remainder : ℤ → ℤ → ℤ
  identity : ∀ u v, F (a+m*u) (b+m*v) =
    m*(constant+dx*u+dy*v)+m^2*remainder u v

theorem LiftPacket.step {F p m a b} (packet : LiftPacket F p m a b)
    (hm : m ≠ 0) (hpm : p ∣ m) (u v : ℤ) :
    m*p ∣ F (a+m*u) (b+m*v) ↔ p ∣ packet.constant+packet.dx*u+packet.dy*v := by
  rw [packet.identity]
  have he : m*(packet.constant+packet.dx*u+packet.dy*v)+m^2*packet.remainder u v =
    m*(packet.constant+packet.dx*u+packet.dy*v+m*packet.remainder u v) := by ring
  rw [he, mul_dvd_mul_iff_left hm]
  have hd : p ∣ m*packet.remainder u v := dvd_mul_of_dvd_left hpm _
  constructor
  · intro h
    have hs := dvd_sub h hd
    simpa using hs
  · intro h
    exact dvd_add h hd

theorem LiftPacket.horizontal_unique {F p m a b} (packet : LiftPacket F p m a b)
    (hunit : IsCoprime p packet.dx) (u w v : ℤ)
    (hu : p ∣ packet.constant+packet.dx*u+packet.dy*v)
    (hw : p ∣ packet.constant+packet.dx*w+packet.dy*v) : p ∣ u-w := by
  apply hunit.dvd_of_dvd_mul_left
  have h := dvd_sub hu hw
  convert h using 1 <;> ring

theorem LiftPacket.vertical_unique {F p m a b} (packet : LiftPacket F p m a b)
    (hunit : IsCoprime p packet.dy) (u v w : ℤ)
    (hv : p ∣ packet.constant+packet.dx*u+packet.dy*v)
    (hw : p ∣ packet.constant+packet.dx*u+packet.dy*w) : p ∣ v-w := by
  apply hunit.dvd_of_dvd_mul_left
  have h := dvd_sub hv hw
  convert h using 1 <;> ring

theorem LiftPacket.singular {F p m a b} (packet : LiftPacket F p m a b)
    (hdx : p ∣ packet.dx) (hdy : p ∣ packet.dy) (u v : ℤ) :
    p ∣ packet.constant+packet.dx*u+packet.dy*v ↔ p ∣ packet.constant := by
  have hd : p ∣ packet.dx*u+packet.dy*v := dvd_add
    (dvd_mul_of_dvd_left hdx _) (dvd_mul_of_dvd_left hdy _)
  constructor
  · intro h
    have hs := dvd_sub h hd
    convert hs using 1 <;> ring
  · intro h
    simpa [add_assoc] using dvd_add h hd

end PerfectPower.ResidueAtlas
