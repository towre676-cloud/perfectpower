import PerfectPower.ResidueAtlasCRT

namespace PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas
open scoped BigOperators

/-- A complete modular cover for a predicate, allowing several original sources. -/
structure CoverPacket (P : ℤ → ℤ → Prop) (m : ℤ) where
  positive : 0<m
  roots : Finset (ℤ×ℤ)
  canonical : ∀ z ∈ roots, 0≤z.1 ∧ z.1<m ∧ 0≤z.2 ∧ z.2<m
  complete : ∀ x y, (x%m,y%m) ∈ roots ↔ P x y

def ofAtlas {F m} (atlas : AtlasPacket F m) :
    CoverPacket (fun x y => F x y%m=0) m :=
  ⟨atlas.positive,atlas.roots,atlas.canonical,atlas.complete⟩

/-- Reduction commutes through any divisor, including negative coordinates. -/
theorem reduce_divisor (m n x : ℤ) (hnm : n∣m) : (x%m)%n=x%n :=
  ((Int.mod_modEq x m).of_dvd hnm).eq

/-- Shared-prime powers are nested: retain the stronger residues that project correctly. -/
def nestedRoots {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n) :
    Finset (ℤ×ℤ) := left.roots.filter fun z => (z.1%n,z.2%n) ∈ right.roots

theorem nested_complete {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n)
    (hnm : n∣m) (x y : ℤ) :
    (x%m,y%m) ∈ nestedRoots left right ↔ P x y ∧ Q x y := by
  simp only [nestedRoots,Finset.mem_filter,reduce_divisor m n x hnm,
    reduce_divisor m n y hnm,left.complete,right.complete]

def nested {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n)
    (hnm : n∣m) : CoverPacket (fun x y => P x y ∧ Q x y) m where
  positive := left.positive
  roots := nestedRoots left right
  canonical z hz := left.canonical z (Finset.mem_filter.mp hz).1
  complete := nested_complete left right hnm

theorem nested_card_le {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n) :
    (nestedRoots left right).card≤left.roots.card := Finset.card_filter_le _ _

open PerfectPower.ResidueAtlasCRT (pair coordinate_left coordinate_right coordinate_canonical coordinate_recover)

def roots {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n) (u v : ℤ) : Finset (ℤ × ℤ) :=
  (left.roots.product right.roots).image (fun zw => pair m n u v zw.1 zw.2)

theorem pair_left {P m} (left : CoverPacket P m) (n u v : ℤ) (z w : ℤ × ℤ)
    (hz : z ∈ left.roots) (h : u*m+v*n=1) :
    ((pair m n u v z w).1%m,(pair m n u v z w).2%m) = z := by
  have hc := left.canonical z hz
  apply Prod.ext
  · simpa [pair,coordinate_left _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.1 hc.2.1]
  · simpa [pair,coordinate_left _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.2.2.1 hc.2.2.2]

theorem pair_right {Q n} (right : CoverPacket Q n) (m u v : ℤ) (z w : ℤ × ℤ)
    (hw : w ∈ right.roots) (h : u*m+v*n=1) :
    ((pair m n u v z w).1%n,(pair m n u v z w).2%n) = w := by
  have hc := right.canonical w hw
  apply Prod.ext
  · simpa [pair,coordinate_right _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.1 hc.2.1]
  · simpa [pair,coordinate_right _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.2.2.1 hc.2.2.2]

theorem roots_card {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n)
    (u v : ℤ) (h : u*m+v*n=1) :
    (roots left right u v).card = left.roots.card*right.roots.card := by
  rw [roots,Finset.card_image_of_injOn,Finset.product_eq_sprod,Finset.card_product]
  intro zw hz tw ht he
  have hz' := Finset.mem_product.mp hz
  have ht' := Finset.mem_product.mp ht
  apply Prod.ext
  · have hh := congrArg (fun q : ℤ × ℤ => (q.1%m,q.2%m)) he
    simpa only [pair_left left n u v zw.1 zw.2 hz'.1 h,
      pair_left left n u v tw.1 tw.2 ht'.1 h] using hh
  · have hh := congrArg (fun q : ℤ × ℤ => (q.1%n,q.2%n)) he
    simpa only [pair_right right m u v zw.1 zw.2 hz'.2 h,
      pair_right right m u v tw.1 tw.2 ht'.2 h] using hh

theorem roots_complete {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n)
    (u v : ℤ) (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) (x y : ℤ) :
    (x%(m*n),y%(m*n)) ∈ roots left right u v ↔
      P x y ∧ Q x y := by
  constructor
  · intro hz
    obtain ⟨⟨z,w⟩,hzw,he⟩ := Finset.mem_image.mp hz
    have hzw' := Finset.mem_product.mp (show (z,w) ∈ left.roots ×ˢ right.roots from hzw)
    have hxl : x%m=z.1 := by
      have hh := congrArg (fun q : ℤ × ℤ => q.1%m) he
      simpa [pair,coordinate_left _ _ _ _ _ _ h,Int.mod_mul_right_mod,
        Int.emod_eq_of_lt (left.canonical z hzw'.1).1 (left.canonical z hzw'.1).2.1] using hh.symm
    have hyl : y%m=z.2 := by
      have hh := congrArg (fun q : ℤ × ℤ => q.2%m) he
      simpa [pair,coordinate_left _ _ _ _ _ _ h,Int.mod_mul_right_mod,
        Int.emod_eq_of_lt (left.canonical z hzw'.1).2.2.1 (left.canonical z hzw'.1).2.2.2] using hh.symm
    have hxr : x%n=w.1 := by
      have hh := congrArg (fun q : ℤ × ℤ => q.1%n) he
      simpa [pair,coordinate_right _ _ _ _ _ _ h,Int.mod_mul_left_mod,
        Int.emod_eq_of_lt (right.canonical w hzw'.2).1 (right.canonical w hzw'.2).2.1] using hh.symm
    have hyr : y%n=w.2 := by
      have hh := congrArg (fun q : ℤ × ℤ => q.2%n) he
      simpa [pair,coordinate_right _ _ _ _ _ _ h,Int.mod_mul_left_mod,
        Int.emod_eq_of_lt (right.canonical w hzw'.2).2.2.1 (right.canonical w hzw'.2).2.2.2] using hh.symm
    constructor
    · apply (left.complete x y).mp
      simpa [hxl,hyl] using hzw'.1
    · apply (right.complete x y).mp
      simpa [hxr,hyr] using hzw'.2
  · rintro ⟨hl,hr⟩
    apply Finset.mem_image.mpr
    refine ⟨((x%m,y%m),(x%n,y%n)),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨(left.complete x y).mpr hl,(right.complete x y).mpr hr⟩
    · exact Prod.ext (coordinate_recover m n u v x left.positive right.positive hco h)
        (coordinate_recover m n u v y left.positive right.positive hco h)

def merge {P Q m n} (left : CoverPacket P m) (right : CoverPacket Q n)
    (u v : ℤ) (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) :
    CoverPacket (fun x y => P x y ∧ Q x y) (m*n) where
  positive := mul_pos left.positive right.positive
  roots := roots left right u v
  canonical z hz := by
    obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hz
    have hx := coordinate_canonical m n u v a.1 b.1 left.positive right.positive
    have hy := coordinate_canonical m n u v a.2 b.2 left.positive right.positive
    exact ⟨hx.1,hx.2,hy.1,hy.2⟩
  complete := roots_complete left right u v hco h

/-- Exact empty-intersection obstruction for all original coordinates. -/
theorem CoverPacket.empty_obstruction {P m} (cover : CoverPacket P m)
    (he : cover.roots=∅) (x y : ℤ) : ¬ P x y := by
  intro h
  have hz := (cover.complete x y).mpr h
  rw [he] at hz
  exact Finset.notMem_empty _ hz

def candidates {P m} (cover : CoverPacket P m) (bounds : Bounds) : Finset (ℤ×ℤ) :=
  cover.roots.biUnion (cellValues bounds m)

theorem candidates_complete {P m} (cover : CoverPacket P m) (bounds : Bounds) (x y : ℤ) :
    (x,y) ∈ candidates cover bounds ↔
      bounds.1.1≤x ∧ x≤bounds.1.2 ∧ bounds.2.1≤y ∧ y≤bounds.2.2 ∧ P x y := by
  simp only [candidates,Finset.mem_biUnion]
  constructor
  · rintro ⟨z,hz,hxy⟩
    have h := (cellValues_mem bounds m z x y).mp hxy
    have he : (x%m,y%m)=z := Prod.ext h.2.2.2.2.1 h.2.2.2.2.2
    have hr : (x%m,y%m) ∈ cover.roots := by simpa only [he] using hz
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,(cover.complete x y).mp hr⟩
  · rintro ⟨hx0,hx1,hy0,hy1,hP⟩
    exact ⟨(x%m,y%m),(cover.complete x y).mpr hP,
      (cellValues_mem bounds m _ x y).mpr ⟨hx0,hx1,hy0,hy1,rfl,rfl⟩⟩

theorem card_candidates {P m} (cover : CoverPacket P m) (bounds : Bounds) :
    (candidates cover bounds).card=∑ z ∈ cover.roots,
      PerfectPower.ResiduePopulation.count (xcell bounds m z)*
      PerfectPower.ResiduePopulation.count (ycell bounds m z) := by
  rw [candidates,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro z hz
    exact card_cellValues bounds m z cover.positive (cover.canonical z hz)
  · intro z _ w _ hne
    exact cellValues_disjoint bounds m z w hne

/-- Exact simultaneous source solutions inside a declared rectangle. -/
def solutions {P m} (cover : CoverPacket P m) (bounds : Bounds)
    (S : ℤ → ℤ → Prop) [DecidablePred (fun z : ℤ×ℤ => S z.1 z.2)] : Finset (ℤ×ℤ) :=
  (candidates cover bounds).filter fun z => S z.1 z.2

theorem solutions_complete {P m} (cover : CoverPacket P m) (bounds : Bounds)
    (S : ℤ → ℤ → Prop) [DecidablePred (fun z : ℤ×ℤ => S z.1 z.2)]
    (survives : ∀ x y, S x y → P x y) (x y : ℤ) :
    (x,y) ∈ solutions cover bounds S ↔
      bounds.1.1≤x ∧ x≤bounds.1.2 ∧ bounds.2.1≤y ∧ y≤bounds.2.2 ∧ S x y := by
  simp only [solutions,Finset.mem_filter,candidates_complete]
  constructor
  · rintro ⟨⟨hx0,hx1,hy0,hy1,_⟩,hs⟩
    exact ⟨hx0,hx1,hy0,hy1,hs⟩
  · rintro ⟨hx0,hx1,hy0,hy1,hs⟩
    exact ⟨⟨hx0,hx1,hy0,hy1,survives x y hs⟩,hs⟩

end PerfectPower.ResidueAtlasIntersectionFactored
