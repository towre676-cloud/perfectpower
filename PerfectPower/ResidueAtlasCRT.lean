import PerfectPower.ResidueAtlas
import Mathlib.Data.Int.ModEq

namespace PerfectPower.ResidueAtlasCRT
open PerfectPower.ResidueAtlas
open scoped BigOperators

def coordinate (m n u v a b : ℤ) : ℤ := (a*(n*v)+b*(m*u)) % (m*n)

theorem coordinate_left (m n u v a b : ℤ) (h : u*m+v*n=1) :
    coordinate m n u v a b % m = a % m := by
  have hc : Int.ModEq m (a*(n*v)+b*(m*u)) a := by
    apply Int.modEq_of_dvd
    refine ⟨u*(a-b), ?_⟩
    calc
      a-(a*(n*v)+b*(m*u)) = a*(1-(u*m+v*n))+m*(u*(a-b)) := by ring
      _ = m*(u*(a-b)) := by rw [h]; ring
  exact ((Int.mod_modEq _ (m*n)).of_mul_right n).trans hc

theorem coordinate_right (m n u v a b : ℤ) (h : u*m+v*n=1) :
    coordinate m n u v a b % n = b % n := by
  have hc : Int.ModEq n (a*(n*v)+b*(m*u)) b := by
    apply Int.modEq_of_dvd
    refine ⟨v*(b-a), ?_⟩
    calc
      b-(a*(n*v)+b*(m*u)) = b*(1-(u*m+v*n))+n*(v*(b-a)) := by ring
      _ = n*(v*(b-a)) := by rw [h]; ring
  exact ((Int.mod_modEq _ (m*n)).of_mul_left m).trans hc

theorem coordinate_canonical (m n u v a b : ℤ) (hm : 0<m) (hn : 0<n) :
    0 ≤ coordinate m n u v a b ∧ coordinate m n u v a b < m*n := by
  exact ⟨Int.emod_nonneg _ (ne_of_gt (mul_pos hm hn)),Int.emod_lt_of_pos _ (mul_pos hm hn)⟩

theorem coordinate_recover (m n u v x : ℤ) (hm : 0<m) (hn : 0<n)
    (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) :
    coordinate m n u v (x%m) (x%n) = x%(m*n) := by
  have hl : Int.ModEq m (coordinate m n u v (x%m) (x%n)) x := by
    simpa [Int.ModEq] using coordinate_left m n u v (x%m) (x%n) h
  have hr : Int.ModEq n (coordinate m n u v (x%m) (x%n)) x := by
    simpa [Int.ModEq] using coordinate_right m n u v (x%m) (x%n) h
  have hc := (Int.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hl,hr⟩
  have hb := coordinate_canonical m n u v (x%m) (x%n) hm hn
  simpa [Int.ModEq,Int.emod_eq_of_lt hb.1 hb.2] using hc

def pair (m n u v : ℤ) (z w : ℤ × ℤ) : ℤ × ℤ :=
  (coordinate m n u v z.1 w.1,coordinate m n u v z.2 w.2)

def roots {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n) (u v : ℤ) : Finset (ℤ × ℤ) :=
  (left.roots.product right.roots).image (fun zw => pair m n u v zw.1 zw.2)

theorem pair_left {F m} (left : AtlasPacket F m) (n u v : ℤ) (z w : ℤ × ℤ)
    (hz : z ∈ left.roots) (h : u*m+v*n=1) :
    ((pair m n u v z w).1%m,(pair m n u v z w).2%m) = z := by
  have hc := left.canonical z hz
  apply Prod.ext
  · simpa [pair,coordinate_left _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.1 hc.2.1]
  · simpa [pair,coordinate_left _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.2.2.1 hc.2.2.2]

theorem pair_right {F n} (right : AtlasPacket F n) (m u v : ℤ) (z w : ℤ × ℤ)
    (hw : w ∈ right.roots) (h : u*m+v*n=1) :
    ((pair m n u v z w).1%n,(pair m n u v z w).2%n) = w := by
  have hc := right.canonical w hw
  apply Prod.ext
  · simpa [pair,coordinate_right _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.1 hc.2.1]
  · simpa [pair,coordinate_right _ _ _ _ _ _ h,Int.emod_eq_of_lt hc.2.2.1 hc.2.2.2]

theorem roots_card {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n)
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

theorem roots_complete {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n)
    (u v : ℤ) (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) (x y : ℤ) :
    (x%(m*n),y%(m*n)) ∈ roots left right u v ↔
      F x y % m = 0 ∧ F x y % n = 0 := by
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

theorem product_zero (m n z : ℤ) (hco : m.natAbs.Coprime n.natAbs) :
    z%(m*n)=0 ↔ z%m=0 ∧ z%n=0 := by
  simpa [Int.ModEq] using (Int.modEq_and_modEq_iff_modEq_mul (a:=z) (b:=0) hco).symm

theorem merged_periodic {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n)
    (hco : m.natAbs.Coprime n.natAbs) (x y : ℤ) :
    F x y % (m*n) = F (x%(m*n)) (y%(m*n)) % (m*n) := by
  have hl : Int.ModEq m (F x y) (F (x%(m*n)) (y%(m*n))) := by
    change F x y % m = F (x%(m*n)) (y%(m*n)) % m
    rw [left.periodic x y,left.periodic (x%(m*n)) (y%(m*n)),Int.mod_mul_right_mod,Int.mod_mul_right_mod]
  have hr : Int.ModEq n (F x y) (F (x%(m*n)) (y%(m*n))) := by
    change F x y % n = F (x%(m*n)) (y%(m*n)) % n
    rw [right.periodic x y,right.periodic (x%(m*n)) (y%(m*n)),Int.mod_mul_left_mod,Int.mod_mul_left_mod]
  exact (Int.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hl,hr⟩

theorem merged_checked {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n)
    (u v : ℤ) (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) :
    rootTable F (m*n) = roots left right u v := by
  ext z
  constructor
  · intro hz
    have hb := (rootTable_mem F (m*n) z.1 z.2).mp hz
    have hm : (z.1%(m*n),z.2%(m*n)) = z := Prod.ext
      (Int.emod_eq_of_lt hb.1 hb.2.1) (Int.emod_eq_of_lt hb.2.2.1 hb.2.2.2.1)
    rw [← hm]
    exact (roots_complete left right u v hco h z.1 z.2).mpr ((product_zero m n _ hco).mp hb.2.2.2.2)
  · intro hz
    obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hz
    have hx := coordinate_canonical m n u v a.1 b.1 left.positive right.positive
    have hy := coordinate_canonical m n u v a.2 b.2 left.positive right.positive
    apply (rootTable_mem F (m*n) _ _).mpr
    refine ⟨hx.1,hx.2,hy.1,hy.2,?_⟩
    apply (product_zero m n _ hco).mpr
    apply (roots_complete left right u v hco h _ _).mp
    simpa [pair,Int.emod_eq_of_lt hx.1 hx.2,Int.emod_eq_of_lt hy.1 hy.2] using hz

def merge {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n)
    (u v : ℤ) (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) : AtlasPacket F (m*n) :=
  ⟨mul_pos left.positive right.positive,roots left right u v,
    merged_checked left right u v hco h,merged_periodic left right hco⟩

theorem merged_count {F m n} (left : AtlasPacket F m) (right : AtlasPacket F n)
    (u v : ℤ) (hco : m.natAbs.Coprime n.natAbs) (h : u*m+v*n=1) (bounds : Bounds) :
    (candidates (merge left right u v hco h) bounds).card =
      ∑ z ∈ left.roots, ∑ w ∈ right.roots,
        PerfectPower.ResiduePopulation.count (xcell bounds (m*n) (pair m n u v z w)) *
        PerfectPower.ResiduePopulation.count (ycell bounds (m*n) (pair m n u v z w)) := by
  have hinj : Set.InjOn (fun zw : (ℤ × ℤ) × (ℤ × ℤ) => pair m n u v zw.1 zw.2)
      (left.roots.product right.roots) := by
    apply Finset.card_image_iff.mp
    simpa only [roots,Finset.product_eq_sprod,Finset.card_product] using roots_card left right u v h
  rw [card_candidates]
  change (∑ q ∈ (left.roots.product right.roots).image (fun zw => pair m n u v zw.1 zw.2),
    PerfectPower.ResiduePopulation.count (xcell bounds (m*n) q) *
    PerfectPower.ResiduePopulation.count (ycell bounds (m*n) q)) = _
  rw [Finset.sum_image]
  · rw [Finset.product_eq_sprod,Finset.sum_product]
  · exact hinj

end PerfectPower.ResidueAtlasCRT
