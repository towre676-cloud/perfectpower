import PerfectPower.ResidueAtlasIntersectionFactored
import PerfectPower.IntegerValuedPolynomial

namespace PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
open scoped BigOperators

/-- The rational power relation is exactly the denominator-cleared integer equation. -/
theorem rational_power_iff (F L y : ℤ) (d : ℕ) (hL : L≠0) :
    (F : ℚ)/(L : ℚ)=(y : ℚ)^d ↔ F=L*y^d := by
  have hq : (L : ℚ)≠0 := by exact_mod_cast hL
  rw [div_eq_iff hq]
  constructor
  · intro h
    have hi : F=y^d*L := by exact_mod_cast h
    simpa only [mul_comm] using hi
  · intro h
    have hi : F=y^d*L := by simpa only [mul_comm] using h
    exact_mod_cast hi

/-- A denominator-clearing identity in the original two coordinates. -/
structure ChartPacket (F G : ℤ → ℤ → ℤ) (L r : ℤ) where
  positive : 0<L
  identity : ∀ n y, F (r+L*n) y=L*G n y

theorem ChartPacket.source_iff {F G L r} (chart : ChartPacket F G L r) (n y : ℤ) :
    F (r+L*n) y=0 ↔ G n y=0 := by
  rw [chart.identity,mul_eq_zero]
  simp [ne_of_gt chart.positive]

/-- A denominator prime requires L*m in the original source, not merely m. -/
theorem ChartPacket.congruence_iff {F G L r} (chart : ChartPacket F G L r)
    (m n y : ℤ) : L*m ∣ F (r+L*n) y ↔ m ∣ G n y := by
  rw [chart.identity]
  exact mul_dvd_mul_iff_left (ne_of_gt chart.positive)

/-- Exact signed parameter bounds for the affine integer chart. -/
def parameterBounds (bounds : Bounds) (L r : ℤ) : Bounds :=
  (((bounds.1.1-1-r)/L+1,(bounds.1.2-r)/L),bounds.2)

theorem parameter_bounds (bounds : Bounds) (L r n : ℤ) (hL : 0<L) :
    bounds.1.1≤r+L*n ∧ r+L*n≤bounds.1.2 ↔
    (parameterBounds bounds L r).1.1≤n ∧ n≤(parameterBounds bounds L r).1.2 := by
  unfold parameterBounds
  rw [show (bounds.1.1-1-r)/L+1≤n ↔ (bounds.1.1-1-r)/L<n by omega,
    Int.ediv_lt_iff_lt_mul hL,Int.le_ediv_iff_mul_le hL]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

def original (L r : ℤ) (z : ℤ×ℤ) : ℤ×ℤ := (r+L*z.1,z.2)

theorem original_injective (L r : ℤ) (hL : 0<L) : Function.Injective (original L r) := by
  intro z w h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    simp only [original] at hx
    exact mul_left_cancel₀ (ne_of_gt hL) (add_left_cancel hx)
  · simpa only [original] using congrArg (fun q : ℤ×ℤ => q.2) h

/-- The original-coordinate candidate set, without enumerating the original rectangle. -/
def chartCandidates {P m} (cover : CoverPacket P m) (bounds : Bounds) (L r : ℤ) : Finset (ℤ×ℤ) :=
  (candidates cover (parameterBounds bounds L r)).image (original L r)

theorem chart_count {P m} (cover : CoverPacket P m) (bounds : Bounds) (L r : ℤ) (hL : 0<L) :
    (chartCandidates cover bounds L r).card =
      ∑ z ∈ cover.roots,
        PerfectPower.ResiduePopulation.count (PerfectPower.ResidueAtlas.xcell (parameterBounds bounds L r) m z)*
        PerfectPower.ResiduePopulation.count (PerfectPower.ResidueAtlas.ycell (parameterBounds bounds L r) m z) := by
  rw [chartCandidates,Finset.card_image_of_injective _ (original_injective L r hL),card_candidates]

theorem chart_complete {P m} (cover : CoverPacket P m) (bounds : Bounds) (L r x y : ℤ)
    (hL : 0<L) :
    (x,y) ∈ chartCandidates cover bounds L r ↔
      bounds.1.1≤x ∧ x≤bounds.1.2 ∧ bounds.2.1≤y ∧ y≤bounds.2.2 ∧
      ∃ n : ℤ, x=r+L*n ∧ P n y := by
  constructor
  · intro hz
    obtain ⟨⟨n,v⟩,hn,he⟩ := Finset.mem_image.mp hz
    have hx : r+L*n=x := congrArg Prod.fst he
    have hy : v=y := congrArg Prod.snd he
    have hb := (candidates_complete cover (parameterBounds bounds L r) n v).mp hn
    have ho := (parameter_bounds bounds L r n hL).mpr ⟨hb.1,hb.2.1⟩
    exact ⟨hx ▸ ho.1,hx ▸ ho.2,hy ▸ hb.2.2.1,hy ▸ hb.2.2.2.1,
      n,hx.symm,hy ▸ hb.2.2.2.2⟩
  · rintro ⟨hx0,hx1,hy0,hy1,n,rfl,hP⟩
    apply Finset.mem_image.mpr
    refine ⟨(n,y),?_,rfl⟩
    have hb := (parameter_bounds bounds L r n hL).mp ⟨hx0,hx1⟩
    exact (candidates_complete cover (parameterBounds bounds L r) n y).mpr
      ⟨hb.1,hb.2,hy0,hy1,hP⟩

theorem chart_disjoint {P Q m k} (left : CoverPacket P m) (right : CoverPacket Q k)
    (bounds : Bounds) (L r s : ℤ) (hr : 0≤r ∧ r<L) (hs : 0≤s ∧ s<L) (hne : r≠s) :
    Disjoint (chartCandidates left bounds L r) (chartCandidates right bounds L s) := by
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hw
  have hx := congrArg (fun q : ℤ×ℤ => q.1%L) (ha.trans hb.symm)
  simp only [original,Int.add_mul_emod_self_left,Int.emod_eq_of_lt hr.1 hr.2,
    Int.emod_eq_of_lt hs.1 hs.2] at hx
  exact hne hx

/-- Transport of the actual quotient power equation on its integral chart. -/
theorem quotient_power_iff (f g : Polynomial ℤ) (L r d : ℕ) (hL : L≠0)
    (hc : f.comp (Polynomial.C (r : ℤ)+Polynomial.C (L : ℤ)*Polynomial.X) = Polynomial.C (L : ℤ)*g)
    (n y : ℤ) :
    PerfectPower.IntegerValuedPolynomial.quotientValue f L ((r : ℤ)+(L : ℤ)*n)=y^d ↔ g.eval n=y^d := by
  rw [PerfectPower.IntegerValuedPolynomial.chart_quotient f g L r hL hc n]

def familyCandidates {ι : Type*} [Fintype ι] {P : ι → ℤ → ℤ → Prop} {m : ι → ℤ}
    (covers : ∀ i, CoverPacket (P i) (m i)) (bounds : Bounds) (L : ℤ) (r : ι → ℤ) : Finset (ℤ×ℤ) :=
  Finset.univ.biUnion fun i => chartCandidates (covers i) bounds L (r i)

theorem family_complete {ι : Type*} [Fintype ι] {P : ι → ℤ → ℤ → Prop} {m : ι → ℤ}
    (covers : ∀ i, CoverPacket (P i) (m i)) (bounds : Bounds) (L : ℤ) (r : ι → ℤ)
    (hL : 0<L) (x y : ℤ) :
    (x,y) ∈ familyCandidates covers bounds L r ↔
      bounds.1.1≤x ∧ x≤bounds.1.2 ∧ bounds.2.1≤y ∧ y≤bounds.2.2 ∧
      ∃ i, ∃ n : ℤ, x=r i+L*n ∧ P i n y := by
  simp only [familyCandidates,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨hx0,hx1,hy0,hy1,n,hx,hP⟩ := (chart_complete (covers i) bounds L (r i) x y hL).mp hi
    exact ⟨hx0,hx1,hy0,hy1,i,n,hx,hP⟩
  · rintro ⟨hx0,hx1,hy0,hy1,i,n,hx,hP⟩
    exact ⟨i,(chart_complete (covers i) bounds L (r i) x y hL).mpr
      ⟨hx0,hx1,hy0,hy1,n,hx,hP⟩⟩

theorem family_count {ι : Type*} [Fintype ι] {P : ι → ℤ → ℤ → Prop} {m : ι → ℤ}
    (covers : ∀ i, CoverPacket (P i) (m i)) (bounds : Bounds) (L : ℤ) (r : ι → ℤ)
    (hL : 0<L) (hr : ∀ i, 0≤r i ∧ r i<L) (hi : Function.Injective r) :
    (familyCandidates covers bounds L r).card = ∑ i, ∑ z ∈ (covers i).roots,
      PerfectPower.ResiduePopulation.count (PerfectPower.ResidueAtlas.xcell (parameterBounds bounds L (r i)) (m i) z)*
      PerfectPower.ResiduePopulation.count (PerfectPower.ResidueAtlas.ycell (parameterBounds bounds L (r i)) (m i) z) := by
  rw [familyCandidates,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact chart_count (covers i) bounds L (r i) hL
  · intro i _ j _ hne
    exact chart_disjoint (covers i) (covers j) bounds L (r i) (r j) (hr i) (hr j) (hi.ne hne)

end PerfectPower.RationalPowerAtlas
