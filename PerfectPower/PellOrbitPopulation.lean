import PerfectPower.PellOrbitCore
import PerfectPower.PellFamily
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

namespace PerfectPower.PellOrbitPopulation
open PellOrbitCore

theorem orbit_power {D : ℤ} (a : Pell.Solution₁ D) (s : ℤ × ℤ) (k : ℕ) :
    unitOrbit D a.x a.y s k = unitAct D (a^k).x (a^k).y s := by
  induction k with
  | zero => simp [unitOrbit,unitAct]
  | succ k ih =>
    rw [orbit_succ,ih,pow_succ,Pell.Solution₁.x_mul,Pell.Solution₁.y_mul]
    ext <;> simp only [unitAct] <;> ring

def fastOrbit {D : ℤ} (a : Pell.Solution₁ D) (s : ℤ × ℤ) (fuel k : ℕ) : ℤ × ℤ :=
  unitAct D (PellFamily.fastPower a fuel k).x (PellFamily.fastPower a fuel k).y s

theorem fastOrbit_eq {D : ℤ} (a : Pell.Solution₁ D) (s : ℤ × ℤ) (fuel k : ℕ)
    (hk : k < 2^fuel) : fastOrbit a s fuel k = unitOrbit D a.x a.y s k := by
  rw [fastOrbit,PellFamily.fastPower_eq a fuel k hk,orbit_power]

def seeds (D A B N Xcap Ycap : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc 1 Xcap).product (Finset.Icc 0 Ycap)).filter fun p =>
    p.1^2-D*p.2^2=N ∧ terminal D A B p

theorem seed_complete {D A B N Xcap Ycap : ℤ}
    (hD : 0 < D) (hA : 1 < A) (hB : 0 < B) (hu : A^2-D*B^2=1)
    (hX : 0 ≤ Xcap) (hY : 0 ≤ Ycap)
    (hxgap : |N| * A^2+|N| < (Xcap+1)^2)
    (hygap : |N| * A^2 < D*(Ycap+1)^2) (p : ℤ × ℤ) :
    p ∈ seeds D A B N Xcap Ycap ↔
      0 < p.1 ∧ 0 ≤ p.2 ∧ p.1^2-D*p.2^2=N ∧ terminal D A B p := by
  constructor
  · intro h
    obtain ⟨hp,hn,ht⟩ := Finset.mem_filter.mp h
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    obtain ⟨hx0,hx1⟩ := Finset.mem_Icc.mp hx
    obtain ⟨hy0,hy1⟩ := Finset.mem_Icc.mp hy
    exact ⟨by omega,hy0,hn,ht⟩
  · rintro ⟨hx,hy,hn,ht⟩
    have hb := terminal_bound hD hA hB hu p hx hy hn ht
    have hxc : p.1 ≤ Xcap := by
      by_contra h
      have hh : Xcap+1 ≤ p.1 := by omega
      nlinarith [le_abs_self N]
    have hyc : p.2 ≤ Ycap := by
      by_contra h
      have hh : Ycap+1 ≤ p.2 := by omega
      have hs : (Ycap+1)^2 ≤ p.2^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs hD.le
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,hxc⟩,Finset.mem_Icc.mpr ⟨hy,hyc⟩⟩,hn,ht⟩

def positivePopulation (D A B cutoff : ℤ) (S : Finset (ℤ × ℤ))
    (length : (ℤ × ℤ) → ℕ) : Finset (ℤ × ℤ) :=
  (S.biUnion fun s => (Finset.range (length s)).image fun k =>
    ((unitOrbit D A B s k).2,(unitOrbit D A B s k).1)).filter fun p => p.1 ≤ cutoff

/-- Boundary certificates for every representative close the entire finite union. -/
theorem positive_complete {D A B N cutoff : ℤ}
    (hD : 0 < D) (hA : 1 < A) (hB : 0 < B) (hu : A^2-D*B^2=1)
    (S : Finset (ℤ × ℤ)) (length : (ℤ × ℤ) → ℕ)
    (hS : ∀ s, s ∈ S ↔ 0 < s.1 ∧ 0 ≤ s.2 ∧ s.1^2-D*s.2^2=N ∧ terminal D A B s)
    (hb : ∀ s ∈ S, cutoff < (unitOrbit D A B s (length s)).2) (p : ℤ × ℤ) :
    p ∈ positivePopulation D A B cutoff S length ↔
      0 ≤ p.1 ∧ 0 < p.2 ∧ p.1 ≤ cutoff ∧ p.2^2-D*p.1^2=N := by
  simp only [positivePopulation,Finset.mem_filter,Finset.mem_biUnion,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨⟨s,hs,k,hk,he⟩,hcut⟩
    obtain ⟨hx,hy,hn,ht⟩ := (hS s).mp hs
    obtain ⟨hpX,hpY⟩ := orbit_nonneg hD hA hB s hx hy k
    have hpN := (unitOrbit_norm hu s k).trans hn
    cases p
    cases he
    exact ⟨hpY,hpX,hcut,hpN⟩
  · rintro ⟨hy,hx,hcut,hn⟩
    obtain ⟨s,h1,h2,h3,h4,h5,k,hk⟩ := terminal_exhaust hD hA hB hu p.2 p.1 hx hy hn
    have hs := (hS s).mpr ⟨h1,h2,h3,h5⟩
    have hlen : k < length s := by
      by_contra hh
      have hm := (orbit_input_strictMono hD hA hB s h1 h2).monotone (show length s ≤ k by omega)
      have hnext := hb s hs
      rw [hk] at hm
      simp only [Prod.snd] at hm
      omega
    exact ⟨⟨s,hs,k,hlen,by rw [hk]⟩,hcut⟩

def zeroPopulation (D N cutoff : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc 0 |N|).filter fun y => y ≤ cutoff ∧ -D*y^2=N).image fun y => (y,0)

theorem zero_complete {D N cutoff : ℤ} (hD : 0 < D) (p : ℤ × ℤ) :
    p ∈ zeroPopulation D N cutoff ↔
      0 ≤ p.1 ∧ p.2=0 ∧ p.1 ≤ cutoff ∧ p.2^2-D*p.1^2=N := by
  simp only [zeroPopulation,Finset.mem_image,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨y,⟨⟨hy,hcap⟩,hcut,hn⟩,rfl⟩
    exact ⟨hy,rfl,hcut,by simpa using hn⟩
  · rintro ⟨hy,hz,hcut,hn⟩
    have hn' : -D*p.1^2=N := by simpa [hz] using hn
    have hcap : p.1 ≤ |N| := by
      have : D ≥ 1 := by omega
      have hm := mul_le_mul_of_nonneg_right this (sq_nonneg p.1)
      nlinarith [neg_abs_le N]
    exact ⟨p.1,⟨⟨hy,hcap⟩,hcut,hn'⟩,by ext <;> simp [hz]⟩

theorem nonnegative_complete {D N cutoff : ℤ}
    (P : Finset (ℤ × ℤ))
    (hp : ∀ p, p ∈ P ↔ 0 ≤ p.1 ∧ 0 < p.2 ∧ p.1 ≤ cutoff ∧ p.2^2-D*p.1^2=N)
    (hD : 0 < D) (p : ℤ × ℤ) :
    p ∈ P ∪ zeroPopulation D N cutoff ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ cutoff ∧ p.2^2-D*p.1^2=N := by
  rw [Finset.mem_union,hp,zero_complete hD]
  constructor
  · rintro (h | h) <;> rcases h with ⟨h1,h2,h3,h4⟩ <;> exact ⟨h1,by omega,h3,h4⟩
  · rintro ⟨h1,h2,h3,h4⟩
    by_cases hz : p.2=0
    · exact Or.inr ⟨h1,hz,h3,h4⟩
    · exact Or.inl ⟨h1,by omega,h3,h4⟩

def signedPopulation (P : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  P.biUnion fun p => (PellFamily.signVariants p).toFinset

theorem signed_complete {D N cutoff : ℤ} (P : Finset (ℤ × ℤ))
    (hp : ∀ p, p ∈ P ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ cutoff ∧ p.2^2-D*p.1^2=N)
    (p : ℤ × ℤ) : p ∈ signedPopulation P ↔ |p.1| ≤ cutoff ∧ p.2^2-D*p.1^2=N := by
  simp only [signedPopulation,Finset.mem_biUnion,List.mem_toFinset,PellFamily.mem_signVariants]
  constructor
  · rintro ⟨s,hs,hx,hy⟩
    obtain ⟨h1,h2,h3,h4⟩ := (hp s).mp hs
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx,hy,abs_of_nonneg h1,h3,h4]
  · rintro ⟨hcut,hn⟩
    refine ⟨(|p.1|,|p.2|),(hp _).mpr ⟨abs_nonneg _,abs_nonneg _,hcut,by simpa only [sq_abs] using hn⟩,?_,?_⟩
    · rcases le_total 0 p.1 with h | h
      · exact Or.inl (abs_of_nonneg h).symm
      · exact Or.inr (by rw [abs_of_nonpos h,neg_neg])
    · rcases le_total 0 p.2 with h | h
      · exact Or.inl (abs_of_nonneg h).symm
      · exact Or.inr (by rw [abs_of_nonpos h,neg_neg])
end PerfectPower.PellOrbitPopulation
