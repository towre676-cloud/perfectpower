import PerfectPower.IntegerPolynomialFibres

namespace PerfectPower.DivisorPopulation
open PolynomialFibre PerfectPower.BoundedNative

def values (k : ℤ) : Finset (ℤ × ℤ) :=
  ((FastDivisors.pairs k).image fun z => ((z.2-z.1)/2, (z.2+z.1)/2)).filter
    fun z => z.2^2 = z.1^2 + k

theorem values_complete (k p y : ℤ) (hk : k ≠ 0) :
    y^2 = p^2+k ↔ (p,y) ∈ values k := by
  constructor
  · intro h
    have hm : (y-p)*(y+p)=k := by nlinarith
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(y-p,y+p), FastDivisors.mem_pairs.mpr ⟨hm,hk⟩, ?_⟩, h⟩
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · exact fun h => (Finset.mem_filter.mp h).2

def points (as : List ℤ) (k : ℤ) : Finset (ℤ × ℤ) :=
  (values k).biUnion fun z => (IntegerPolynomialFibres.fibre as z.1).image fun x => (x,z.2)

theorem complete (as : List ℤ) (k : ℤ) (hv : valid as) (hd : 2 ≤ as.length)
    (hk : k ≠ 0) (x y : ℤ) :
    y^2 = (horner as x)^2+k ↔ (x,y) ∈ points as k := by
  constructor
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨(horner as x,y), (values_complete k _ _ hk).mp h, ?_⟩
    exact Finset.mem_image.mpr ⟨x, (IntegerPolynomialFibres.fibre_complete as _ x hv hd).mp rfl, rfl⟩
  · intro h
    obtain ⟨⟨p,v⟩, hz, hxy⟩ := Finset.mem_biUnion.mp h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hxy
    have hx : u=x := congr_arg Prod.fst he
    have hy : v=y := congr_arg Prod.snd he
    subst u
    subst v
    have hp := (IntegerPolynomialFibres.fibre_complete as p x hv hd).mpr hu
    have hh := (values_complete k p y hk).mpr hz
    simpa [hp] using hh

end PerfectPower.DivisorPopulation
