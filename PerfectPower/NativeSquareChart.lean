import PerfectPower.SolutionChart
import PerfectPower.NativeDivisorSquare

namespace PerfectPower.NativeSquareChart
open NativePolynomialSquare SolutionChart

def relation (as : List ℤ) (k : ℤ) (z : ℤ × ℤ) : Prop :=
  z.2^2 = (eval as z.1)^2+k

def parameter (as : List ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (eval as z.1, z.2)

def fibre (as : List ℤ) (b : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (NativePolynomialRoots.fibre as b.1).image fun x => (x,b.2)

theorem fibre_exact (as : List ℤ) (k : ℤ) (hv : valid as) (hd : 2 ≤ as.length)
    (hk : k ≠ 0) (b : ℤ × ℤ) (hb : b ∈ NativeDivisorSquare.values k) (a : ℤ × ℤ) :
    a ∈ fibre as b ↔ relation as k a ∧ parameter as a = b := by
  rcases a with ⟨x,y⟩
  rcases b with ⟨p,v⟩
  have hvv := (NativeDivisorSquare.values_complete k p v hk).mpr hb
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    have hx : u = x := congr_arg Prod.fst he
    have hy : v = y := congr_arg Prod.snd he
    subst u
    subst v
    have hp := (NativePolynomialRoots.fibre_complete as p x hv hd).mpr hu
    exact ⟨by simpa [relation, hp] using hvv, by simp [parameter, hp]⟩
  · rintro ⟨_, he⟩
    have hp : eval as x = p := congr_arg Prod.fst he
    have hy : y = v := congr_arg Prod.snd he
    exact Finset.mem_image.mpr
      ⟨x, (NativePolynomialRoots.fibre_complete as p x hv hd).mp hp,
        by simp [hy]⟩

/-- Any subset of closed parameter fibres gives a certified partial answer. -/
def chart (as : List ℤ) (k : ℤ) (hv : valid as) (hd : 2 ≤ as.length) (hk : k ≠ 0)
    (closed : Finset (ℤ × ℤ)) (hclosed : closed ⊆ NativeDivisorSquare.values k) :
    Chart (β := ℤ × ℤ) (relation as k) where
  parameter := parameter as
  parameters := NativeDivisorSquare.values k
  covered _ h := (NativeDivisorSquare.values_complete k _ _ hk).mp h
  solved := closed
  solved_subset := hclosed
  fibre := fibre as
  fibre_exact b hb a := fibre_exact as k hv hd hk b (hclosed hb) a

theorem full_known (as : List ℤ) (k : ℤ) (hv : valid as) (hd : 2 ≤ as.length)
    (hk : k ≠ 0) :
    (chart as k hv hd hk (NativeDivisorSquare.values k) (fun _ h => h)).known =
      NativeDivisorSquare.points as k := rfl

end PerfectPower.NativeSquareChart
