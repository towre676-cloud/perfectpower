import PerfectPower.Tactic.NativePolynomialPower

namespace PerfectPower.Showcase.hidden_needle
open NativePolynomialSquare
native_polynomial_square canonical for [0, -2, 0, 2], 25

def translated : Finset (ℤ × ℤ) := canonical.image fun p => (p.1 + (1000000000000000000000000000000), p.2)

theorem coordinate_identity (x : ℤ) :
    eval [-1999999999999999999999999999999999999999999999999999999999998000000000000000000000000000000, 5999999999999999999999999999999999999999999999999999999999998, -6000000000000000000000000000000, 2] x = eval [0, -2, 0, 2] (x - (1000000000000000000000000000000)) := by
  simp only [eval]
  ring

theorem original_complete (x y : ℤ) :
    y^2 = (eval [-1999999999999999999999999999999999999999999999999999999999998000000000000000000000000000000, 5999999999999999999999999999999999999999999999999999999999998, -6000000000000000000000000000000, 2] x)^2 + (25) ↔ (x,y) ∈ translated := by
  rw [coordinate_identity, canonical_complete]
  simp only [translated, Finset.mem_image]
  constructor
  · intro h
    refine ⟨(x - (1000000000000000000000000000000), y), h, ?_⟩
    ext <;> simp
  · rintro ⟨⟨t,w⟩, h, heq⟩
    have hx : t + (1000000000000000000000000000000) = x := congrArg Prod.fst heq
    have hy : w = y := congrArg Prod.snd heq
    have ht : x - (1000000000000000000000000000000) = t := by omega
    simpa [ht, hy] using h

#print axioms original_complete
end PerfectPower.Showcase.hidden_needle
