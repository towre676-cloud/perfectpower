import PerfectPower.MordellMinus2Core
import PerfectPower.AffinePopulation

namespace PerfectPower.GlobalMordellPopulation

/-- The complete source population, globally over both integer coordinates. -/
def points : List (Int × Int) := [(3,-5),(3,5)]

theorem complete (p : Int × Int) : p ∈ points ↔ p.2^2 = p.1^3-2 := by
  rw [PerfectPower.MordellMinus2.points]
  simp [points, Prod.ext_iff]
  tauto

theorem affine_complete (a b : Int) (ha : a ≠ 0) (p : Int × Int) :
    p ∈ PerfectPower.AffinePopulation.pullback points a b ↔
      p.2^2 = (a*p.1+b)^3-2 :=
  PerfectPower.AffinePopulation.pullback_complete points _ complete a b ha p

end PerfectPower.GlobalMordellPopulation
