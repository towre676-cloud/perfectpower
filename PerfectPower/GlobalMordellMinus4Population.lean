import PerfectPower.MordellMinus4Core
import PerfectPower.AffinePopulation

namespace PerfectPower.GlobalMordellMinus4Population

def points : List (Int × Int) := [(2,-2),(2,2),(5,-11),(5,11)]

theorem complete (p : Int × Int) : p ∈ points ↔ p.2^2 = p.1^3-4 := by
  rw [PerfectPower.MordellMinus4.points]
  simp [points, Prod.ext_iff]
  tauto

theorem affine_complete (a b : Int) (ha : a ≠ 0) (p : Int × Int) :
    p ∈ PerfectPower.AffinePopulation.pullback points a b ↔
      p.2^2 = (a*p.1+b)^3-4 :=
  PerfectPower.AffinePopulation.pullback_complete points _ complete a b ha p

end PerfectPower.GlobalMordellMinus4Population
