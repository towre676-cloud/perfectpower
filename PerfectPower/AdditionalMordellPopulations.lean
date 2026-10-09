import PerfectPower.MordellMinus5Core
import PerfectPower.MordellMinus6Core
import PerfectPower.MordellMinus13Core

namespace PerfectPower.AdditionalMordellMinus5
def points : List (Int × Int) := []
theorem complete (p : Int × Int) : p ∈ points ↔ p.2^2 = p.1^3-5 := by
  simp only [points,List.not_mem_nil,false_iff]
  exact PerfectPower.MordellMinus5.no_points p.1 p.2
end PerfectPower.AdditionalMordellMinus5

namespace PerfectPower.AdditionalMordellMinus6
def points : List (Int × Int) := []
theorem complete (p : Int × Int) : p ∈ points ↔ p.2^2 = p.1^3-6 := by
  simp only [points,List.not_mem_nil,false_iff]
  exact PerfectPower.MordellMinus6.no_points p.1 p.2
end PerfectPower.AdditionalMordellMinus6

namespace PerfectPower.AdditionalMordellMinus13
def points : List (Int × Int) := [(17,-70),(17,70)]
theorem complete (p : Int × Int) : p ∈ points ↔ p.2^2 = p.1^3-13 := by
  rw [PerfectPower.MordellMinus13.points]
  simp [points,Prod.ext_iff]
  tauto
end PerfectPower.AdditionalMordellMinus13
