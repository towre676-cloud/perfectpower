import PerfectPower.Generated.GraphProbability03Moments00
import PerfectPower.Generated.GraphProbability03Moments01
import PerfectPower.Generated.GraphProbability03Moments02
import PerfectPower.Generated.GraphProbability03Moments03
import PerfectPower.Generated.GraphProbability03Moments04
import PerfectPower.Generated.GraphProbability03Moments05
import PerfectPower.Generated.GraphProbability03Moments06
import PerfectPower.Generated.GraphProbability03Moments07
namespace PerfectPower.GraphProbability03
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_checked : ∀ S, det (DeterminantalEvents.padded K S)=FiniteGraphProbability.inclusion w O S := by
  intro S
  by_cases h0 : (0 : Fin 6) ∈ S
  · by_cases h1 : (1 : Fin 6) ∈ S
    · by_cases h2 : (2 : Fin 6) ∈ S
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,2,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_063
            · have hs : S=({0,1,2,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_031
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,2,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_047
            · have hs : S=({0,1,2,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_015
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,2,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_055
            · have hs : S=({0,1,2,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_023
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,2,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_039
            · have hs : S=({0,1,2} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_007
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_059
            · have hs : S=({0,1,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_027
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_043
            · have hs : S=({0,1,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_011
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_051
            · have hs : S=({0,1,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_019
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,1,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_035
            · have hs : S=({0,1} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_003
    · by_cases h2 : (2 : Fin 6) ∈ S
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,2,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_061
            · have hs : S=({0,2,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_029
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,2,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_045
            · have hs : S=({0,2,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_013
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,2,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_053
            · have hs : S=({0,2,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_021
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,2,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_037
            · have hs : S=({0,2} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_005
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_057
            · have hs : S=({0,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_025
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_041
            · have hs : S=({0,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_009
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_049
            · have hs : S=({0,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_017
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({0,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_033
            · have hs : S=({0} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_001
  · by_cases h1 : (1 : Fin 6) ∈ S
    · by_cases h2 : (2 : Fin 6) ∈ S
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,2,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_062
            · have hs : S=({1,2,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_030
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,2,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_046
            · have hs : S=({1,2,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_014
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,2,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_054
            · have hs : S=({1,2,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_022
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,2,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_038
            · have hs : S=({1,2} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_006
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_058
            · have hs : S=({1,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_026
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_042
            · have hs : S=({1,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_010
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_050
            · have hs : S=({1,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_018
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({1,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_034
            · have hs : S=({1} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_002
    · by_cases h2 : (2 : Fin 6) ∈ S
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({2,3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_060
            · have hs : S=({2,3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_028
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({2,3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_044
            · have hs : S=({2,3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_012
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({2,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_052
            · have hs : S=({2,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_020
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({2,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_036
            · have hs : S=({2} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_004
      · by_cases h3 : (3 : Fin 6) ∈ S
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({3,4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_056
            · have hs : S=({3,4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_024
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({3,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_040
            · have hs : S=({3} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_008
        · by_cases h4 : (4 : Fin 6) ∈ S
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({4,5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_048
            · have hs : S=({4} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_016
          · by_cases h5 : (5 : Fin 6) ∈ S
            · have hs : S=({5} : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_032
            · have hs : S=(∅ : Finset (Fin 6)) := by
                ext i; fin_cases i <;> simp_all
              rw [hs]
              exact inclusion_000
theorem all_events (I J : Finset (Fin 6)) (h : Disjoint I J) :
    DeterminantalEvents.mixed K I J=FiniteGraphProbability.eventMass w O I J :=
  FiniteGraphProbability.mixed_probability w O K inclusion_checked I J h
theorem probability_bounds (I J : Finset (Fin 6)) (h : Disjoint I J) :
    0 ≤ DeterminantalEvents.mixed K I J ∧ DeterminantalEvents.mixed K I J ≤ 1 := by
  rw [all_events I J h]
  exact FiniteGraphProbability.rational_event_bounds w O nonnegative normalized I J
end PerfectPower.GraphProbability03
