import PerfectPower.Generated.GraphProbability10Moments00
import PerfectPower.Generated.GraphProbability10Moments01
namespace PerfectPower.GraphProbability10
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_checked : ∀ S, det (DeterminantalEvents.padded K S)=FiniteGraphProbability.inclusion w O S := by
  intro S
  by_cases h0 : (0 : Fin 4) ∈ S
  · by_cases h1 : (1 : Fin 4) ∈ S
    · by_cases h2 : (2 : Fin 4) ∈ S
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({0,1,2,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_015
        · have hs : S=({0,1,2} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_007
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({0,1,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_011
        · have hs : S=({0,1} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_003
    · by_cases h2 : (2 : Fin 4) ∈ S
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({0,2,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_013
        · have hs : S=({0,2} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_005
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({0,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_009
        · have hs : S=({0} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_001
  · by_cases h1 : (1 : Fin 4) ∈ S
    · by_cases h2 : (2 : Fin 4) ∈ S
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({1,2,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_014
        · have hs : S=({1,2} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_006
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({1,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_010
        · have hs : S=({1} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_002
    · by_cases h2 : (2 : Fin 4) ∈ S
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({2,3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_012
        · have hs : S=({2} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_004
      · by_cases h3 : (3 : Fin 4) ∈ S
        · have hs : S=({3} : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_008
        · have hs : S=(∅ : Finset (Fin 4)) := by
            ext i; fin_cases i <;> simp_all
          rw [hs]
          exact inclusion_000
theorem all_events (I J : Finset (Fin 4)) (h : Disjoint I J) :
    DeterminantalEvents.mixed K I J=FiniteGraphProbability.eventMass w O I J :=
  FiniteGraphProbability.mixed_probability w O K inclusion_checked I J h
theorem probability_bounds (I J : Finset (Fin 4)) (h : Disjoint I J) :
    0 ≤ DeterminantalEvents.mixed K I J ∧ DeterminantalEvents.mixed K I J ≤ 1 := by
  rw [all_events I J h]
  exact FiniteGraphProbability.rational_event_bounds w O nonnegative normalized I J
end PerfectPower.GraphProbability10
