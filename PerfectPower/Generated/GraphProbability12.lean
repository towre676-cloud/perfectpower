import PerfectPower.Generated.GraphProbability12Moments00
namespace PerfectPower.GraphProbability12
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_checked : ∀ S, det (DeterminantalEvents.padded K S)=FiniteGraphProbability.inclusion w O S := by
  intro S
  by_cases h0 : (0 : Fin 3) ∈ S
  · by_cases h1 : (1 : Fin 3) ∈ S
    · by_cases h2 : (2 : Fin 3) ∈ S
      · have hs : S=({0,1,2} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_007
      · have hs : S=({0,1} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_003
    · by_cases h2 : (2 : Fin 3) ∈ S
      · have hs : S=({0,2} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_005
      · have hs : S=({0} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_001
  · by_cases h1 : (1 : Fin 3) ∈ S
    · by_cases h2 : (2 : Fin 3) ∈ S
      · have hs : S=({1,2} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_006
      · have hs : S=({1} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_002
    · by_cases h2 : (2 : Fin 3) ∈ S
      · have hs : S=({2} : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_004
      · have hs : S=(∅ : Finset (Fin 3)) := by
          ext i; fin_cases i <;> simp_all
        rw [hs]
        exact inclusion_000
theorem all_events (I J : Finset (Fin 3)) (h : Disjoint I J) :
    DeterminantalEvents.mixed K I J=FiniteGraphProbability.eventMass w O I J :=
  FiniteGraphProbability.mixed_probability w O K inclusion_checked I J h
theorem probability_bounds (I J : Finset (Fin 3)) (h : Disjoint I J) :
    0 ≤ DeterminantalEvents.mixed K I J ∧ DeterminantalEvents.mixed K I J ≤ 1 := by
  rw [all_events I J h]
  exact FiniteGraphProbability.rational_event_bounds w O nonnegative normalized I J
end PerfectPower.GraphProbability12
