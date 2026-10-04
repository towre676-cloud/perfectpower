import PerfectPower.Generated.GraphProbability04Moments00
import PerfectPower.Generated.GraphProbability04Moments01
import PerfectPower.Generated.GraphProbability04Moments02
import PerfectPower.Generated.GraphProbability04Moments03
import PerfectPower.Generated.GraphProbability04Moments04
import PerfectPower.Generated.GraphProbability04Moments05
import PerfectPower.Generated.GraphProbability04Moments06
import PerfectPower.Generated.GraphProbability04Moments07
import PerfectPower.Generated.GraphProbability04Moments08
import PerfectPower.Generated.GraphProbability04Moments09
import PerfectPower.Generated.GraphProbability04Moments10
import PerfectPower.Generated.GraphProbability04Moments11
import PerfectPower.Generated.GraphProbability04Moments12
import PerfectPower.Generated.GraphProbability04Moments13
import PerfectPower.Generated.GraphProbability04Moments14
import PerfectPower.Generated.GraphProbability04Moments15
namespace PerfectPower.GraphProbability04
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_checked : ∀ S, det (DeterminantalEvents.padded K S)=FiniteGraphProbability.inclusion w O S := by
  intro S
  by_cases h0 : (0 : Fin 7) ∈ S
  · by_cases h1 : (1 : Fin 7) ∈ S
    · by_cases h2 : (2 : Fin 7) ∈ S
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_127
              · have hs : S=({0,1,2,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_063
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_095
              · have hs : S=({0,1,2,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_031
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_111
              · have hs : S=({0,1,2,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_047
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_079
              · have hs : S=({0,1,2,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_015
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_119
              · have hs : S=({0,1,2,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_055
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_087
              · have hs : S=({0,1,2,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_023
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_103
              · have hs : S=({0,1,2,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_039
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,2,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_071
              · have hs : S=({0,1,2} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_007
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_123
              · have hs : S=({0,1,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_059
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_091
              · have hs : S=({0,1,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_027
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_107
              · have hs : S=({0,1,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_043
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_075
              · have hs : S=({0,1,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_011
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_115
              · have hs : S=({0,1,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_051
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_083
              · have hs : S=({0,1,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_019
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_099
              · have hs : S=({0,1,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_035
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,1,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_067
              · have hs : S=({0,1} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_003
    · by_cases h2 : (2 : Fin 7) ∈ S
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_125
              · have hs : S=({0,2,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_061
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_093
              · have hs : S=({0,2,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_029
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_109
              · have hs : S=({0,2,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_045
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_077
              · have hs : S=({0,2,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_013
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_117
              · have hs : S=({0,2,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_053
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_085
              · have hs : S=({0,2,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_021
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_101
              · have hs : S=({0,2,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_037
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,2,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_069
              · have hs : S=({0,2} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_005
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_121
              · have hs : S=({0,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_057
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_089
              · have hs : S=({0,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_025
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_105
              · have hs : S=({0,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_041
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_073
              · have hs : S=({0,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_009
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_113
              · have hs : S=({0,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_049
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_081
              · have hs : S=({0,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_017
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_097
              · have hs : S=({0,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_033
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({0,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_065
              · have hs : S=({0} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_001
  · by_cases h1 : (1 : Fin 7) ∈ S
    · by_cases h2 : (2 : Fin 7) ∈ S
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_126
              · have hs : S=({1,2,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_062
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_094
              · have hs : S=({1,2,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_030
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_110
              · have hs : S=({1,2,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_046
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_078
              · have hs : S=({1,2,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_014
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_118
              · have hs : S=({1,2,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_054
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_086
              · have hs : S=({1,2,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_022
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_102
              · have hs : S=({1,2,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_038
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,2,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_070
              · have hs : S=({1,2} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_006
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_122
              · have hs : S=({1,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_058
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_090
              · have hs : S=({1,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_026
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_106
              · have hs : S=({1,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_042
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_074
              · have hs : S=({1,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_010
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_114
              · have hs : S=({1,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_050
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_082
              · have hs : S=({1,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_018
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_098
              · have hs : S=({1,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_034
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({1,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_066
              · have hs : S=({1} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_002
    · by_cases h2 : (2 : Fin 7) ∈ S
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_124
              · have hs : S=({2,3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_060
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_092
              · have hs : S=({2,3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_028
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_108
              · have hs : S=({2,3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_044
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_076
              · have hs : S=({2,3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_012
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_116
              · have hs : S=({2,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_052
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_084
              · have hs : S=({2,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_020
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_100
              · have hs : S=({2,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_036
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({2,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_068
              · have hs : S=({2} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_004
      · by_cases h3 : (3 : Fin 7) ∈ S
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({3,4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_120
              · have hs : S=({3,4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_056
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({3,4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_088
              · have hs : S=({3,4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_024
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({3,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_104
              · have hs : S=({3,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_040
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({3,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_072
              · have hs : S=({3} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_008
        · by_cases h4 : (4 : Fin 7) ∈ S
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({4,5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_112
              · have hs : S=({4,5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_048
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({4,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_080
              · have hs : S=({4} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_016
          · by_cases h5 : (5 : Fin 7) ∈ S
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({5,6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_096
              · have hs : S=({5} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_032
            · by_cases h6 : (6 : Fin 7) ∈ S
              · have hs : S=({6} : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_064
              · have hs : S=(∅ : Finset (Fin 7)) := by
                  ext i; fin_cases i <;> simp_all
                rw [hs]
                exact inclusion_000
theorem all_events (I J : Finset (Fin 7)) (h : Disjoint I J) :
    DeterminantalEvents.mixed K I J=FiniteGraphProbability.eventMass w O I J :=
  FiniteGraphProbability.mixed_probability w O K inclusion_checked I J h
theorem probability_bounds (I J : Finset (Fin 7)) (h : Disjoint I J) :
    0 ≤ DeterminantalEvents.mixed K I J ∧ DeterminantalEvents.mixed K I J ≤ 1 := by
  rw [all_events I J h]
  exact FiniteGraphProbability.rational_event_bounds w O nonnegative normalized I J
end PerfectPower.GraphProbability04
