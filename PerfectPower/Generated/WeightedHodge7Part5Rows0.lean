import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_5_0 : ∀ j, (hodge_7_L*hodge_7_H) 0 j = ((0 : Matrix (Fin 39) (Fin 39) ℚ)) 0 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_5_1 : ∀ j, (hodge_7_L*hodge_7_H) 1 j = ((0 : Matrix (Fin 39) (Fin 39) ℚ)) 1 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_5_2 : ∀ j, (hodge_7_L*hodge_7_H) 2 j = ((0 : Matrix (Fin 39) (Fin 39) ℚ)) 2 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_5_3 : ∀ j, (hodge_7_L*hodge_7_H) 3 j = ((0 : Matrix (Fin 39) (Fin 39) ℚ)) 3 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_5_4 : ∀ j, (hodge_7_L*hodge_7_H) 4 j = ((0 : Matrix (Fin 39) (Fin 39) ℚ)) 4 j := by
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
