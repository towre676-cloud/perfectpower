import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_1_0 : ∀ j, (hodge_7_B*hodge_7_B) 0 j = (hodge_7_B) 0 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_1 : ∀ j, (hodge_7_B*hodge_7_B) 1 j = (hodge_7_B) 1 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_2 : ∀ j, (hodge_7_B*hodge_7_B) 2 j = (hodge_7_B) 2 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_3 : ∀ j, (hodge_7_B*hodge_7_B) 3 j = (hodge_7_B) 3 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_4 : ∀ j, (hodge_7_B*hodge_7_B) 4 j = (hodge_7_B) 4 j := by
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
