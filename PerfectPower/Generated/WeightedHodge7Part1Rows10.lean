import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_1_10 : ∀ j, (hodge_7_B*hodge_7_B) 10 j = (hodge_7_B) 10 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_11 : ∀ j, (hodge_7_B*hodge_7_B) 11 j = (hodge_7_B) 11 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_12 : ∀ j, (hodge_7_B*hodge_7_B) 12 j = (hodge_7_B) 12 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_13 : ∀ j, (hodge_7_B*hodge_7_B) 13 j = (hodge_7_B) 13 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_14 : ∀ j, (hodge_7_B*hodge_7_B) 14 j = (hodge_7_B) 14 j := by
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
