import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_1_5 : ∀ j, (hodge_7_B*hodge_7_B) 5 j = (hodge_7_B) 5 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_6 : ∀ j, (hodge_7_B*hodge_7_B) 6 j = (hodge_7_B) 6 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_7 : ∀ j, (hodge_7_B*hodge_7_B) 7 j = (hodge_7_B) 7 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_8 : ∀ j, (hodge_7_B*hodge_7_B) 8 j = (hodge_7_B) 8 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_9 : ∀ j, (hodge_7_B*hodge_7_B) 9 j = (hodge_7_B) 9 j := by
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
