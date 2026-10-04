import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_1_20 : ∀ j, (hodge_7_B*hodge_7_B) 20 j = (hodge_7_B) 20 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_21 : ∀ j, (hodge_7_B*hodge_7_B) 21 j = (hodge_7_B) 21 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_22 : ∀ j, (hodge_7_B*hodge_7_B) 22 j = (hodge_7_B) 22 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_23 : ∀ j, (hodge_7_B*hodge_7_B) 23 j = (hodge_7_B) 23 j := by
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_1_24 : ∀ j, (hodge_7_B*hodge_7_B) 24 j = (hodge_7_B) 24 j := by
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
