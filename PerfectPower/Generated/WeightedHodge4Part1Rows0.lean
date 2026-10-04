import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_1_0 : ∀ j, (hodge_4_B*hodge_4_B) 0 j = (hodge_4_B) 0 j := by decide +kernel
theorem hodge_4_row_1_1 : ∀ j, (hodge_4_B*hodge_4_B) 1 j = (hodge_4_B) 1 j := by decide +kernel
theorem hodge_4_row_1_2 : ∀ j, (hodge_4_B*hodge_4_B) 2 j = (hodge_4_B) 2 j := by decide +kernel
theorem hodge_4_row_1_3 : ∀ j, (hodge_4_B*hodge_4_B) 3 j = (hodge_4_B) 3 j := by decide +kernel
theorem hodge_4_row_1_4 : ∀ j, (hodge_4_B*hodge_4_B) 4 j = (hodge_4_B) 4 j := by decide +kernel
end PerfectPower.ParallelCertificates
