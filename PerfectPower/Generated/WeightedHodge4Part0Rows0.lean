import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_0_0 : ∀ j, (hodge_4_G*hodge_4_G) 0 j = (hodge_4_G) 0 j := by decide +kernel
theorem hodge_4_row_0_1 : ∀ j, (hodge_4_G*hodge_4_G) 1 j = (hodge_4_G) 1 j := by decide +kernel
theorem hodge_4_row_0_2 : ∀ j, (hodge_4_G*hodge_4_G) 2 j = (hodge_4_G) 2 j := by decide +kernel
theorem hodge_4_row_0_3 : ∀ j, (hodge_4_G*hodge_4_G) 3 j = (hodge_4_G) 3 j := by decide +kernel
theorem hodge_4_row_0_4 : ∀ j, (hodge_4_G*hodge_4_G) 4 j = (hodge_4_G) 4 j := by decide +kernel
end PerfectPower.ParallelCertificates
