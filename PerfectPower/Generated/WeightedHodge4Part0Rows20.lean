import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_0_20 : ∀ j, (hodge_4_G*hodge_4_G) 20 j = (hodge_4_G) 20 j := by decide +kernel
end PerfectPower.ParallelCertificates
