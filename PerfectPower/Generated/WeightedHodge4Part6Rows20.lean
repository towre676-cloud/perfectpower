import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_6_20 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 20 j = (hodge_4_M*hodge_4_H) 20 j := by decide +kernel
end PerfectPower.ParallelCertificates
