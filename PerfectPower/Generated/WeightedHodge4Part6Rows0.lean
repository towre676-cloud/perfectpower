import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_6_0 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 0 j = (hodge_4_M*hodge_4_H) 0 j := by decide +kernel
theorem hodge_4_row_6_1 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 1 j = (hodge_4_M*hodge_4_H) 1 j := by decide +kernel
theorem hodge_4_row_6_2 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 2 j = (hodge_4_M*hodge_4_H) 2 j := by decide +kernel
theorem hodge_4_row_6_3 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 3 j = (hodge_4_M*hodge_4_H) 3 j := by decide +kernel
theorem hodge_4_row_6_4 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 4 j = (hodge_4_M*hodge_4_H) 4 j := by decide +kernel
end PerfectPower.ParallelCertificates
