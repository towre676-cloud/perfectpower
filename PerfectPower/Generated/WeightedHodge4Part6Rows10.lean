import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_6_10 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 10 j = (hodge_4_M*hodge_4_H) 10 j := by decide +kernel
theorem hodge_4_row_6_11 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 11 j = (hodge_4_M*hodge_4_H) 11 j := by decide +kernel
theorem hodge_4_row_6_12 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 12 j = (hodge_4_M*hodge_4_H) 12 j := by decide +kernel
theorem hodge_4_row_6_13 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 13 j = (hodge_4_M*hodge_4_H) 13 j := by decide +kernel
theorem hodge_4_row_6_14 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 14 j = (hodge_4_M*hodge_4_H) 14 j := by decide +kernel
end PerfectPower.ParallelCertificates
