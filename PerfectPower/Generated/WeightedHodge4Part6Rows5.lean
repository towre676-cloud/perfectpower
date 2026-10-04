import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_6_5 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 5 j = (hodge_4_M*hodge_4_H) 5 j := by decide +kernel
theorem hodge_4_row_6_6 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 6 j = (hodge_4_M*hodge_4_H) 6 j := by decide +kernel
theorem hodge_4_row_6_7 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 7 j = (hodge_4_M*hodge_4_H) 7 j := by decide +kernel
theorem hodge_4_row_6_8 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 8 j = (hodge_4_M*hodge_4_H) 8 j := by decide +kernel
theorem hodge_4_row_6_9 : ∀ j, (hodge_4_H.transpose*hodge_4_M) 9 j = (hodge_4_M*hodge_4_H) 9 j := by decide +kernel
end PerfectPower.ParallelCertificates
