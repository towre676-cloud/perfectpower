import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_2_20 : ∀ j, (hodge_4_G*hodge_4_B) 20 j = ((0 : Matrix (Fin 21) (Fin 21) ℚ)) 20 j := by decide +kernel
end PerfectPower.ParallelCertificates
