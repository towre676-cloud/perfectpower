import PerfectPower.Generated.WeightedHodge4Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_row_2_0 : ∀ j, (hodge_4_G*hodge_4_B) 0 j = ((0 : Matrix (Fin 21) (Fin 21) ℚ)) 0 j := by decide +kernel
theorem hodge_4_row_2_1 : ∀ j, (hodge_4_G*hodge_4_B) 1 j = ((0 : Matrix (Fin 21) (Fin 21) ℚ)) 1 j := by decide +kernel
theorem hodge_4_row_2_2 : ∀ j, (hodge_4_G*hodge_4_B) 2 j = ((0 : Matrix (Fin 21) (Fin 21) ℚ)) 2 j := by decide +kernel
theorem hodge_4_row_2_3 : ∀ j, (hodge_4_G*hodge_4_B) 3 j = ((0 : Matrix (Fin 21) (Fin 21) ℚ)) 3 j := by decide +kernel
theorem hodge_4_row_2_4 : ∀ j, (hodge_4_G*hodge_4_B) 4 j = ((0 : Matrix (Fin 21) (Fin 21) ℚ)) 4 j := by decide +kernel
end PerfectPower.ParallelCertificates
