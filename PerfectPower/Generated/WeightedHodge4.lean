import PerfectPower.Generated.WeightedHodge4Part0Rows0
import PerfectPower.Generated.WeightedHodge4Part0Rows5
import PerfectPower.Generated.WeightedHodge4Part0Rows10
import PerfectPower.Generated.WeightedHodge4Part0Rows15
import PerfectPower.Generated.WeightedHodge4Part0Rows20
import PerfectPower.Generated.WeightedHodge4Part1Rows0
import PerfectPower.Generated.WeightedHodge4Part1Rows5
import PerfectPower.Generated.WeightedHodge4Part1Rows10
import PerfectPower.Generated.WeightedHodge4Part1Rows15
import PerfectPower.Generated.WeightedHodge4Part1Rows20
import PerfectPower.Generated.WeightedHodge4Part2Rows0
import PerfectPower.Generated.WeightedHodge4Part2Rows5
import PerfectPower.Generated.WeightedHodge4Part2Rows10
import PerfectPower.Generated.WeightedHodge4Part2Rows15
import PerfectPower.Generated.WeightedHodge4Part2Rows20
import PerfectPower.Generated.WeightedHodge4Part3Rows0
import PerfectPower.Generated.WeightedHodge4Part3Rows5
import PerfectPower.Generated.WeightedHodge4Part3Rows10
import PerfectPower.Generated.WeightedHodge4Part3Rows15
import PerfectPower.Generated.WeightedHodge4Part3Rows20
import PerfectPower.Generated.WeightedHodge4Part4Rows0
import PerfectPower.Generated.WeightedHodge4Part4Rows5
import PerfectPower.Generated.WeightedHodge4Part4Rows10
import PerfectPower.Generated.WeightedHodge4Part4Rows15
import PerfectPower.Generated.WeightedHodge4Part4Rows20
import PerfectPower.Generated.WeightedHodge4Part5Rows0
import PerfectPower.Generated.WeightedHodge4Part5Rows5
import PerfectPower.Generated.WeightedHodge4Part5Rows10
import PerfectPower.Generated.WeightedHodge4Part5Rows15
import PerfectPower.Generated.WeightedHodge4Part5Rows20
import PerfectPower.Generated.WeightedHodge4Part6Rows0
import PerfectPower.Generated.WeightedHodge4Part6Rows5
import PerfectPower.Generated.WeightedHodge4Part6Rows10
import PerfectPower.Generated.WeightedHodge4Part6Rows15
import PerfectPower.Generated.WeightedHodge4Part6Rows20
namespace PerfectPower.ParallelCertificates
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_4_part_0 : hodge_4_G*hodge_4_G=hodge_4_G := by
  ext i j
  fin_cases i
  · exact hodge_4_row_0_0 j
  · exact hodge_4_row_0_1 j
  · exact hodge_4_row_0_2 j
  · exact hodge_4_row_0_3 j
  · exact hodge_4_row_0_4 j
  · exact hodge_4_row_0_5 j
  · exact hodge_4_row_0_6 j
  · exact hodge_4_row_0_7 j
  · exact hodge_4_row_0_8 j
  · exact hodge_4_row_0_9 j
  · exact hodge_4_row_0_10 j
  · exact hodge_4_row_0_11 j
  · exact hodge_4_row_0_12 j
  · exact hodge_4_row_0_13 j
  · exact hodge_4_row_0_14 j
  · exact hodge_4_row_0_15 j
  · exact hodge_4_row_0_16 j
  · exact hodge_4_row_0_17 j
  · exact hodge_4_row_0_18 j
  · exact hodge_4_row_0_19 j
  · exact hodge_4_row_0_20 j
theorem hodge_4_part_1 : hodge_4_B*hodge_4_B=hodge_4_B := by
  ext i j
  fin_cases i
  · exact hodge_4_row_1_0 j
  · exact hodge_4_row_1_1 j
  · exact hodge_4_row_1_2 j
  · exact hodge_4_row_1_3 j
  · exact hodge_4_row_1_4 j
  · exact hodge_4_row_1_5 j
  · exact hodge_4_row_1_6 j
  · exact hodge_4_row_1_7 j
  · exact hodge_4_row_1_8 j
  · exact hodge_4_row_1_9 j
  · exact hodge_4_row_1_10 j
  · exact hodge_4_row_1_11 j
  · exact hodge_4_row_1_12 j
  · exact hodge_4_row_1_13 j
  · exact hodge_4_row_1_14 j
  · exact hodge_4_row_1_15 j
  · exact hodge_4_row_1_16 j
  · exact hodge_4_row_1_17 j
  · exact hodge_4_row_1_18 j
  · exact hodge_4_row_1_19 j
  · exact hodge_4_row_1_20 j
theorem hodge_4_part_2 : hodge_4_G*hodge_4_B=0 := by
  ext i j
  fin_cases i
  · exact hodge_4_row_2_0 j
  · exact hodge_4_row_2_1 j
  · exact hodge_4_row_2_2 j
  · exact hodge_4_row_2_3 j
  · exact hodge_4_row_2_4 j
  · exact hodge_4_row_2_5 j
  · exact hodge_4_row_2_6 j
  · exact hodge_4_row_2_7 j
  · exact hodge_4_row_2_8 j
  · exact hodge_4_row_2_9 j
  · exact hodge_4_row_2_10 j
  · exact hodge_4_row_2_11 j
  · exact hodge_4_row_2_12 j
  · exact hodge_4_row_2_13 j
  · exact hodge_4_row_2_14 j
  · exact hodge_4_row_2_15 j
  · exact hodge_4_row_2_16 j
  · exact hodge_4_row_2_17 j
  · exact hodge_4_row_2_18 j
  · exact hodge_4_row_2_19 j
  · exact hodge_4_row_2_20 j
theorem hodge_4_part_3 : hodge_4_B*hodge_4_G=0 := by
  ext i j
  fin_cases i
  · exact hodge_4_row_3_0 j
  · exact hodge_4_row_3_1 j
  · exact hodge_4_row_3_2 j
  · exact hodge_4_row_3_3 j
  · exact hodge_4_row_3_4 j
  · exact hodge_4_row_3_5 j
  · exact hodge_4_row_3_6 j
  · exact hodge_4_row_3_7 j
  · exact hodge_4_row_3_8 j
  · exact hodge_4_row_3_9 j
  · exact hodge_4_row_3_10 j
  · exact hodge_4_row_3_11 j
  · exact hodge_4_row_3_12 j
  · exact hodge_4_row_3_13 j
  · exact hodge_4_row_3_14 j
  · exact hodge_4_row_3_15 j
  · exact hodge_4_row_3_16 j
  · exact hodge_4_row_3_17 j
  · exact hodge_4_row_3_18 j
  · exact hodge_4_row_3_19 j
  · exact hodge_4_row_3_20 j
theorem hodge_4_part_4 : hodge_4_G+hodge_4_B+hodge_4_H=1 := by
  ext i j
  fin_cases i
  · exact hodge_4_row_4_0 j
  · exact hodge_4_row_4_1 j
  · exact hodge_4_row_4_2 j
  · exact hodge_4_row_4_3 j
  · exact hodge_4_row_4_4 j
  · exact hodge_4_row_4_5 j
  · exact hodge_4_row_4_6 j
  · exact hodge_4_row_4_7 j
  · exact hodge_4_row_4_8 j
  · exact hodge_4_row_4_9 j
  · exact hodge_4_row_4_10 j
  · exact hodge_4_row_4_11 j
  · exact hodge_4_row_4_12 j
  · exact hodge_4_row_4_13 j
  · exact hodge_4_row_4_14 j
  · exact hodge_4_row_4_15 j
  · exact hodge_4_row_4_16 j
  · exact hodge_4_row_4_17 j
  · exact hodge_4_row_4_18 j
  · exact hodge_4_row_4_19 j
  · exact hodge_4_row_4_20 j
theorem hodge_4_part_5 : hodge_4_L*hodge_4_H=0 := by
  ext i j
  fin_cases i
  · exact hodge_4_row_5_0 j
  · exact hodge_4_row_5_1 j
  · exact hodge_4_row_5_2 j
  · exact hodge_4_row_5_3 j
  · exact hodge_4_row_5_4 j
  · exact hodge_4_row_5_5 j
  · exact hodge_4_row_5_6 j
  · exact hodge_4_row_5_7 j
  · exact hodge_4_row_5_8 j
  · exact hodge_4_row_5_9 j
  · exact hodge_4_row_5_10 j
  · exact hodge_4_row_5_11 j
  · exact hodge_4_row_5_12 j
  · exact hodge_4_row_5_13 j
  · exact hodge_4_row_5_14 j
  · exact hodge_4_row_5_15 j
  · exact hodge_4_row_5_16 j
  · exact hodge_4_row_5_17 j
  · exact hodge_4_row_5_18 j
  · exact hodge_4_row_5_19 j
  · exact hodge_4_row_5_20 j
theorem hodge_4_part_6 : hodge_4_H.transpose*hodge_4_M=hodge_4_M*hodge_4_H := by
  ext i j
  fin_cases i
  · exact hodge_4_row_6_0 j
  · exact hodge_4_row_6_1 j
  · exact hodge_4_row_6_2 j
  · exact hodge_4_row_6_3 j
  · exact hodge_4_row_6_4 j
  · exact hodge_4_row_6_5 j
  · exact hodge_4_row_6_6 j
  · exact hodge_4_row_6_7 j
  · exact hodge_4_row_6_8 j
  · exact hodge_4_row_6_9 j
  · exact hodge_4_row_6_10 j
  · exact hodge_4_row_6_11 j
  · exact hodge_4_row_6_12 j
  · exact hodge_4_row_6_13 j
  · exact hodge_4_row_6_14 j
  · exact hodge_4_row_6_15 j
  · exact hodge_4_row_6_16 j
  · exact hodge_4_row_6_17 j
  · exact hodge_4_row_6_18 j
  · exact hodge_4_row_6_19 j
  · exact hodge_4_row_6_20 j
theorem hodge_4_part_7 : Matrix.trace hodge_4_H=8 := by decide +kernel
theorem hodge_4_checked : hodge_4_G*hodge_4_G=hodge_4_G ∧ hodge_4_B*hodge_4_B=hodge_4_B ∧ hodge_4_G*hodge_4_B=0 ∧ hodge_4_B*hodge_4_G=0 ∧ hodge_4_G+hodge_4_B+hodge_4_H=1 ∧ hodge_4_L*hodge_4_H=0 ∧ hodge_4_H.transpose*hodge_4_M=hodge_4_M*hodge_4_H ∧ Matrix.trace hodge_4_H=8 := by
  exact ⟨hodge_4_part_0,hodge_4_part_1,hodge_4_part_2,hodge_4_part_3,hodge_4_part_4,hodge_4_part_5,hodge_4_part_6,hodge_4_part_7⟩
theorem hodge_4_idempotent : hodge_4_H*hodge_4_H=hodge_4_H := by
  have hc := hodge_4_checked
  have he : hodge_4_H=1-hodge_4_G-hodge_4_B := by rw [← hc.2.2.2.2.1]; abel
  rw [he]
  exact (PerfectPower.WeightedHodge.harmonic_projector hodge_4_G hodge_4_B hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1).1
end PerfectPower.ParallelCertificates
