import PerfectPower.Generated.WeightedHodge7Part0Rows0
import PerfectPower.Generated.WeightedHodge7Part0Rows5
import PerfectPower.Generated.WeightedHodge7Part0Rows10
import PerfectPower.Generated.WeightedHodge7Part0Rows15
import PerfectPower.Generated.WeightedHodge7Part0Rows20
import PerfectPower.Generated.WeightedHodge7Part0Rows25
import PerfectPower.Generated.WeightedHodge7Part0Rows30
import PerfectPower.Generated.WeightedHodge7Part0Rows35
import PerfectPower.Generated.WeightedHodge7Part1Rows0
import PerfectPower.Generated.WeightedHodge7Part1Rows5
import PerfectPower.Generated.WeightedHodge7Part1Rows10
import PerfectPower.Generated.WeightedHodge7Part1Rows15
import PerfectPower.Generated.WeightedHodge7Part1Rows20
import PerfectPower.Generated.WeightedHodge7Part1Rows25
import PerfectPower.Generated.WeightedHodge7Part1Rows30
import PerfectPower.Generated.WeightedHodge7Part1Rows35
import PerfectPower.Generated.WeightedHodge7Part2Rows0
import PerfectPower.Generated.WeightedHodge7Part2Rows5
import PerfectPower.Generated.WeightedHodge7Part2Rows10
import PerfectPower.Generated.WeightedHodge7Part2Rows15
import PerfectPower.Generated.WeightedHodge7Part2Rows20
import PerfectPower.Generated.WeightedHodge7Part2Rows25
import PerfectPower.Generated.WeightedHodge7Part2Rows30
import PerfectPower.Generated.WeightedHodge7Part2Rows35
import PerfectPower.Generated.WeightedHodge7Part3Rows0
import PerfectPower.Generated.WeightedHodge7Part3Rows5
import PerfectPower.Generated.WeightedHodge7Part3Rows10
import PerfectPower.Generated.WeightedHodge7Part3Rows15
import PerfectPower.Generated.WeightedHodge7Part3Rows20
import PerfectPower.Generated.WeightedHodge7Part3Rows25
import PerfectPower.Generated.WeightedHodge7Part3Rows30
import PerfectPower.Generated.WeightedHodge7Part3Rows35
import PerfectPower.Generated.WeightedHodge7Part4Rows0
import PerfectPower.Generated.WeightedHodge7Part4Rows5
import PerfectPower.Generated.WeightedHodge7Part4Rows10
import PerfectPower.Generated.WeightedHodge7Part4Rows15
import PerfectPower.Generated.WeightedHodge7Part4Rows20
import PerfectPower.Generated.WeightedHodge7Part4Rows25
import PerfectPower.Generated.WeightedHodge7Part4Rows30
import PerfectPower.Generated.WeightedHodge7Part4Rows35
import PerfectPower.Generated.WeightedHodge7Part5Rows0
import PerfectPower.Generated.WeightedHodge7Part5Rows5
import PerfectPower.Generated.WeightedHodge7Part5Rows10
import PerfectPower.Generated.WeightedHodge7Part5Rows15
import PerfectPower.Generated.WeightedHodge7Part5Rows20
import PerfectPower.Generated.WeightedHodge7Part5Rows25
import PerfectPower.Generated.WeightedHodge7Part5Rows30
import PerfectPower.Generated.WeightedHodge7Part5Rows35
import PerfectPower.Generated.WeightedHodge7Part6Rows0
import PerfectPower.Generated.WeightedHodge7Part6Rows5
import PerfectPower.Generated.WeightedHodge7Part6Rows10
import PerfectPower.Generated.WeightedHodge7Part6Rows15
import PerfectPower.Generated.WeightedHodge7Part6Rows20
import PerfectPower.Generated.WeightedHodge7Part6Rows25
import PerfectPower.Generated.WeightedHodge7Part6Rows30
import PerfectPower.Generated.WeightedHodge7Part6Rows35
namespace PerfectPower.ParallelCertificates
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_part_0 : hodge_7_G*hodge_7_G=hodge_7_G := by
  ext i j
  fin_cases i
  · exact hodge_7_row_0_0 j
  · exact hodge_7_row_0_1 j
  · exact hodge_7_row_0_2 j
  · exact hodge_7_row_0_3 j
  · exact hodge_7_row_0_4 j
  · exact hodge_7_row_0_5 j
  · exact hodge_7_row_0_6 j
  · exact hodge_7_row_0_7 j
  · exact hodge_7_row_0_8 j
  · exact hodge_7_row_0_9 j
  · exact hodge_7_row_0_10 j
  · exact hodge_7_row_0_11 j
  · exact hodge_7_row_0_12 j
  · exact hodge_7_row_0_13 j
  · exact hodge_7_row_0_14 j
  · exact hodge_7_row_0_15 j
  · exact hodge_7_row_0_16 j
  · exact hodge_7_row_0_17 j
  · exact hodge_7_row_0_18 j
  · exact hodge_7_row_0_19 j
  · exact hodge_7_row_0_20 j
  · exact hodge_7_row_0_21 j
  · exact hodge_7_row_0_22 j
  · exact hodge_7_row_0_23 j
  · exact hodge_7_row_0_24 j
  · exact hodge_7_row_0_25 j
  · exact hodge_7_row_0_26 j
  · exact hodge_7_row_0_27 j
  · exact hodge_7_row_0_28 j
  · exact hodge_7_row_0_29 j
  · exact hodge_7_row_0_30 j
  · exact hodge_7_row_0_31 j
  · exact hodge_7_row_0_32 j
  · exact hodge_7_row_0_33 j
  · exact hodge_7_row_0_34 j
  · exact hodge_7_row_0_35 j
  · exact hodge_7_row_0_36 j
  · exact hodge_7_row_0_37 j
  · exact hodge_7_row_0_38 j
theorem hodge_7_part_1 : hodge_7_B*hodge_7_B=hodge_7_B := by
  ext i j
  fin_cases i
  · exact hodge_7_row_1_0 j
  · exact hodge_7_row_1_1 j
  · exact hodge_7_row_1_2 j
  · exact hodge_7_row_1_3 j
  · exact hodge_7_row_1_4 j
  · exact hodge_7_row_1_5 j
  · exact hodge_7_row_1_6 j
  · exact hodge_7_row_1_7 j
  · exact hodge_7_row_1_8 j
  · exact hodge_7_row_1_9 j
  · exact hodge_7_row_1_10 j
  · exact hodge_7_row_1_11 j
  · exact hodge_7_row_1_12 j
  · exact hodge_7_row_1_13 j
  · exact hodge_7_row_1_14 j
  · exact hodge_7_row_1_15 j
  · exact hodge_7_row_1_16 j
  · exact hodge_7_row_1_17 j
  · exact hodge_7_row_1_18 j
  · exact hodge_7_row_1_19 j
  · exact hodge_7_row_1_20 j
  · exact hodge_7_row_1_21 j
  · exact hodge_7_row_1_22 j
  · exact hodge_7_row_1_23 j
  · exact hodge_7_row_1_24 j
  · exact hodge_7_row_1_25 j
  · exact hodge_7_row_1_26 j
  · exact hodge_7_row_1_27 j
  · exact hodge_7_row_1_28 j
  · exact hodge_7_row_1_29 j
  · exact hodge_7_row_1_30 j
  · exact hodge_7_row_1_31 j
  · exact hodge_7_row_1_32 j
  · exact hodge_7_row_1_33 j
  · exact hodge_7_row_1_34 j
  · exact hodge_7_row_1_35 j
  · exact hodge_7_row_1_36 j
  · exact hodge_7_row_1_37 j
  · exact hodge_7_row_1_38 j
theorem hodge_7_part_2 : hodge_7_G*hodge_7_B=0 := by
  ext i j
  fin_cases i
  · exact hodge_7_row_2_0 j
  · exact hodge_7_row_2_1 j
  · exact hodge_7_row_2_2 j
  · exact hodge_7_row_2_3 j
  · exact hodge_7_row_2_4 j
  · exact hodge_7_row_2_5 j
  · exact hodge_7_row_2_6 j
  · exact hodge_7_row_2_7 j
  · exact hodge_7_row_2_8 j
  · exact hodge_7_row_2_9 j
  · exact hodge_7_row_2_10 j
  · exact hodge_7_row_2_11 j
  · exact hodge_7_row_2_12 j
  · exact hodge_7_row_2_13 j
  · exact hodge_7_row_2_14 j
  · exact hodge_7_row_2_15 j
  · exact hodge_7_row_2_16 j
  · exact hodge_7_row_2_17 j
  · exact hodge_7_row_2_18 j
  · exact hodge_7_row_2_19 j
  · exact hodge_7_row_2_20 j
  · exact hodge_7_row_2_21 j
  · exact hodge_7_row_2_22 j
  · exact hodge_7_row_2_23 j
  · exact hodge_7_row_2_24 j
  · exact hodge_7_row_2_25 j
  · exact hodge_7_row_2_26 j
  · exact hodge_7_row_2_27 j
  · exact hodge_7_row_2_28 j
  · exact hodge_7_row_2_29 j
  · exact hodge_7_row_2_30 j
  · exact hodge_7_row_2_31 j
  · exact hodge_7_row_2_32 j
  · exact hodge_7_row_2_33 j
  · exact hodge_7_row_2_34 j
  · exact hodge_7_row_2_35 j
  · exact hodge_7_row_2_36 j
  · exact hodge_7_row_2_37 j
  · exact hodge_7_row_2_38 j
theorem hodge_7_part_3 : hodge_7_B*hodge_7_G=0 := by
  ext i j
  fin_cases i
  · exact hodge_7_row_3_0 j
  · exact hodge_7_row_3_1 j
  · exact hodge_7_row_3_2 j
  · exact hodge_7_row_3_3 j
  · exact hodge_7_row_3_4 j
  · exact hodge_7_row_3_5 j
  · exact hodge_7_row_3_6 j
  · exact hodge_7_row_3_7 j
  · exact hodge_7_row_3_8 j
  · exact hodge_7_row_3_9 j
  · exact hodge_7_row_3_10 j
  · exact hodge_7_row_3_11 j
  · exact hodge_7_row_3_12 j
  · exact hodge_7_row_3_13 j
  · exact hodge_7_row_3_14 j
  · exact hodge_7_row_3_15 j
  · exact hodge_7_row_3_16 j
  · exact hodge_7_row_3_17 j
  · exact hodge_7_row_3_18 j
  · exact hodge_7_row_3_19 j
  · exact hodge_7_row_3_20 j
  · exact hodge_7_row_3_21 j
  · exact hodge_7_row_3_22 j
  · exact hodge_7_row_3_23 j
  · exact hodge_7_row_3_24 j
  · exact hodge_7_row_3_25 j
  · exact hodge_7_row_3_26 j
  · exact hodge_7_row_3_27 j
  · exact hodge_7_row_3_28 j
  · exact hodge_7_row_3_29 j
  · exact hodge_7_row_3_30 j
  · exact hodge_7_row_3_31 j
  · exact hodge_7_row_3_32 j
  · exact hodge_7_row_3_33 j
  · exact hodge_7_row_3_34 j
  · exact hodge_7_row_3_35 j
  · exact hodge_7_row_3_36 j
  · exact hodge_7_row_3_37 j
  · exact hodge_7_row_3_38 j
theorem hodge_7_part_4 : hodge_7_G+hodge_7_B+hodge_7_H=1 := by
  ext i j
  fin_cases i
  · exact hodge_7_row_4_0 j
  · exact hodge_7_row_4_1 j
  · exact hodge_7_row_4_2 j
  · exact hodge_7_row_4_3 j
  · exact hodge_7_row_4_4 j
  · exact hodge_7_row_4_5 j
  · exact hodge_7_row_4_6 j
  · exact hodge_7_row_4_7 j
  · exact hodge_7_row_4_8 j
  · exact hodge_7_row_4_9 j
  · exact hodge_7_row_4_10 j
  · exact hodge_7_row_4_11 j
  · exact hodge_7_row_4_12 j
  · exact hodge_7_row_4_13 j
  · exact hodge_7_row_4_14 j
  · exact hodge_7_row_4_15 j
  · exact hodge_7_row_4_16 j
  · exact hodge_7_row_4_17 j
  · exact hodge_7_row_4_18 j
  · exact hodge_7_row_4_19 j
  · exact hodge_7_row_4_20 j
  · exact hodge_7_row_4_21 j
  · exact hodge_7_row_4_22 j
  · exact hodge_7_row_4_23 j
  · exact hodge_7_row_4_24 j
  · exact hodge_7_row_4_25 j
  · exact hodge_7_row_4_26 j
  · exact hodge_7_row_4_27 j
  · exact hodge_7_row_4_28 j
  · exact hodge_7_row_4_29 j
  · exact hodge_7_row_4_30 j
  · exact hodge_7_row_4_31 j
  · exact hodge_7_row_4_32 j
  · exact hodge_7_row_4_33 j
  · exact hodge_7_row_4_34 j
  · exact hodge_7_row_4_35 j
  · exact hodge_7_row_4_36 j
  · exact hodge_7_row_4_37 j
  · exact hodge_7_row_4_38 j
theorem hodge_7_part_5 : hodge_7_L*hodge_7_H=0 := by
  ext i j
  fin_cases i
  · exact hodge_7_row_5_0 j
  · exact hodge_7_row_5_1 j
  · exact hodge_7_row_5_2 j
  · exact hodge_7_row_5_3 j
  · exact hodge_7_row_5_4 j
  · exact hodge_7_row_5_5 j
  · exact hodge_7_row_5_6 j
  · exact hodge_7_row_5_7 j
  · exact hodge_7_row_5_8 j
  · exact hodge_7_row_5_9 j
  · exact hodge_7_row_5_10 j
  · exact hodge_7_row_5_11 j
  · exact hodge_7_row_5_12 j
  · exact hodge_7_row_5_13 j
  · exact hodge_7_row_5_14 j
  · exact hodge_7_row_5_15 j
  · exact hodge_7_row_5_16 j
  · exact hodge_7_row_5_17 j
  · exact hodge_7_row_5_18 j
  · exact hodge_7_row_5_19 j
  · exact hodge_7_row_5_20 j
  · exact hodge_7_row_5_21 j
  · exact hodge_7_row_5_22 j
  · exact hodge_7_row_5_23 j
  · exact hodge_7_row_5_24 j
  · exact hodge_7_row_5_25 j
  · exact hodge_7_row_5_26 j
  · exact hodge_7_row_5_27 j
  · exact hodge_7_row_5_28 j
  · exact hodge_7_row_5_29 j
  · exact hodge_7_row_5_30 j
  · exact hodge_7_row_5_31 j
  · exact hodge_7_row_5_32 j
  · exact hodge_7_row_5_33 j
  · exact hodge_7_row_5_34 j
  · exact hodge_7_row_5_35 j
  · exact hodge_7_row_5_36 j
  · exact hodge_7_row_5_37 j
  · exact hodge_7_row_5_38 j
theorem hodge_7_part_6 : hodge_7_H.transpose*hodge_7_M=hodge_7_M*hodge_7_H := by
  ext i j
  fin_cases i
  · exact hodge_7_row_6_0 j
  · exact hodge_7_row_6_1 j
  · exact hodge_7_row_6_2 j
  · exact hodge_7_row_6_3 j
  · exact hodge_7_row_6_4 j
  · exact hodge_7_row_6_5 j
  · exact hodge_7_row_6_6 j
  · exact hodge_7_row_6_7 j
  · exact hodge_7_row_6_8 j
  · exact hodge_7_row_6_9 j
  · exact hodge_7_row_6_10 j
  · exact hodge_7_row_6_11 j
  · exact hodge_7_row_6_12 j
  · exact hodge_7_row_6_13 j
  · exact hodge_7_row_6_14 j
  · exact hodge_7_row_6_15 j
  · exact hodge_7_row_6_16 j
  · exact hodge_7_row_6_17 j
  · exact hodge_7_row_6_18 j
  · exact hodge_7_row_6_19 j
  · exact hodge_7_row_6_20 j
  · exact hodge_7_row_6_21 j
  · exact hodge_7_row_6_22 j
  · exact hodge_7_row_6_23 j
  · exact hodge_7_row_6_24 j
  · exact hodge_7_row_6_25 j
  · exact hodge_7_row_6_26 j
  · exact hodge_7_row_6_27 j
  · exact hodge_7_row_6_28 j
  · exact hodge_7_row_6_29 j
  · exact hodge_7_row_6_30 j
  · exact hodge_7_row_6_31 j
  · exact hodge_7_row_6_32 j
  · exact hodge_7_row_6_33 j
  · exact hodge_7_row_6_34 j
  · exact hodge_7_row_6_35 j
  · exact hodge_7_row_6_36 j
  · exact hodge_7_row_6_37 j
  · exact hodge_7_row_6_38 j
theorem hodge_7_part_7 : Matrix.trace hodge_7_H=14 := by decide +kernel
theorem hodge_7_checked : hodge_7_G*hodge_7_G=hodge_7_G ∧ hodge_7_B*hodge_7_B=hodge_7_B ∧ hodge_7_G*hodge_7_B=0 ∧ hodge_7_B*hodge_7_G=0 ∧ hodge_7_G+hodge_7_B+hodge_7_H=1 ∧ hodge_7_L*hodge_7_H=0 ∧ hodge_7_H.transpose*hodge_7_M=hodge_7_M*hodge_7_H ∧ Matrix.trace hodge_7_H=14 := by
  exact ⟨hodge_7_part_0,hodge_7_part_1,hodge_7_part_2,hodge_7_part_3,hodge_7_part_4,hodge_7_part_5,hodge_7_part_6,hodge_7_part_7⟩
theorem hodge_7_idempotent : hodge_7_H*hodge_7_H=hodge_7_H := by
  have hc := hodge_7_checked
  have he : hodge_7_H=1-hodge_7_G-hodge_7_B := by rw [← hc.2.2.2.2.1]; abel
  rw [he]
  exact (PerfectPower.WeightedHodge.harmonic_projector hodge_7_G hodge_7_B hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1).1
end PerfectPower.ParallelCertificates
