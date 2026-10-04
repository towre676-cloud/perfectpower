import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_15 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 15 j = (hodge_7_M*hodge_7_H) 15 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_16 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 16 j = (hodge_7_M*hodge_7_H) 16 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_17 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 17 j = (hodge_7_M*hodge_7_H) 17 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_18 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 18 j = (hodge_7_M*hodge_7_H) 18 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_19 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 19 j = (hodge_7_M*hodge_7_H) 19 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
