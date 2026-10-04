import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_10 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 10 j = (hodge_7_M*hodge_7_H) 10 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_11 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 11 j = (hodge_7_M*hodge_7_H) 11 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_12 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 12 j = (hodge_7_M*hodge_7_H) 12 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_13 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 13 j = (hodge_7_M*hodge_7_H) 13 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_14 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 14 j = (hodge_7_M*hodge_7_H) 14 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
