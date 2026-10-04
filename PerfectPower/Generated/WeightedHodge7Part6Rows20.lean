import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_20 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 20 j = (hodge_7_M*hodge_7_H) 20 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_21 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 21 j = (hodge_7_M*hodge_7_H) 21 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_22 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 22 j = (hodge_7_M*hodge_7_H) 22 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_23 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 23 j = (hodge_7_M*hodge_7_H) 23 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_24 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 24 j = (hodge_7_M*hodge_7_H) 24 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
