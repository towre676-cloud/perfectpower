import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_5 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 5 j = (hodge_7_M*hodge_7_H) 5 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_6 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 6 j = (hodge_7_M*hodge_7_H) 6 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_7 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 7 j = (hodge_7_M*hodge_7_H) 7 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_8 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 8 j = (hodge_7_M*hodge_7_H) 8 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_9 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 9 j = (hodge_7_M*hodge_7_H) 9 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
