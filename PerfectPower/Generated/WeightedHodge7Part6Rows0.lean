import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_0 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 0 j = (hodge_7_M*hodge_7_H) 0 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_1 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 1 j = (hodge_7_M*hodge_7_H) 1 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_2 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 2 j = (hodge_7_M*hodge_7_H) 2 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_3 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 3 j = (hodge_7_M*hodge_7_H) 3 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_4 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 4 j = (hodge_7_M*hodge_7_H) 4 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
