import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_30 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 30 j = (hodge_7_M*hodge_7_H) 30 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_31 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 31 j = (hodge_7_M*hodge_7_H) 31 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_32 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 32 j = (hodge_7_M*hodge_7_H) 32 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_33 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 33 j = (hodge_7_M*hodge_7_H) 33 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_34 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 34 j = (hodge_7_M*hodge_7_H) 34 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
