import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_25 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 25 j = (hodge_7_M*hodge_7_H) 25 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_26 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 26 j = (hodge_7_M*hodge_7_H) 26 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_27 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 27 j = (hodge_7_M*hodge_7_H) 27 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_28 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 28 j = (hodge_7_M*hodge_7_H) 28 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_29 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 29 j = (hodge_7_M*hodge_7_H) 29 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
