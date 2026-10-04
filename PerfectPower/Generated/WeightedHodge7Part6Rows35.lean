import PerfectPower.Generated.WeightedHodge7Data
namespace PerfectPower.ParallelCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem hodge_7_row_6_35 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 35 j = (hodge_7_M*hodge_7_H) 35 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_36 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 36 j = (hodge_7_M*hodge_7_H) 36 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_37 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 37 j = (hodge_7_M*hodge_7_H) 37 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
theorem hodge_7_row_6_38 : ∀ j, (hodge_7_H.transpose*hodge_7_M) 38 j = (hodge_7_M*hodge_7_H) 38 j := by
  simp only [hodge_7_M, Matrix.mul_diagonal, Matrix.diagonal_mul]
  intro j
  fin_cases j <;> decide +kernel
end PerfectPower.ParallelCertificates
