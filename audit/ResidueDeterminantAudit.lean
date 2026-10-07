import PerfectPower.IntegralKernelWitness
import PerfectPower.ResidueDeterminantCertificate

#print axioms PerfectPower.IntegralKernelWitness.integralKernelMatrix_map
#print axioms PerfectPower.IntegralKernelWitness.mul_integralKernelMatrix
#print axioms PerfectPower.IntegralKernelWitness.integralKernelMatrix_mulVec_of_kernel
#print axioms PerfectPower.IntegralKernelWitness.gram_det_ne_zero_of_linearIndependent
#print axioms PerfectPower.IntegralKernelWitness.mulVec_eq_zero_of_row_mem_span
#print axioms PerfectPower.IntegralKernelWitness.integralKernelMatrix_column_mem_kernel
#print axioms PerfectPower.IntegralKernelWitness.mem_span_integralKernelMatrix_columns
#print axioms PerfectPower.ResidueDeterminantCertificate.pow_sum_dvd_det_of_row_dvd
#print axioms PerfectPower.ResidueDeterminantCertificate.determinant_dvd_of_local_expansion
#print axioms PerfectPower.ResidueDeterminantCertificate.determinant_dvd_polynomial_eval
#print axioms PerfectPower.ResidueDeterminantCertificate.det_abs_le_row_product
#print axioms PerfectPower.ResidueDeterminantCertificate.determinant_zero_of_divisor_bound
#print axioms PerfectPower.ResidueDeterminantCertificate.determinant_dvd_of_transform
#print axioms PerfectPower.ResidueDeterminantCertificate.relation_of_kernel_column

open Matrix
namespace IntegralIndexGap
def K : Matrix (Fin 3) (Fin 3) ℤ := !![2, -1, -1; -1, 2, -1; -1, -1, 2]
def missing : Fin 3 → ℤ := ![1, -1, 0]
def A : Matrix (Fin 1) (Fin 3) ℤ := !![1, 1, 1]
theorem missing_is_kernel : A *ᵥ missing = 0 := by decide +kernel
theorem missing_not_column_combination : ¬ ∃ z : Fin 3 → ℤ, K *ᵥ z = missing := by
  rintro ⟨z, hz⟩
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  simp [K, missing, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  omega
#print axioms missing_is_kernel
#print axioms missing_not_column_combination
end IntegralIndexGap
