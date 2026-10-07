import PerfectPower.ResidueDeterminantCertificate
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Determinant_72a80eccf47ee30c
open Matrix
open scoped BigOperators
def A : Matrix (Fin 2) (Fin 2) ℤ := !![(1), (2); (2), (4)]
def E : Matrix (Fin 2) (Fin 2) ℤ := !![(1), (0); (-2), (1)]
def U : Matrix (Fin 2) (Fin 2) ℤ := !![(1), (2); (0), (0)]
def weights : Fin 2 → ℕ := ![(0), (1)]
def bounds : Fin 2 → ℝ := ![(2), (4)]
theorem transform : E * A = U := by decide +kernel
theorem row_divides : ∀ i j, (35 : ℤ)^weights i ∣ U i j := by decide +kernel
theorem divisor_sum : (35 : ℤ)^(∑ i, weights i) = 35 := by decide +kernel
theorem coprime : IsCoprime (35 : ℤ) E.det := by
  refine ⟨0, 1, ?_⟩
  decide +kernel
theorem divides : (35 : ℤ) ∣ A.det := by
  apply PerfectPower.ResidueDeterminantCertificate.determinant_dvd_of_transform A E 35 coprime
  rw [transform]
  have h := PerfectPower.ResidueDeterminantCertificate.pow_sum_dvd_det_of_row_dvd
    (35 : ℤ) weights U row_divides
  rwa [divisor_sum] at h
theorem magnitude : ∀ i j, |(A i j : ℝ)| ≤ bounds i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [A, bounds, Matrix.cons_val_zero, Matrix.cons_val_succ]
theorem strict_bound : (Nat.factorial (Fintype.card (Fin 2)) : ℝ) * ∏ i, bounds i < (35 : ℝ) := by
  norm_num [bounds, Fin.prod_univ_succ, Nat.factorial]
theorem determinant_zero : A.det = 0 :=
  PerfectPower.ResidueDeterminantCertificate.determinant_zero_of_divisor_bound A 35 bounds divides magnitude strict_bound
#print axioms determinant_zero
end Determinant_72a80eccf47ee30c
