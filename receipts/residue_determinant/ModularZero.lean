import PerfectPower.ResidueDeterminantCertificate
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Determinant_b8bb691d6a7ed750
open Matrix
open scoped BigOperators
def A : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (2), (3); (2), (3), (4); (3), (4), (5)]
def E : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (0), (0); (-2016), (1008), (0); (2030109), (-1015056), (1)]
def U : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (2), (3); (0), (-1008), (-2016); (0), (1015054), (2030108)]
def weights : Fin 3 → ℕ := ![(0), (0), (1)]
def bounds : Fin 3 → ℝ := ![(3), (4), (5)]
theorem transform : E * A = U := by decide +kernel
theorem row_divides : ∀ i j, (1009 : ℤ)^weights i ∣ U i j := by decide +kernel
theorem divisor_sum : (1009 : ℤ)^(∑ i, weights i) = 1009 := by decide +kernel
theorem coprime : IsCoprime (1009 : ℤ) E.det := by
  refine ⟨1, -1, ?_⟩
  decide +kernel
theorem divides : (1009 : ℤ) ∣ A.det := by
  apply PerfectPower.ResidueDeterminantCertificate.determinant_dvd_of_transform A E 1009 coprime
  rw [transform]
  have h := PerfectPower.ResidueDeterminantCertificate.pow_sum_dvd_det_of_row_dvd
    (1009 : ℤ) weights U row_divides
  rwa [divisor_sum] at h
theorem magnitude : ∀ i j, |(A i j : ℝ)| ≤ bounds i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [A, bounds, Matrix.cons_val_zero, Matrix.cons_val_succ]
theorem strict_bound : (Nat.factorial (Fintype.card (Fin 3)) : ℝ) * ∏ i, bounds i < (1009 : ℝ) := by
  norm_num [bounds, Fin.prod_univ_succ, Nat.factorial]
theorem determinant_zero : A.det = 0 :=
  PerfectPower.ResidueDeterminantCertificate.determinant_zero_of_divisor_bound A 1009 bounds divides magnitude strict_bound
#print axioms determinant_zero
end Determinant_b8bb691d6a7ed750
