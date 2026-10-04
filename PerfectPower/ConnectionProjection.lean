import Mathlib
noncomputable section
namespace PerfectPower.ConnectionProjection
open Matrix
variable {e v : Type*} [Fintype e] [Fintype v] [DecidableEq e] [DecidableEq v]
variable {K : Type*} [CommRing K]
/-- The asymmetric connection kernel uses no square roots of edge weights. -/
def kernel (W : Matrix e e K) (B : Matrix e v K) (C : Matrix v e K)
    (N : Matrix v v K) := W*B*N*C

omit [DecidableEq e] in
theorem idempotent (W : Matrix e e K) (B : Matrix e v K) (C : Matrix v e K)
    (N : Matrix v v K) (h : N*(C*W*B)=1) :
    kernel W B C N*kernel W B C N=kernel W B C N := by
  calc kernel W B C N*kernel W B C N = (W*B)*(N*(C*W*B))*N*C := by
        simp only [kernel,Matrix.mul_assoc]
    _=kernel W B C N := by rw [h,Matrix.mul_one];rfl

omit [DecidableEq e] in

theorem trace_rank (W : Matrix e e K) (B : Matrix e v K) (C : Matrix v e K)
    (N : Matrix v v K) (h : N*(C*W*B)=1) :
    Matrix.trace (kernel W B C N)=(Fintype.card v : K) := by
  unfold kernel
  rw [Matrix.trace_mul_comm]
  have he : C*(W*B*N)=C*W*B*N := by simp only [Matrix.mul_assoc]
  rw [he,Matrix.trace_mul_comm,h]
  simp

/-- Inclusion-exclusion for one required and one forbidden edge. -/
theorem mixed_two (a b c d : K) : -(a*(d-1)-b*c)=a-(a*d-b*c) := by ring

/-- A positive conditional denominator is necessary to interpret an event ratio. -/
theorem conditional_ratio (p q r : ℚ) (hq : q ≠ 0) (h : p=q*r) : p/q=r := by
  rw [h];field_simp
end PerfectPower.ConnectionProjection
