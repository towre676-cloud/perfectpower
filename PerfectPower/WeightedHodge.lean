import Mathlib

noncomputable section
namespace PerfectPower.WeightedHodge
open Matrix
variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
variable [DecidableEq n] [DecidableEq m] [DecidableEq k]
variable {K : Type*} [Field K]

/-- Weighted adjoint for a rectangular map, with an explicit domain inverse. -/
def adjoint (D : Matrix m n K) (NX : Matrix n n K) (MY : Matrix m m K) := NX*D.transpose*MY

omit [DecidableEq m] in
theorem adjoint_identity (D : Matrix m n K) (MX NX : Matrix n n K)
    (MY : Matrix m m K) (hX : MX*NX=1) : MX*adjoint D NX MY=D.transpose*MY := by
  simp only [adjoint,← Matrix.mul_assoc,hX,Matrix.one_mul]

/-- A column-space projector with a supplied inverse Gram matrix. -/
def projector (C : Matrix n k K) (M : Matrix n n K) (N : Matrix k k K) :=
  C*N*C.transpose*M

omit [DecidableEq n] in
theorem fixes_columns (C : Matrix n k K) (M : Matrix n n K) (N : Matrix k k K)
    (h : N*(C.transpose*M*C)=1) : projector C M N*C=C := by
  simp only [projector,Matrix.mul_assoc] at *
  rw [h,Matrix.mul_one]

omit [DecidableEq n] in
theorem projector_idempotent (C : Matrix n k K) (M : Matrix n n K) (N : Matrix k k K)
    (h : N*(C.transpose*M*C)=1) : projector C M N*projector C M N=projector C M N := by
  calc projector C M N*projector C M N = (projector C M N*C)*N*C.transpose*M := by
        simp only [projector,Matrix.mul_assoc]
    _ = projector C M N := by rw [fixes_columns C M N h]; rfl

omit [DecidableEq n] [DecidableEq k] in
theorem weighted_self_adjoint (C : Matrix n k K) (M : Matrix n n K) (N : Matrix k k K)
    (hM : M.transpose=M) (hN : N.transpose=N) :
    (projector C M N).transpose*M=M*projector C M N := by
  simp only [projector,transpose_mul,transpose_transpose,hM,hN,Matrix.mul_assoc]

/-- Orthogonal component projectors produce a third exact harmonic projector. -/
theorem harmonic_projector (G B : Matrix n n K) (hG : G*G=G) (hB : B*B=B)
    (hGB : G*B=0) (hBG : B*G=0) :
    let H := 1-G-B
    H*H=H ∧ G*H=0 ∧ B*H=0 ∧ H*G=0 ∧ H*B=0 ∧ G+B+H=1 := by
  dsimp
  simp only [mul_sub,sub_mul,Matrix.mul_one,Matrix.one_mul,hG,hB,hGB,hBG]
  constructor
  · abel
  constructor
  · abel
  constructor
  · abel
  constructor
  · abel
  constructor <;> abel

theorem harmonic_annihilated (L G B : Matrix n n K)
    (h : L=L*G+L*B) : L*(1-G-B)=0 := by
  calc L*(1-G-B)=L-(L*G+L*B) := by noncomm_ring
    _=0 := by rw [← h,sub_self]

/-- Regularization is a filter, and need not be idempotent. -/
theorem regularization_counterexample :
    let P : Matrix (Fin 2) (Fin 2) ℚ := !![(1/2),0;0,1]
    P*P ≠ P := by
  dsimp
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.mul_apply,Fin.sum_univ_two] at h00

end PerfectPower.WeightedHodge
