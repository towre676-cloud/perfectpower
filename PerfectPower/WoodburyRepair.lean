import Mathlib
noncomputable section
namespace PerfectPower.WoodburyRepair
open Matrix
variable {n k R : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] [Ring R]

def repair (P : Matrix n n R) (U : Matrix n k R) (Q : Matrix k k R)
    (V : Matrix k n R) := P - P*U*Q*V*P

theorem left_inverse (A P : Matrix n n R) (U : Matrix n k R)
    (V : Matrix k n R) (Q : Matrix k k R)
    (base : A*P=1) (defect : (1+V*P*U)*Q=1) :
    (A+U*V)*repair P U Q V=1 := by
  have hs : Q+(V*P*U)*Q=1 := by
    simpa only [Matrix.add_mul,Matrix.one_mul] using defect
  have h := congrArg (fun M : Matrix k k R => U*M*V*P) hs
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,Matrix.one_mul,
    ← Matrix.mul_assoc] at h
  unfold repair
  simp only [Matrix.add_mul,Matrix.mul_sub,← Matrix.mul_assoc,base,Matrix.one_mul]
  nth_rw 1 [← h]
  abel

theorem right_inverse (A P : Matrix n n R) (U : Matrix n k R)
    (V : Matrix k n R) (Q : Matrix k k R)
    (base : P*A=1) (defect : Q*(1+V*P*U)=1) :
    repair P U Q V*(A+U*V)=1 := by
  have hs : Q+Q*(V*P*U)=1 := by
    simpa only [Matrix.mul_add,Matrix.mul_one] using defect
  have h := congrArg (fun M : Matrix k k R => P*U*M*V) hs
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,Matrix.one_mul,
    Matrix.mul_assoc] at h
  unfold repair
  simp only [Matrix.sub_mul,Matrix.mul_add,Matrix.mul_assoc,base,Matrix.mul_one]
  nth_rw 1 [← h]
  abel

end PerfectPower.WoodburyRepair
