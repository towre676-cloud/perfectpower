import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! The old-level fibre embedding used by the recursive Weil projector plan.
The row digits (k,s,r) represent r+p*(s+m*k); r=0 supports the lift.
Literal Fourier/chirp intertwining and orbit bounds are separate obligations.
-/
namespace PerfectPower.WeilOldLevel
open Matrix
open scoped BigOperators
variable (p m : ℕ) [NeZero p]

def lift (c : ℝ) : Matrix ((Fin p × Fin m) × Fin p) (Fin m) ℝ :=
  fun x y => if x.2=0 ∧ x.1.2=y then c else 0

theorem gram (c : ℝ) : (lift p m c).transpose * lift p m c = (p*c^2) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [lift,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.transpose_apply,
      Matrix.smul_apply,Matrix.one_apply,← pow_two,ite_and]
  · simp [lift,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.transpose_apply,
      Matrix.smul_apply,Matrix.one_apply,hij]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro r _
    split_ifs <;> simp_all

theorem isometry (c : ℝ) (hc : (p:ℝ)*c^2=1) :
    (lift p m c).transpose * lift p m c = 1 := by rw [gram,hc,one_smul]

theorem sqrt_normalization : (p:ℝ)*(1/Real.sqrt (p:ℝ))^2=1 := by
  have hp : 0<(p:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs := Real.sq_sqrt (le_of_lt hp)
  have hn : Real.sqrt (p:ℝ)≠0 := Real.sqrt_ne_zero'.mpr hp
  field_simp

theorem normalized_isometry :
    (lift p m (1/Real.sqrt (p:ℝ))).transpose * lift p m (1/Real.sqrt (p:ℝ))=1 :=
  isometry p m _ (sqrt_normalization p)

theorem old_projector_idempotent (c : ℝ) (hc : (p:ℝ)*c^2=1) :
    (lift p m c*(lift p m c).transpose)*(lift p m c*(lift p m c).transpose) =
      lift p m c*(lift p m c).transpose := by
  calc
    _ = lift p m c*((lift p m c).transpose*lift p m c)*(lift p m c).transpose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [isometry p m c hc]; simp

theorem old_projector_symmetric (c : ℝ) :
    (lift p m c*(lift p m c).transpose).IsSymm := by
  simp [Matrix.IsSymm,Matrix.transpose_mul]

end PerfectPower.WeilOldLevel
