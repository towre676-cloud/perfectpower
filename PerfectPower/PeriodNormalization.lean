import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace PerfectPower.PeriodNormalization
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K]

/-- A supplied left and right inverse produces the unique finite period correction. -/
theorem period_correction (M N : Matrix ι ι K) (hMN : M*N=1) (hNM : N*M=1)
    (candidate target : ι → K) :
    candidate + M *ᵥ (N *ᵥ (target-candidate)) = target ∧
    ∀ c : ι → K, candidate+M *ᵥ c=target → c=N *ᵥ (target-candidate) := by
  constructor
  · rw [mulVec_mulVec, hMN, one_mulVec]
    abel
  · intro c h
    have hm : M *ᵥ c = target-candidate := by rw [← h]; abel
    rw [← hm, mulVec_mulVec, hNM, one_mulVec]

end PerfectPower.PeriodNormalization
