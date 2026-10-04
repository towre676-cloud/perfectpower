import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

namespace PerfectPower.ConnectionDeterminant
open scoped BigOperators
variable {e : Type*} [Fintype e]

def minor (B : e → Fin 2 → ℂ) (i j : e) : ℂ := B i 0*B j 1-B j 0*B i 1

def gram (B : e → Fin 2 → ℂ) (w : e → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => ∑ i, w i * star (B i a) * B i b

/-- Two-column weighted Cauchy–Binet, with ordered pairs (each basis counted twice).
No nonzero weights or connected-support assumptions are needed. -/
theorem weighted_cauchy_binet_two (B : e → Fin 2 → ℂ) (w : e → ℂ) :
    2*(gram B w).det = ∑ i, ∑ j, w i*w j*star (minor B i j)*minor B i j := by
  have hex (i j : e) : w i*w j*star (minor B i j)*minor B i j =
      (w i*star (B i 0)*B i 0)*(w j*star (B j 1)*B j 1) +
      (w j*star (B j 0)*B j 0)*(w i*star (B i 1)*B i 1) -
      (w i*star (B i 0)*B i 1)*(w j*star (B j 1)*B j 0) -
      (w j*star (B j 0)*B j 1)*(w i*star (B i 1)*B i 0) := by
    simp only [minor, star_sub, star_mul]
    ring
  simp_rw [hex]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Matrix.det_fin_two]
  unfold gram
  ring

end PerfectPower.ConnectionDeterminant
