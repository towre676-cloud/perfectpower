import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Rectangular determinant expansion in arbitrary column dimension, including
rank-deficient supports. Repeated selected columns vanish automatically. -/
noncomputable section
namespace PerfectPower.RectangularDeterminant
open scoped BigOperators Classical
open Matrix Equiv
variable {n e R : Type*} [Fintype n] [DecidableEq n] [Fintype e] [CommRing R]

/-- The multilinear rectangular expansion, before grouping by unordered bases. -/
theorem det_mul_expansion (M : Matrix n e R) (N : Matrix e n R) :
    (M * N).det = ∑ p : n → e,
      Matrix.det (fun i j => M i (p j)) * ∏ j, N (p j) j := by
  calc
    (M * N).det = ∑ p : n → e, ∑ σ : Perm n,
        (↑(Equiv.Perm.sign σ) : R) * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [det_apply', Finset.prod_mul_distrib, Finset.sum_mul, mul_assoc]

omit [Fintype e] in
theorem repeated_selection_zero (M : Matrix n e R) (p : n → e)
    (hp : ¬ Function.Injective p) : Matrix.det (fun i j => M i (p j)) = 0 := by
  unfold Function.Injective at hp
  push_neg at hp
  obtain ⟨i, j, he, hn⟩ := hp
  exact Matrix.det_zero_of_column_eq hn (by intro k; rw [he])

/-- Only injective row selections contribute. This is valid even when there are
fewer rows than columns, without dividing by a factorial in the coefficient ring. -/
theorem det_mul_injective [DecidableEq e] (M : Matrix n e R) (N : Matrix e n R) :
    (M * N).det = ∑ p : n → e with Function.Injective p,
      Matrix.det (fun i j => M i (p j)) * ∏ j, N (p j) j := by
  classical
  rw [det_mul_expansion]
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro p _ hp
  have hn : ¬ Function.Injective p := by simpa using hp
  rw [repeated_selection_zero M p hn, zero_mul]

end PerfectPower.RectangularDeterminant
