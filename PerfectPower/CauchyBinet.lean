import PerfectPower.RectangularDeterminant

/-! Ordered Cauchy–Binet: each unordered minor is counted `card n` factorial times.
The identity holds over any commutative ring, without dividing by that factorial. -/
noncomputable section
namespace PerfectPower.CauchyBinet
open scoped BigOperators Classical
open Matrix Equiv
variable {n e R : Type*} [Fintype n] [DecidableEq n] [Fintype e] [CommRing R]

private theorem fixed_permutation (M : Matrix n e R) (N : Matrix e n R) (σ : Perm n) :
    (∑ p : n → e, Matrix.det (fun i j => M i (p j)) *
      (↑(Perm.sign σ) : R) * ∏ i, N (p (σ i)) i) = (M * N).det := by
  rw [PerfectPower.RectangularDeterminant.det_mul_expansion]
  apply Fintype.sum_equiv (Equiv.arrowCongr σ⁻¹ (Equiv.refl e))
  intro p
  have hd : Matrix.det (fun i j => M i (p (σ j))) =
      (↑(Perm.sign σ) : R) * Matrix.det (fun i j => M i (p j)) := by
    exact Matrix.det_permute' σ (fun i j => M i (p j))
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
  change _ = Matrix.det (fun i j => M i (p (σ j))) * ∏ i, N (p (σ i)) i
  rw [hd]
  ring

theorem ordered_cauchy_binet (M : Matrix n e R) (N : Matrix e n R) :
    ((Fintype.card n).factorial : R) * (M * N).det =
      ∑ p : n → e, Matrix.det (fun i j => M i (p j)) *
        Matrix.det (fun i j => N (p i) j) := by
  calc
    _ = ∑ σ : Perm n, (M * N).det := by
      simp [Fintype.card_perm, nsmul_eq_mul]
    _ = ∑ σ : Perm n, ∑ p : n → e,
        Matrix.det (fun i j => M i (p j)) * (↑(Perm.sign σ) : R) *
          ∏ i, N (p (σ i)) i := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (fixed_permutation M N σ).symm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Matrix.det_apply', Finset.mul_sum, mul_assoc]

/-- Weighted Gram matrix in any number of columns. -/
def gram [StarRing R] (B : Matrix e n R) (w : e → R) : Matrix n n R :=
  fun a b => ∑ i, star (B i a) * w i * B i b

/-- General weighted squared-minor identity, with ordered selections.
Repeated selections vanish; no nonzero-weight or rank hypothesis is needed. -/
theorem weighted_gram [StarRing R] (B : Matrix e n R) (w : e → R) :
    ((Fintype.card n).factorial : R) * (gram B w).det =
      ∑ p : n → e, (∏ i, w (p i)) *
        star (Matrix.det (fun i j => B (p i) j)) *
        Matrix.det (fun i j => B (p i) j) := by
  have h := ordered_cauchy_binet (Matrix.of (fun i j => star (B j i)))
    (Matrix.of (fun i j => w i * B i j))
  have hg : (Matrix.of (fun i j => star (B j i))) * (Matrix.of (fun i j => w i * B i j)) = gram B w := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, gram, mul_assoc]
  rw [hg] at h
  rw [h]
  simp only [Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro p _
  have hs : Matrix.det (fun i j => star (B (p j) i)) =
      star (Matrix.det (fun i j => B (p i) j)) :=
    Matrix.det_conjTranspose (fun i j => B (p i) j)
  have hw : Matrix.det (fun i j => w (p i) * B (p i) j) =
      (∏ i, w (p i)) * Matrix.det (fun i j => B (p i) j) :=
    Matrix.det_mul_column (fun i => w (p i)) (fun i j => B (p i) j)
  rw [hs, hw]
  ring

/-- When every maximal minor vanishes, the weighted Gram determinant vanishes.
Characteristic zero lets us cancel the ordered-selection multiplicity. -/
theorem gram_det_zero_of_minors_zero [StarRing R] [NoZeroDivisors R] [CharZero R]
    (B : Matrix e n R) (w : e → R)
    (h : ∀ p : n → e, Matrix.det (fun i j => B (p i) j) = 0) :
    (gram B w).det = 0 := by
  have he := weighted_gram B w
  simp only [h, mul_zero, Finset.sum_const_zero] at he
  exact (mul_eq_zero.mp he).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end PerfectPower.CauchyBinet
