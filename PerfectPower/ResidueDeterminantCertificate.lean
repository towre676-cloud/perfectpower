/-
Copyright 2026 OpenAI. Adapted for PerfectPower from openai/math
adc7f1241b42e322a6451854ab7e4b4c146bf78a, under Apache-2.0.
See third_party/openai_math/LICENSE and NOTICE.md for provenance.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

namespace PerfectPower.ResidueDeterminantCertificate
open Matrix
open scoped BigOperators

open MvPolynomial

theorem pow_sum_dvd_det_of_row_dvd {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : R) (w : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i j, q ^ w i ∣ A i j) : q ^ (∑ i, w i) ∣ A.det := by
  choose B hB using hA
  have hmatrix : A = Matrix.of (fun i j => q ^ w i * B i j) := by
    ext i j
    exact hB i j
  rw [hmatrix]
  change q ^ (∑ i, w i) ∣ (Matrix.of (fun i j => q ^ w i * (Matrix.of B) i j)).det
  rw [Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

theorem determinant_dvd_of_local_expansion
    {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (q : R) (m : ℕ) (w : τ → ℕ)
    (v : τ → ι → R) (c : ι → τ → R)
    (hv : ∀ a j, q ^ w a ∣ v a j)
    (hm : ∀ r : ι → τ, Function.Injective r → m ≤ ∑ i, w (r i)) :
    q ^ m ∣ (Matrix.of (fun i j => ∑ a, c i a * v a j)).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  have hexpand : (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
    change L (fun i j => ∑ a, c i a * v a j) =
      ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
    have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
    simp only [AlternatingMap.coe_multilinearMap] at h
    have hfun : (fun i => ∑ a, c i a • v a) =
        (fun i j => ∑ a, c i a * v a j) := by
      funext i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun] at h
    have hs (r : ι → τ) : L (fun i => c i (r i) • v (r i)) =
        (∏ i, c i (r i)) * L (fun i => v (r i)) := by
      exact L.toMultilinearMap.map_smul_univ (fun i => c i (r i)) (fun i => v (r i))
    simpa only [hs] using h
  rw [hexpand]
  apply Finset.dvd_sum
  intro r _
  by_cases hr : Function.Injective r
  · apply dvd_mul_of_dvd_right
    exact (pow_dvd_pow q (hm r hr)).trans
      (pow_sum_dvd_det_of_row_dvd q (fun i => w (r i)) _ (fun i j => hv (r i) j))
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hr
    have hz : (Matrix.of (fun i => v (r i))).det = 0 := by
      exact L.map_eq_zero_of_eq (fun i => v (r i)) (congrArg v hab) hne
    rw [hz, mul_zero]
    exact dvd_zero _

theorem determinant_dvd_polynomial_eval {σ ι R : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] (q : R) (m : ℕ)
    (P : ι → MvPolynomial σ R) (x : ι → σ → R)
    (hx : ∀ j a, q ∣ x j a)
    (hm : ∀ r : ι → (σ →₀ ℕ), Function.Injective r →
      m ≤ ∑ i, (r i).sum (fun _ e => e)) :
    q ^ m ∣ (Matrix.of (fun i j => eval (x j) (P i))).det := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion (fun i => (P i).support)
  let v : s → ι → R := fun a j => a.val.prod (fun l e => x j l ^ e)
  let c : ι → s → R := fun i a => (P i).coeff a.val
  have hv : ∀ a j, q ^ a.val.sum (fun _ e => e) ∣ v a j := by
    intro a j
    dsimp [v, Finsupp.sum, Finsupp.prod]
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun l _ => pow_dvd_pow_of_dvd (hx j l) _)
  have hweight : ∀ r : ι → s, Function.Injective r →
      m ≤ ∑ i, (r i).val.sum (fun _ e => e) := by
    intro r hr
    exact hm (fun i => (r i).val) (Subtype.val_injective.comp hr)
  have heq : (Matrix.of (fun i j => eval (x j) (P i))) =
      Matrix.of (fun i j => ∑ a : s, c i a * v a j) := by
    ext i j
    simp only [Matrix.of_apply, c, v, Finsupp.prod, eval_eq]
    rw [Finset.sum_coe_sort s (fun a => (P i).coeff a * ∏ l ∈ a.support, x j l ^ a l)]
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩
    · intro a _ ha
      have hz : (P i).coeff a = 0 := by
        simpa only [MvPolynomial.mem_support_iff, not_not] using ha
      simp only [hz, zero_mul]
  rw [heq]
  exact determinant_dvd_of_local_expansion q m (fun a : s => a.val.sum (fun _ e => e))
    v c hv hweight

theorem det_abs_le_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]


/-- Any integer multiple too small to be nonzero is zero. The magnitude and
    divisibility obligations remain explicit; no global point bound is assumed. -/
theorem determinant_zero_of_divisor_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (D : ℤ) (B : ι → ℝ)
    (hdiv : D ∣ A.det) (hA : ∀ i j, |(A i j : ℝ)| ≤ B i)
    (hlt : (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i < (D : ℝ)) :
    A.det = 0 := by
  apply Int.eq_zero_of_abs_lt_dvd hdiv
  have hbound := det_abs_le_row_product ((Int.castRingHom ℝ).mapMatrix A) B hA
  rw [← (Int.castRingHom ℝ).map_det] at hbound
  have h := hbound.trans_lt hlt
  change |(A.det : ℝ)| < (D : ℝ) at h
  exact_mod_cast h

/-- Exact integral row transformations may have a nonunit determinant.
    Coprimality with the divisor is the necessary cancellation obligation. -/
theorem determinant_dvd_of_transform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A E : Matrix ι ι ℤ) (D : ℤ) (hcoprime : IsCoprime D E.det)
    (hdiv : D ∣ (E * A).det) : D ∣ A.det := by
  rw [Matrix.det_mul] at hdiv
  exact hcoprime.dvd_of_dvd_mul_left hdiv

/-- A nonzero column gives an integral annihilating relation. This does not
    assert that all integral kernel vectors are generated by these columns. -/
theorem relation_of_kernel_column {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℤ) (K : Matrix κ κ ℤ)
    (hAK : A * K = 0) (j : κ) (hj : (fun i => K i j) ≠ 0) :
    ∃ c : κ → ℤ, c ≠ 0 ∧ A *ᵥ c = 0 := by
  refine ⟨fun i => K i j, hj, ?_⟩
  ext i
  exact congrArg (fun M => M i j) hAK

end PerfectPower.ResidueDeterminantCertificate
