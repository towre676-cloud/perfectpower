import PerfectPower.Continuation.RationalYun

namespace PerfectPower.RationalYun
open Polynomial
open scoped BigOperators
noncomputable section

/-- Remove the full d-th powers layer by layer. -/
def Decomposition.quotientPart {F : ℚ[X]} (Y : Decomposition F) (d : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range Y.m, Y.part (j + 1) ^ ((j + 1) / d)

/-- Keep the multiplicity residues modulo d. -/
def Decomposition.remainderPart {F : ℚ[X]} (Y : Decomposition F) (d : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range Y.m, Y.part (j + 1) ^ ((j + 1) % d)

/-- Structural factor extraction, before any pointwise root test or counting.
The identity even handles d=0; classification applications use d>=2. -/
theorem Decomposition.powerSplit {F : ℚ[X]} (Y : Decomposition F) (d : ℕ) :
    F = C Y.lead * Y.remainderPart d * (Y.quotientPart d) ^ d := by
  conv_lhs => rw [Y.eq_prod]
  unfold Decomposition.remainderPart Decomposition.quotientPart
  rw [mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [Nat.mul_comm ((j + 1) / d) d]
  exact (Nat.mod_add_div (j + 1) d).symm

/-- Degree accounting for a decomposition, including empty/constant layers. -/
theorem Decomposition.weighted_degree {F : ℚ[X]} (Y : Decomposition F) :
    F.natDegree = ∑ j ∈ Finset.range Y.m, (j + 1) * (Y.part (j + 1)).natDegree := by
  conv_lhs => rw [Y.eq_prod]
  rw [natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr Y.lead_ne)]
  rw [natDegree_prod]
  · simp only [natDegree_pow]
  · intro j hj
    exact pow_ne_zero _ (Y.part_monic (j + 1)).ne_zero

/-- A single residual multiplicity layer is the structural radical case.
Its degree-one/linear normalization is a separate corollary. -/
theorem Decomposition.single_remainder {F : ℚ[X]} (Y : Decomposition F) (d r : ℕ)
    (hr : 1 ≤ r) (hrm : r ≤ Y.m)
    (hothers : ∀ j ∈ Finset.range Y.m, j + 1 ≠ r →
      d ∣ j + 1 ∨ Y.part (j + 1) = 1) :
    Y.remainderPart d = Y.part r ^ (r % d) := by
  unfold Decomposition.remainderPart
  have hmem : r - 1 ∈ Finset.range Y.m := Finset.mem_range.mpr (by omega)
  rw [Finset.prod_eq_single_of_mem (r - 1) hmem]
  · congr 2 <;> omega
  · intro j hj hneq
    have hjr : j + 1 ≠ r := by omega
    rcases hothers j hj hjr with hdvd | hone
    · rw [Nat.mod_eq_zero_of_dvd hdvd, pow_zero]
    · rw [hone, one_pow]

/-- The structural Pell case: all nontrivial residual exponents are e,
and their product supplies the quadratic factor when its degree is two. -/
theorem Decomposition.uniform_remainder {F : ℚ[X]} (Y : Decomposition F) (d e : ℕ)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % d = 0 ∨ (j + 1) % d = e ∨ Y.part (j + 1) = 1) :
    Y.remainderPart d =
      (∏ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % d = e), Y.part (j + 1)) ^ e := by
  classical
  unfold Decomposition.remainderPart
  rw [← Finset.prod_pow]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases he : (j + 1) % d = e
  · simp [he]
  · simp only [he, ite_false]
    rcases hres j hj with hz | heq | hone
    · rw [hz, pow_zero]
    · exact (he heq).elim
    · rw [hone, one_pow]

/-- Monicity of every layer fixes the leading scalar uniquely. -/
theorem Decomposition.lead_eq_leadingCoeff {F : ℚ[X]} (Y : Decomposition F) :
    Y.lead = F.leadingCoeff := by
  have hmon : (∏ j ∈ Finset.range Y.m, Y.part (j + 1) ^ (j + 1)).Monic :=
    monic_prod_of_monic _ _ (fun j _ => (Y.part_monic (j + 1)).pow (j + 1))
  have h := congrArg Polynomial.leadingCoeff Y.eq_prod
  simp only [leadingCoeff_mul, leadingCoeff_C, hmon.leadingCoeff, mul_one] at h
  exact h.symm

/-- A unique degree-one residual layer yields the rational linear-factor form. -/
theorem Decomposition.radical_shape {F : ℚ[X]} (Y : Decomposition F) (d r : ℕ)
    (hr : 1 ≤ r) (hrm : r ≤ Y.m) (hlinear : (Y.part r).natDegree = 1)
    (hothers : ∀ j ∈ Finset.range Y.m, j + 1 ≠ r →
      d ∣ j + 1 ∨ Y.part (j + 1) = 1) :
    ∃ α : ℚ, ∃ G : ℚ[X],
      F = C Y.lead * (X - C α) ^ (r % d) * G ^ d := by
  refine ⟨-(Y.part r).coeff 0, Y.quotientPart d, ?_⟩
  have hpart : Y.part r = X - C (-(Y.part r).coeff 0) := by
    simpa only [C_neg, sub_neg_eq_add] using (Y.part_monic r).eq_X_add_C hlinear
  have hshape := Y.powerSplit d
  rw [Y.single_remainder d r hr hrm hothers, hpart] at hshape
  exact hshape

/-- The quadratic factor used by the Pell reduction. -/
def Decomposition.pellPart {F : ℚ[X]} (Y : Decomposition F) (e : ℕ) : ℚ[X] :=
  ∏ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e), Y.part (j + 1)

/-- Quadratic residual degree and uniform half-exponents give the Pell shape. -/
theorem Decomposition.pell_shape {F : ℚ[X]} (Y : Decomposition F) (e : ℕ)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % (2 * e) = 0 ∨ (j + 1) % (2 * e) = e ∨ Y.part (j + 1) = 1)
    (hdegree : (∑ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e),
      (Y.part (j + 1)).natDegree) = 2) :
    (Y.pellPart e).Monic ∧ (Y.pellPart e).natDegree = 2 ∧
      F = C Y.lead * (Y.pellPart e) ^ e * (Y.quotientPart (2 * e)) ^ (2 * e) := by
  have hmon : (Y.pellPart e).Monic := monic_prod_of_monic _ _ (fun j _ => Y.part_monic (j + 1))
  refine ⟨hmon, ?_, ?_⟩
  · unfold Decomposition.pellPart
    rw [natDegree_prod _ _ (fun j _ => (Y.part_monic (j + 1)).ne_zero)]
    exact hdegree
  · have hshape := Y.powerSplit (2 * e)
    rw [Y.uniform_remainder (2 * e) e hres] at hshape
    exact hshape

end
end PerfectPower.RationalYun
