import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic

/-! Squarefree multiplicity layers over the coefficient field.
The construction is noncomputable normalized factorization, not an executable
implementation of Yun's algorithm. No arithmetic finiteness premise is used. -/
namespace PerfectPower.RationalYun

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators
noncomputable section

/-- A monic squarefree-layer decomposition over Q. -/
structure Decomposition (F : ℚ[X]) where
  /-- Nonzero leading scalar. -/
  lead : ℚ
  /-- Monic squarefree factor at each multiplicity. -/
  part : ℕ → ℚ[X]
  /-- Finite cutoff used in the factorization identity. -/
  m : ℕ
  lead_ne : lead ≠ 0
  part_monic : ∀ j, (part j).Monic
  part_sq : ∀ j, Squarefree (part j)
  part_cop : ∀ i j, i ≠ j → IsCoprime (part i) (part j)
  eq_prod : F = C lead * ∏ j ∈ Finset.range m, part (j + 1) ^ (j + 1)

/-- Normalized irreducible factors, with repetitions for multiplicity. -/
def bag (F : ℚ[X]) : Multiset ℚ[X] := normalizedFactors F

/-- Distinct factors occurring with exactly the specified multiplicity. -/
def layerSet (F : ℚ[X]) (j : ℕ) : Finset ℚ[X] :=
  (bag F).toFinset.filter (fun p => (bag F).count p = j)

/-- Missing layers have value one. -/
def layer (F : ℚ[X]) (j : ℕ) : ℚ[X] := ∏ p ∈ layerSet F j, p

lemma normalized_irreducibles_coprime {p q : ℚ[X]} (hp : Irreducible p)
    (hq : Irreducible q) (hnp : normalize p = p) (hnq : normalize q = q)
    (hne : p ≠ q) : IsCoprime p q := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdvd
  exact hne ((hp.associated_of_dvd hq hdvd).eq_of_normalized hnp hnq)

lemma layer_mem {F : ℚ[X]} {j : ℕ} {p : ℚ[X]} (hp : p ∈ layerSet F j) :
    p ∈ bag F ∧ (bag F).count p = j := by
  simpa only [layerSet, Finset.mem_filter, Multiset.mem_toFinset] using hp

lemma layer_monic (F : ℚ[X]) (j : ℕ) : (layer F j).Monic := by
  apply monic_prod_of_monic
  intro p hp
  have hmem := (layer_mem hp).1
  have hirr := irreducible_of_normalized_factor p hmem
  exact (normalize_eq_self_iff_monic hirr.ne_zero).mp (normalize_normalized_factor p hmem)

lemma squarefree_product (s : Finset ℚ[X])
    (hirr : ∀ p ∈ s, Irreducible p) (hnorm : ∀ p ∈ s, normalize p = p) :
    Squarefree (∏ p ∈ s, p) := by
  have hne : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hirr p hp).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hne).mpr
  have hnf : normalizedFactors (∏ p ∈ s, p) = s.val := by
    change normalizedFactors (s.val.map id).prod = s.val
    rw [Multiset.map_id, normalizedFactors_prod_eq]
    · calc s.val.map normalize = s.val.map id :=
        Multiset.map_congr rfl (fun p hp => hnorm p hp)
        _ = s.val := Multiset.map_id _
    · exact hirr
  rw [hnf]
  exact s.nodup

lemma layer_squarefree (F : ℚ[X]) (j : ℕ) : Squarefree (layer F j) := by
  apply squarefree_product
  · intro p hp
    exact irreducible_of_normalized_factor p (layer_mem hp).1
  · intro p hp
    exact normalize_normalized_factor p (layer_mem hp).1

lemma layers_coprime (F : ℚ[X]) (i j : ℕ) (hij : i ≠ j) :
    IsCoprime (layer F i) (layer F j) := by
  apply IsCoprime.prod_left
  intro p hp
  apply IsCoprime.prod_right
  intro q hq
  have hp' := layer_mem hp
  have hq' := layer_mem hq
  apply normalized_irreducibles_coprime
    (irreducible_of_normalized_factor p hp'.1)
    (irreducible_of_normalized_factor q hq'.1)
    (normalize_normalized_factor p hp'.1)
    (normalize_normalized_factor q hq'.1)
  intro heq
  subst q
  exact hij (hp'.2.symm.trans hq'.2)

/-- Grouping a finite factor multiset by multiplicity, retaining empty layers. -/
lemma grouped_product (s : Multiset ℚ[X]) :
    (∏ j ∈ Finset.range s.card,
      (∏ p ∈ s.toFinset.filter (fun p => s.count p = j + 1), p) ^ (j + 1)) = s.prod := by
  classical
  have hmaps : ∀ p ∈ s.toFinset, s.count p - 1 ∈ Finset.range s.card := by
    intro p hp
    have hpos := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    have hbound := Multiset.count_le_card p s
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ∏ j ∈ Finset.range s.card,
        ∏ p ∈ s.toFinset.filter (fun p => s.count p - 1 = j), p ^ s.count p := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [← Finset.prod_pow]
      have hsets : s.toFinset.filter (fun p => s.count p = j + 1) =
          s.toFinset.filter (fun p => s.count p - 1 = j) := by
        apply Finset.filter_congr
        intro p hp
        have hpos := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
        omega
      rw [← hsets]
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∏ p ∈ s.toFinset, p ^ s.count p := Finset.prod_fiberwise_of_maps_to hmaps _
    _ = s.prod := (Finset.prod_multiset_count s).symm

/-- Existence for every nonzero rational polynomial; constants are included. -/
def ofNonzero (F : ℚ[X]) (hF : F ≠ 0) : Decomposition F where
  lead := F.leadingCoeff
  part := layer F
  m := (bag F).card
  lead_ne := leadingCoeff_ne_zero.mpr hF
  part_monic := layer_monic F
  part_sq := layer_squarefree F
  part_cop := layers_coprime F
  eq_prod := by
    unfold layer layerSet
    rw [grouped_product]
    exact (leadingCoeff_mul_prod_normalizedFactors F).symm

/-- The universal existence statement absent from the integer-comaximal interface. -/
theorem exists_decomposition (F : ℚ[X]) (hF : F ≠ 0) : Nonempty (Decomposition F) :=
  ⟨ofNonzero F hF⟩

/-- Integer inputs acquire a decomposition after mapping to Q[X]. -/
theorem exists_integer_decomposition (F : ℤ[X]) (hF : F ≠ 0) :
    Nonempty (Decomposition (F.map (Int.castRingHom ℚ))) := by
  apply exists_decomposition
  intro hzero
  apply hF
  apply Polynomial.map_injective (Int.castRingHom ℚ) (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
  simpa using hzero

/-- A decomposition with nonzero leading coefficient cannot represent zero. -/
theorem Decomposition.ne_zero {F : ℚ[X]} (Y : Decomposition F) : F ≠ 0 := by
  rw [Y.eq_prod]
  apply mul_ne_zero (by simpa using Y.lead_ne)
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (Y.part_monic (j + 1)).ne_zero

/-- Exact domain of existence: zero is excluded and all nonzero constants included. -/
theorem decomposition_iff_nonzero (F : ℚ[X]) : Nonempty (Decomposition F) ↔ F ≠ 0 := by
  constructor
  · rintro ⟨Y⟩
    exact Y.ne_zero
  · exact exists_decomposition F

/-- The historical integer coefficient-ring obstruction. -/
theorem not_isCoprime_integer_X_X_add_two :
    ¬ IsCoprime (X : ℤ[X]) (X + C 2) := by
  rintro ⟨a, b, h⟩
  have h0 := congrArg (fun P : ℤ[X] => P.eval 0) h
  simp only [eval_add, eval_mul, eval_X, eval_C, eval_one, mul_zero, zero_add] at h0
  omega

/-- Over the coefficient field the same factors have an explicit Bezout identity. -/
theorem isCoprime_rational_X_X_add_two : IsCoprime (X : ℚ[X]) (X + C 2) := by
  refine ⟨C (-1 / 2), C (1 / 2), ?_⟩
  rw [show (-1 / 2 : ℚ) = -(1 / 2) by ring, C_neg]
  calc -C (1 / 2 : ℚ) * X + C (1 / 2 : ℚ) * (X + C 2) =
      C (1 / 2 : ℚ) * C 2 := by ring
    _ = 1 := by rw [← C_mul]; norm_num

end
end PerfectPower.RationalYun
