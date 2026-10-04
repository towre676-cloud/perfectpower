import PerfectPower.DeterminantalEvents
noncomputable section
namespace PerfectPower.FiniteGraphProbability
open Matrix
open scoped BigOperators
variable {e Ω : Type*} [Fintype e] [DecidableEq e] [Fintype Ω]
variable {R : Type*} [CommRing R]

def indicator (O : Finset e) (i : e) : R := if i ∈ O then 1 else 0

omit [Fintype e] in
theorem product_indicator (S O : Finset e) :
    (∏ i ∈ S, indicator O i : R) = if S ⊆ O then 1 else 0 := by
  by_cases h : S ⊆ O
  · simp only [h,if_true]
    apply Finset.prod_eq_one
    intro i hi
    simp [indicator,h hi]
  · simp only [h,if_false]
    obtain ⟨i,hi,ho⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [indicator,ho])

omit [Fintype e] in
theorem product_avoid (S O : Finset e) :
    (∏ i ∈ S, (1-indicator O i) : R) = if Disjoint S O then 1 else 0 := by
  by_cases h : Disjoint S O
  · simp only [h,if_true]
    apply Finset.prod_eq_one
    intro i hi
    simp [indicator,Finset.disjoint_left.mp h hi]
  · simp only [h,if_false]
    rw [Finset.disjoint_left] at h
    push_neg at h
    obtain ⟨i,hi,ho⟩ := h
    exact Finset.prod_eq_zero hi (by simp [indicator,ho])

def inclusion (w : Ω → R) (O : Ω → Finset e) (S : Finset e) : R :=
  ∑ o, if S ⊆ O o then w o else 0

def eventMass (w : Ω → R) (O : Ω → Finset e) (I J : Finset e) : R :=
  ∑ o, if I ⊆ O o ∧ Disjoint J (O o) then w o else 0

theorem padded_indicator (S O : Finset e) :
    det (DeterminantalEvents.padded (diagonal (indicator O : e → R)) S) =
      if S ⊆ O then 1 else 0 := by
  have he : DeterminantalEvents.padded (diagonal (indicator O : e → R)) S =
      diagonal (fun i => if i ∈ S then indicator O i else 1) := by
    ext i j
    by_cases h : i=j
    · subst j
      by_cases hi : i ∈ S <;> simp [DeterminantalEvents.padded,Finset.piecewise,diagonal_apply,hi]
    · by_cases hi : i ∈ S <;> simp [DeterminantalEvents.padded,Finset.piecewise,diagonal_apply,hi,h]
  rw [he,det_diagonal,Fintype.prod_ite_mem,product_indicator]

/-- Inclusion moments suffice for every mixed event, rather than only pairs of edges. -/
theorem mixed_probability (w : Ω → R) (O : Ω → Finset e) (K : Matrix e e R)
    (hlaw : ∀ S, det (DeterminantalEvents.padded K S)=inclusion w O S)
    (I J : Finset e) (hIJ : Disjoint I J) :
    DeterminantalEvents.mixed K I J=eventMass w O I J := by
  have h := DeterminantalEvents.expectation_mixed w (fun o => indicator (O o)) K
    (by
      intro S
      rw [hlaw]
      simp only [inclusion,padded_indicator]
      apply Finset.sum_congr rfl
      intro o ho
      split_ifs <;> simp) I J hIJ
  rw [h]
  simp_rw [product_indicator,product_avoid]
  unfold eventMass
  apply Finset.sum_congr rfl
  intro o ho
  split_ifs <;> simp_all

omit [Fintype e] in
/-- Genuine probabilities are bounded, provided the finite weights are normalized and nonnegative. -/
theorem event_bounds (w : Ω → ℝ) (O : Ω → Finset e) (hw : ∀ o, 0 ≤ w o)
    (hn : ∑ o,w o=1) (I J : Finset e) :
    0 ≤ eventMass w O I J ∧ eventMass w O I J ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro o ho
    split_ifs
    · exact hw o
    · norm_num
  · rw [← hn]
    apply Finset.sum_le_sum
    intro o ho
    split_ifs
    · exact le_rfl
    · exact hw o

omit [Fintype e] in
theorem rational_event_bounds (w : Ω → ℚ) (O : Ω → Finset e) (hw : ∀ o, 0 ≤ w o)
    (hn : ∑ o,w o=1) (I J : Finset e) :
    0 ≤ eventMass w O I J ∧ eventMass w O I J ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro o ho
    split_ifs
    · exact hw o
    · norm_num
  · rw [← hn]
    apply Finset.sum_le_sum
    intro o ho
    split_ifs
    · exact le_rfl
    · exact hw o

omit [Fintype e] in
theorem refinement_le (w : Ω → ℚ) (O : Ω → Finset e) (hw : ∀ o,0 ≤ w o)
    (I J A B : Finset e) : eventMass w O (I ∪ A) (J ∪ B) ≤ eventMass w O I J := by
  apply Finset.sum_le_sum
  intro o ho
  by_cases hr : (I ∪ A) ⊆ O o ∧ Disjoint (J ∪ B) (O o)
  · have hb : I ⊆ O o ∧ Disjoint J (O o) :=
      ⟨fun i hi => hr.1 (Finset.mem_union_left A hi),
        (Finset.disjoint_union_left.mp hr.2).1⟩
    simp [hr,hb]
  · simp only [hr,if_false]
    split_ifs
    · exact hw o
    · exact le_rfl

omit [Fintype e] in
theorem conditional_bounds (w : Ω → ℚ) (O : Ω → Finset e) (hw : ∀ o,0 ≤ w o)
    (I J A B : Finset e) (hq : 0 < eventMass w O I J) :
    0 ≤ eventMass w O (I ∪ A) (J ∪ B) / eventMass w O I J ∧
      eventMass w O (I ∪ A) (J ∪ B) / eventMass w O I J ≤ 1 := by
  have hp : 0 ≤ eventMass w O (I ∪ A) (J ∪ B) := by
    apply Finset.sum_nonneg
    intro o ho
    split_ifs
    · exact hw o
    · exact le_rfl
  exact ⟨div_nonneg hp hq.le, (div_le_one hq).mpr (refinement_le w O hw I J A B)⟩

end PerfectPower.FiniteGraphProbability
