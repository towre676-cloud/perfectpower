import PerfectPower.Continuation.RationalHit

namespace PerfectPower.RationalYun
open Polynomial
open scoped BigOperators
noncomputable section

/-- A sum of natural numbers is one precisely when a unique summand is one. -/
theorem unique_summand_of_sum_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (h : ∑ i ∈ s, f i = 1) :
    ∃ i ∈ s, f i = 1 ∧ ∀ j ∈ s, j ≠ i → f j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp at h
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at h
    have hcases : f a = 0 ∨ f a = 1 := by omega
    rcases hcases with hz | ho
    · have hs : ∑ i ∈ s, f i = 1 := by omega
      obtain ⟨i, hi, hfi, hrest⟩ := ih hs
      refine ⟨i, Finset.mem_insert_of_mem hi, hfi, ?_⟩
      intro j hj hji
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hz
      · exact hrest j hj hji
    · refine ⟨a, Finset.mem_insert_self _ _, ho, ?_⟩
      intro j hj hja
      have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
      have hle := Finset.single_le_sum (fun i (_ : i ∈ s) => Nat.zero_le (f i)) hjs
      omega

/-- Number of distinct algebraic roots whose multiplicity is not divisible by d,
expressed intrinsically through rational squarefree layers. -/
def Decomposition.badDegree {F : ℚ[X]} (Y : Decomposition F) (d : ℕ) : ℕ :=
  ∑ j ∈ Finset.range Y.m, if d ∣ j + 1 then 0 else (Y.part (j + 1)).natDegree

/-- One bad root forces a rational linear factor and a positive residual exponent. -/
theorem Decomposition.radical_shape_of_badDegree_one {F : ℚ[X]}
    (Y : Decomposition F) {d : ℕ} (hd : 2 ≤ d) (hbad : Y.badDegree d = 1) :
    ∃ α : ℚ, ∃ r : ℕ, ∃ G : ℚ[X], 0 < r ∧ r < d ∧
      F = C Y.lead * (X - C α) ^ r * G ^ d := by
  classical
  obtain ⟨i, hi, hone, hrest⟩ := unique_summand_of_sum_one
    (Finset.range Y.m) (fun j => if d ∣ j + 1 then 0 else (Y.part (j + 1)).natDegree) hbad
  have hndvd : ¬ d ∣ i + 1 := by
    intro hdiv
    simp [hdiv] at hone
  have hlinear : (Y.part (i + 1)).natDegree = 1 := by simpa [hndvd] using hone
  have hothers : ∀ j ∈ Finset.range Y.m, j + 1 ≠ i + 1 →
      d ∣ j + 1 ∨ Y.part (j + 1) = 1 := by
    intro j hj hneq
    by_cases hdiv : d ∣ j + 1
    · exact Or.inl hdiv
    · right
      apply eq_one_of_monic_natDegree_zero (Y.part_monic (j + 1))
      have hjneq : j ≠ i := by omega
      simpa [hdiv] using hrest j hj hjneq
  obtain ⟨α, G, hshape⟩ := Y.radical_shape d (i + 1) (by omega)
    (by simpa using Finset.mem_range.mp hi) hlinear hothers
  refine ⟨α, (i + 1) % d, G, ?_, Nat.mod_lt _ (by omega), hshape⟩
  have hmod : (i + 1) % d ≠ 0 := by
    intro hz
    exact hndvd (Nat.dvd_of_mod_eq_zero hz)
  exact Nat.pos_of_ne_zero hmod

end
end PerfectPower.RationalYun
