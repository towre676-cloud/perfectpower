import PerfectPower.MordellCompletionBridge

open PerfectPower.MordellCompletionBridge

#print axioms mem_of_bounded_multiple
#print axioms boundedIndex_of_finite_quotient
#print axioms eq_top_of_bounded_index
#print axioms mem_of_supported_multiple
#print axioms eq_top_of_prime_support
#print axioms not_divisible_of_reduction
#print axioms prime_saturated_of_reduction_separation
#print axioms mem_integralBox_iff
#print axioms integralBox_complete
#print axioms integralList_complete

-- A finite cutoff alone cannot imply global saturation: 17 Z passes all the
-- primes up to 13 but remains a proper subgroup.
example : ∀ p : ℕ, p.Prime → p ≤ 13 →
    PrimeSaturated (AddSubgroup.zmultiples (17 : ℤ)) p := by
  intro p hp hp13 g hg
  rw [Int.mem_zmultiples_iff] at hg ⊢
  have h17 : Prime (17 : ℤ) := by norm_num
  have hnot : ¬ (17 : ℤ) ∣ (p : ℤ) := by
    intro h
    have hnat : 17 ∣ p := Int.natCast_dvd_natCast.mp h
    have hle := Nat.le_of_dvd hp.pos hnat
    omega
  exact (h17.dvd_mul.mp (by simpa [nsmul_eq_mul] using hg)).resolve_left hnot

example : AddSubgroup.zmultiples (17 : ℤ) ≠ ⊤ := by
  intro h
  have hmem : (1 : ℤ) ∈ AddSubgroup.zmultiples (17 : ℤ) := by rw [h]; trivial
  norm_num [Int.mem_zmultiples_iff] at hmem

example : (1 : ℤ) ∉ (integralBox (-2) 3 5).image Prod.fst := by decide +kernel

example : integralBox (-2) 3 5 = {(3, -5), (3, 5)} := by decide +kernel

-- Finite enumeration cannot infer a global coordinate bound.
example : integralBox (-2) 2 4 = ∅ := by decide +kernel
example : (5 : ℤ) ^ 2 = (3 : ℤ) ^ 3 - 2 := by norm_num
