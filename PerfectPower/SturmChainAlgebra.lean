import Mathlib
namespace PerfectPower.SturmChainAlgebra
open scoped BigOperators

/-- A positively rescaled signed remainder forces opposite signs at a middle zero. -/
theorem remainder_opposite (a b c q scale : ℚ) (hscale : 0 < scale)
    (h : a=q*b-scale*c) (hb : b=0) (hc : c ≠ 0) :
    (a<0 ∧ 0<c) ∨ (0<a ∧ c<0) := by
  rw [hb,mul_zero,zero_sub] at h
  rcases lt_or_gt_of_ne hc with hc | hc
  · right
    constructor
    · have := mul_neg_of_pos_of_neg hscale hc
      rw [h]
      exact neg_pos.mpr this
    · exact hc
  · left
    constructor
    · have := mul_pos hscale hc
      rw [h]
      exact neg_neg_of_pos this
    · exact hc

/-- Signed remainder identities propagate a common zero to the next polynomial. -/
theorem zero_propagates (a b c q scale : ℚ) (hscale : scale ≠ 0)
    (h : a=q*b-scale*c) (ha : a=0) (hb : b=0) : c=0 := by
  have he : scale*c=0 := by
    rw [ha,hb,mul_zero,zero_sub] at h
    simpa using h.symm
  exact (mul_eq_zero.mp he).resolve_left hscale

/-- An explicit Bezout identity rules out a common zero without trusting gcd discovery. -/
theorem bezout_separates (a b u v : ℚ) (h : u*a+v*b=1) : a ≠ 0 ∨ b ≠ 0 := by
  by_contra hn
  push_neg at hn
  rcases hn with ⟨ha,hb⟩
  norm_num [ha,hb] at h

/-- Every positive multiplicity retains exactly the same zero set. -/
theorem multiplicity_roots {ι : Type*} [Fintype ι] (f : ι → ℚ) (m : ι → ℕ)
    (hm : ∀ i, m i ≠ 0) (c : ℚ) (hc : c ≠ 0) :
    c*(∏ i,(f i)^(m i))=0 ↔ ∃ i,f i=0 := by
  rw [mul_eq_zero]
  simp only [hc,false_or,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩;exact ⟨i,pow_eq_zero hi⟩
  · rintro ⟨i,hi⟩;exact ⟨i,by simp [hi,hm i]⟩

end PerfectPower.SturmChainAlgebra
