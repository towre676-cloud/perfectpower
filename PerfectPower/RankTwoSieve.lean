import Mathlib

/-! Exact modular reduction of two signed unit exponents. The receiver may include
multiplication by a nonunit norm representative. No global exponent bound is asserted. -/
namespace PerfectPower.RankTwoSieve

variable {G : Type*} [Group G]

theorem signed_periodic (A B : G) (M N : ℕ) (hA : A ^ M = 1) (hB : B ^ N = 1)
    (e f : ℤ) :
    A ^ e * B ^ f = A ^ (e % (M : ℤ)) * B ^ (f % (N : ℤ)) := by
  rw [zpow_eq_zpow_emod' e hA, zpow_eq_zpow_emod' f hB]

def allowed (A B : G) (M N : ℕ) (C : G → Prop) [DecidablePred C] : Finset (ℕ × ℕ) :=
  ((Finset.range M).product (Finset.range N)).filter fun r => C (A ^ r.1 * B ^ r.2)

theorem signed_residue_iff (A B : G) (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hA : A ^ M = 1) (hB : B ^ N = 1) (C : G → Prop) [DecidablePred C]
    (e f : ℤ) :
    C (A ^ e * B ^ f) ↔
      ((e % (M : ℤ)).toNat, (f % (N : ℤ)).toNat) ∈ allowed A B M N C := by
  have he : 0 ≤ e % (M : ℤ) := Int.emod_nonneg _ (by omega)
  have hf : 0 ≤ f % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have he' : e % (M : ℤ) < M := Int.emod_lt_of_pos _ (by omega)
  have hf' : f % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have hre : (e % (M : ℤ)).toNat < M := by omega
  have hrf : (f % (N : ℤ)).toNat < N := by omega
  rw [signed_periodic A B M N hA hB e f]
  have hmem : ((e % (M : ℤ)).toNat, (f % (N : ℤ)).toNat) ∈
      (Finset.range M).product (Finset.range N) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hre, Finset.mem_range.mpr hrf⟩
  simp only [allowed, Finset.mem_filter, hmem, true_and]
  rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg he, Int.toNat_of_nonneg hf]


/-- Independent local necessary conditions can be intersected without discarding
an actual solution. This does not claim the intersection is globally sufficient. -/
theorem intersect_necessary {α : Type*} (S T U : α → Prop)
    (hT : ∀ x, S x → T x) (hU : ∀ x, S x → U x) :
    ∀ x, S x → T x ∧ U x := by
  intro x hx
  exact ⟨hT x hx, hU x hx⟩

end PerfectPower.RankTwoSieve
