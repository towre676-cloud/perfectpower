import Mathlib
import PerfectPower.RankTwoSieve

namespace PerfectPower.IntegralPullback
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem image_iff (A : Matrix n n ℤ) (hA : A.det ≠ 0) (b : n → ℤ) :
    (∃ x : n → ℤ, A *ᵥ x = b) ↔ ∀ i, A.det ∣ (A.adjugate *ᵥ b) i := by
  constructor
  · rintro ⟨x, rfl⟩ i
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec_assoc, one_mulVec]
    exact ⟨x i, rfl⟩
  · intro h
    choose x hx using h
    have hv : A.adjugate *ᵥ b = A.det • x := by
      funext i
      exact hx i
    have he : A.det • (A *ᵥ x) = A.det • b := by
      rw [← mulVec_smul, ← hv, mulVec_mulVec, mul_adjugate, smul_mulVec_assoc, one_mulVec]
    refine ⟨x, ?_⟩
    funext i
    exact mul_left_cancel₀ hA (congrFun he i)

/-- The congruences produce the explicit integral inverse, not just existence. -/
theorem pullback (A : Matrix n n ℤ) (hA : A.det ≠ 0) (b : n → ℤ)
    (h : ∀ i, A.det ∣ (A.adjugate *ᵥ b) i) :
    A *ᵥ (fun i => (A.adjugate *ᵥ b) i / A.det) = b := by
  obtain ⟨x,hx⟩ := (image_iff A hA b).mpr h
  have hv : A.adjugate *ᵥ b = A.det • x := by
    rw [← hx, mulVec_mulVec, adjugate_mul, smul_mulVec_assoc, one_mulVec]
  have he : (fun i => (A.adjugate *ᵥ b) i / A.det) = x := by
    funext i
    rw [hv]
    change A.det * x i / A.det = x i
    exact Int.mul_ediv_cancel_left (x i) hA
  rw [he,hx]

/-- A certified congruence cut on a periodic orbit is exact for integral image membership. -/
theorem orbit_residue_iff {G : Type*} [Group G] (A : Matrix n n ℤ) (hA : A.det ≠ 0)
    (U V : G) (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hU : U^M=1) (hV : V^N=1) (readout : G → n → ℤ) (e f : ℤ) :
    (∃ x : n → ℤ, A *ᵥ x = readout (U^e*V^f)) ↔
    ((e % (M:ℤ)).toNat,(f % (N:ℤ)).toNat) ∈
      RankTwoSieve.allowed U V M N (fun g => ∀ i, A.det ∣ (A.adjugate *ᵥ readout g) i) := by
  classical
  rw [image_iff A hA]
  exact RankTwoSieve.signed_residue_iff U V M N hM hN hU hV (fun g => ∀ i, A.det ∣ (A.adjugate *ᵥ readout g) i) e f
end PerfectPower.IntegralPullback
