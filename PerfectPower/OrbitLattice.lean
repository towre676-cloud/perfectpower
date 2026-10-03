import PerfectPower.SkolemZeros

/-! Exact image condition and periodic congruences, before orbit-zero enumeration. -/
namespace PerfectPower.OrbitLattice
open Matrix SkolemP

/-- The image of (u,v) ↦ (a*u+h*v,-v,0), without division or sign assumptions on a. -/
theorem image_iff (a h w0 w1 w2 : ℤ) :
    (∃ u v : ℤ, w0 = a*u+h*v ∧ w1 = -v ∧ w2 = 0) ↔
      w2 = 0 ∧ a ∣ w0+h*w1 := by
  constructor
  · rintro ⟨u,v,rfl,rfl,rfl⟩
    refine ⟨rfl,u,?_⟩; ring
  · rintro ⟨h0,u,hu⟩
    refine ⟨u,-w1,?_,by ring,h0⟩
    linarith

/-- Every entry of a weighted orbit is periodic modulo q under a certified matrix period.
No invertibility of the representative Γ is needed. -/
theorem weighted_entry_mod (q M : ℕ) (A D Γ : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A^M = 1+q • D) (N : ℕ) (i j : Fin 3) :
    (q : ℤ) ∣ (A^N*Γ) i j - (A^(N%M)*Γ) i j := by
  obtain ⟨W,hW⟩ := one_add_pow q D (N/M)
  have e : A^N = (A^M)^(N/M)*A^(N%M) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [e,hA,hW,Matrix.mul_assoc,add_mul,one_mul,smul_mul_assoc,
    Matrix.add_apply,Matrix.smul_apply,nsmul_eq_mul]
  exact ⟨(W*(A^(N%M)*Γ)) i j,by ring⟩
end PerfectPower.OrbitLattice
