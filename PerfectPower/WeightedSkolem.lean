import PerfectPower.SkolemZeros

/-! Finite zeros on weighted orbits. The right factor Γ carries the norm representative;
no invertibility or commutation of Γ is assumed. Apply separately to the inverse orbit. -/
namespace PerfectPower.WeightedSkolem
open Matrix SkolemP SkolemZeros
variable {p : ℕ} [hp : Fact p.Prime]

/-- **The finite zero set.**  Under the per-class tests, every zero of `(A^N)₂₀` lies below `M`. -/
theorem weighted_corner_zeros (hp3 : 3 ≤ p) {M : ℕ} (hM : 0 < M) {A D Γ : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : A ^ M = 1 + p • D)
    (hcls : ∀ r, r < M → ¬ (p : ℤ) ∣ (A ^ r * Γ) 2 0 ∨ ((A ^ r * Γ) 2 0 = 0 ∧ ¬ (p : ℤ) ∣ (D * (A ^ r * Γ)) 2 0))
    (N : ℕ) (hN : (A ^ N * Γ) 2 0 = 0) : N < M := by
  obtain ⟨m, r, hrM, rfl⟩ : ∃ m r, r < M ∧ N = M * m + r :=
    ⟨N / M, N % M, Nat.mod_lt _ hM, (Nat.div_add_mod N M).symm⟩
  rw [pow_add, pow_mul, hA, Matrix.mul_assoc] at hN
  rcases hcls r hrM with hnd | ⟨h0, h1⟩
  · exfalso
    obtain ⟨W, hW⟩ := one_add_pow p D m
    rw [hW, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at hN
    exact hnd ⟨-((W * (A ^ r * Γ)) 2 0), by linarith⟩
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using hrM
    · exfalso
      rw [corner_pow_mul] at hN
      exact sum_ne_zero hp3 m hm (fun k => (D ^ k * (A ^ r * Γ)) 2 0) (by simpa using h0) (by simpa using h1) hN

/-- The same as an `iff` with a decidable right side. -/
theorem weighted_corner_zeros_iff (hp3 : 3 ≤ p) {M : ℕ} (hM : 0 < M) {A D Γ : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : A ^ M = 1 + p • D)
    (hcls : ∀ r, r < M → ¬ (p : ℤ) ∣ (A ^ r * Γ) 2 0 ∨ ((A ^ r * Γ) 2 0 = 0 ∧ ¬ (p : ℤ) ∣ (D * (A ^ r * Γ)) 2 0))
    (N : ℕ) : (A ^ N * Γ) 2 0 = 0 ↔ N < M ∧ (A ^ N * Γ) 2 0 = 0 :=
  ⟨fun h => ⟨weighted_corner_zeros hp3 hM hA hcls N h, h⟩, And.right⟩

end PerfectPower.WeightedSkolem
