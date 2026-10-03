import PerfectPower.SkolemP

/-!
# Finitely many zeros of a corner entry of matrix powers

`SkolemP.corner_zero` shows that `(A^N)₂₀` vanishes only at `N = 0`.  When the zero set has
several points this module proves the finite list instead.  Let `A^M = 1 + pD` at an odd prime `p`.
Every residue class `r < M` must pass one of two exact tests:
* `p ∤ (A^r)₂₀`: the class has no zero (all `(A^{Mm + r})₂₀ ≡ (A^r)₂₀ mod p`);
* `(A^r)₂₀ = 0` and `p ∤ (D A^r)₂₀`: the class has the single zero `N = r` (`SkolemP.sum_ne_zero`,
  recentred at the known root).
Then `(A^N)₂₀ = 0 ↔ N < M ∧ (A^N)₂₀ = 0`, a decidable statement (`corner_zeros`).  A class
failing both tests (a vanishing first-order term) is not covered.  Choosing `M` as a multiple
`tM₀` with `p ∤ t` puts every known root below `M`; the tests are kernel computations.
-/

namespace PerfectPower.SkolemZeros

open Matrix SkolemP

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- `((1 + pD)^m B)₂₀ = Σ C(m, k) pᵏ (Dᵏ B)₂₀`. -/
lemma corner_pow_mul (p : ℕ) (D B : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ) :
    (((1 + p • D : Matrix (Fin 3) (Fin 3) ℤ) ^ m) * B) 2 0 =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℤ) * (p : ℤ) ^ k * (D ^ k * B) 2 0 := by
  rw [show (1 + p • D : Matrix (Fin 3) (Fin 3) ℤ) = p • D + 1 from add_comm _ _,
    (Commute.one_right (p • D)).add_pow, Finset.sum_mul, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_pow, mul_one, smul_pow]
  rw [← (Nat.cast_commute _ _).eq, Matrix.mul_assoc, ← nsmul_eq_mul, smul_mul_assoc, Matrix.smul_apply,
    Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- **The finite zero set.**  Under the per-class tests, every zero of `(A^N)₂₀` lies below `M`. -/
theorem corner_zeros (hp3 : 3 ≤ p) {M : ℕ} (hM : 0 < M) {A D : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : A ^ M = 1 + p • D)
    (hcls : ∀ r, r < M → ¬ (p : ℤ) ∣ (A ^ r) 2 0 ∨ ((A ^ r) 2 0 = 0 ∧ ¬ (p : ℤ) ∣ (D * A ^ r) 2 0))
    (N : ℕ) (hN : (A ^ N) 2 0 = 0) : N < M := by
  obtain ⟨m, r, hrM, rfl⟩ : ∃ m r, r < M ∧ N = M * m + r :=
    ⟨N / M, N % M, Nat.mod_lt _ hM, (Nat.div_add_mod N M).symm⟩
  rw [pow_add, pow_mul, hA] at hN
  rcases hcls r hrM with hnd | ⟨h0, h1⟩
  · exfalso
    obtain ⟨W, hW⟩ := one_add_pow p D m
    rw [hW, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at hN
    exact hnd ⟨-((W * A ^ r) 2 0), by linarith⟩
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using hrM
    · exfalso
      rw [corner_pow_mul] at hN
      exact sum_ne_zero hp3 m hm (fun k => (D ^ k * A ^ r) 2 0) (by simpa using h0) (by simpa using h1) hN

/-- The same as an `iff` with a decidable right side. -/
theorem corner_zeros_iff (hp3 : 3 ≤ p) {M : ℕ} (hM : 0 < M) {A D : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : A ^ M = 1 + p • D)
    (hcls : ∀ r, r < M → ¬ (p : ℤ) ∣ (A ^ r) 2 0 ∨ ((A ^ r) 2 0 = 0 ∧ ¬ (p : ℤ) ∣ (D * A ^ r) 2 0))
    (N : ℕ) : (A ^ N) 2 0 = 0 ↔ N < M ∧ (A ^ N) 2 0 = 0 :=
  ⟨fun h => ⟨corner_zeros hp3 hM hA hcls N h, h⟩, And.right⟩

end PerfectPower.SkolemZeros
