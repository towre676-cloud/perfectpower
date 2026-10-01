import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Powers from a projector certificate

A corrected form of an idea in old notes (`docs/ARCHIVE_SALVAGE.md`).  Singular values alone say
nothing about powers: `[[0, 1], [0, 0]]` has singular values `1, 0` and square `0`.  What does
determine the powers is a **projector certificate**: `P² = P`, `MP = PM = P`.  Then `T = M − P`
satisfies `PT = TP = 0`, and

`Mᵏ = P + (M − P)ᵏ` for `k ≥ 1` (`pow_eq_of_projector`, in any ring).

In a normed ring, `‖Mᵏ − P‖ ≤ ‖M − P‖ᵏ` (`norm_pow_sub_le`), so a checked bound `‖M − P‖ ≤ ρ < 1`
gives geometric convergence `Mᵏ → P` with an explicit error (`norm_pow_sub_le_of`).  The projector
may be oblique (`P ≠ Pᵀ`).  The exact rational checker is `python/perfectpower/power_certificate.py`.
-/

namespace PerfectPower.PowerCertificate

variable {R : Type*}

/-- **The power decomposition**: `P² = P`, `MP = PM = P` give `Mᵏ = P + (M − P)ᵏ` for `k ≥ 1`. -/
theorem pow_eq_of_projector [Ring R] {M P : R} (hP : P * P = P) (hMP : M * P = P)
    (hPM : P * M = P) {k : ℕ} (hk : 1 ≤ k) : M ^ k = P + (M - P) ^ k := by
  have hTP : (M - P) * P = 0 := by rw [sub_mul, hMP, hP, sub_self]
  have hPT : P * (M - P) = 0 := by rw [mul_sub, hPM, hP, sub_self]
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hTnP : (M - P) ^ n * P = 0 := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hTP, mul_zero]
    calc M ^ (n + 1) = M ^ n * M := pow_succ _ _
      _ = (P + (M - P) ^ n) * (P + (M - P)) := by rw [ih, add_sub_cancel]
      _ = P * P + P * (M - P) + ((M - P) ^ n * P + (M - P) ^ n * (M - P)) := by
          rw [add_mul, mul_add, mul_add]
      _ = P + (M - P) ^ (n + 1) := by rw [hP, hPT, hTnP, ← pow_succ]; abel

/-- **The error bound**: `‖Mᵏ − P‖ ≤ ‖M − P‖ᵏ` for `k ≥ 1`. -/
theorem norm_pow_sub_le [NormedRing R] {M P : R} (hP : P * P = P) (hMP : M * P = P)
    (hPM : P * M = P) {k : ℕ} (hk : 1 ≤ k) : ‖M ^ k - P‖ ≤ ‖M - P‖ ^ k := by
  rw [pow_eq_of_projector hP hMP hPM hk, add_sub_cancel_left]
  exact norm_pow_le' _ (by omega)

/-- With a checked bound `‖M − P‖ ≤ ρ`: `‖Mᵏ − P‖ ≤ ρᵏ`. -/
theorem norm_pow_sub_le_of [NormedRing R] {M P : R} {ρ : ℝ} (hP : P * P = P) (hMP : M * P = P)
    (hPM : P * M = P) (hρ : ‖M - P‖ ≤ ρ) {k : ℕ} (hk : 1 ≤ k) : ‖M ^ k - P‖ ≤ ρ ^ k :=
  (norm_pow_sub_le hP hMP hPM hk).trans (pow_le_pow_left₀ (norm_nonneg _) hρ k)

end PerfectPower.PowerCertificate
