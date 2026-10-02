import Batteries.Tactic.Lint.Misc
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# An integer Skolem lemma at an odd prime

Let `p` be an odd prime.  If `x₀ = 0` and `p ∤ x₁`, then for every `m ≥ 1`
`Σ_{k=0}^{m} C(m, k) pᵏ xₖ ≠ 0`: with `e = v_p(m)`, the `k = 1` term has valuation exactly
`e + 1`, and every term with `k ≥ 2` is divisible by `p^{e+2}` (`k C(m, k) = m C(m − 1, k − 1)`
and `k − v_p(k) ≥ 2`).

**Matrix form** (`corner_zero`).  If `A^M = 1 + pD` with `p ∤ D₂₀` and `p ∤ (A^r)₂₀` for
`0 < r < M`, then `(A^N)₂₀ = 0` only for `N = 0`.  This generalizes `Skolem3` (`p = 3`, `M = 3`)
and needs no `p`-adic analysis and no exponent bound.
-/

namespace PerfectPower.SkolemP

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- `v_p(k) + 2 ≤ k` for `k ≥ 2` and `p ≥ 3`. -/
lemma vk_le (hp3 : 3 ≤ p) (k : ℕ) (hk : 2 ≤ k) : padicValNat p k + 2 ≤ k := by
  set t := padicValNat p k
  have hpow : p ^ t ∣ k := pow_padicValNat_dvd
  have hle : p ^ t ≤ k := Nat.le_of_dvd (by omega) hpow
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]; omega
  · have key : ∀ s : ℕ, 1 ≤ s → s + 2 ≤ p ^ s := by
      intro s hs
      induction s with
      | zero => omega
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simpa using hp3
        · have := ih hn
          rw [pow_succ]
          nlinarith
    have := key t hpos
    omega

/-- `p^{e+2} ∣ C(m, k) pᵏ` for `2 ≤ k ≤ m` and `pᵉ ∣ m`. -/
lemma dvd_term (hp3 : 3 ≤ p) (m k e : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) (he : p ^ e ∣ m) :
    p ^ (e + 2) ∣ Nat.choose m k * p ^ k := by
  have hc : 0 < Nat.choose m k := Nat.choose_pos hkm
  have hkey : k * Nat.choose m k = m * Nat.choose (m - 1) (k - 1) := by
    have := Nat.succ_mul_choose_eq (m - 1) (k - 1)
    simp only [Nat.succ_eq_add_one] at this
    rw [show m - 1 + 1 = m by omega, show k - 1 + 1 = k by omega] at this
    linarith [this, mul_comm (Nat.choose m k) k]
  have h1 : p ^ e ∣ k * Nat.choose m k := by rw [hkey]; exact Dvd.dvd.mul_right he _
  have hv : e ≤ padicValNat p k + padicValNat p (Nat.choose m k) := by
    have hne : k * Nat.choose m k ≠ 0 := by positivity
    have := (padicValNat_dvd_iff_le (p := p) hne).mp h1
    rwa [padicValNat.mul (by omega) hc.ne'] at this
  have hvk := vk_le hp3 k hk
  have hne2 : Nat.choose m k * p ^ k ≠ 0 := by positivity
  rw [padicValNat_dvd_iff_le hne2, padicValNat.mul hc.ne' (by positivity), padicValNat.prime_pow]
  omega

/-- The linear term has valuation exactly `e + 1`. -/
lemma not_dvd_lin (m x : ℕ) (hm : 0 < m) (hx : ¬ p ∣ x) :
    ¬ p ^ (padicValNat p m + 2) ∣ m * p * x := by
  intro h
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (dvd_zero _)
  have hne : m * p * x ≠ 0 := by positivity
  rw [padicValNat_dvd_iff_le hne, padicValNat.mul (by positivity) hx0,
    padicValNat.mul (by omega) hp0] at h
  have : padicValNat p x = 0 := padicValNat.eq_zero_of_not_dvd hx
  have hpp : padicValNat p p = 1 := padicValNat_self
  omega

/-- **The Skolem lemma at an odd prime.** -/
theorem sum_ne_zero (hp3 : 3 ≤ p) (m : ℕ) (hm : 0 < m) (x : ℕ → ℤ) (h0 : x 0 = 0)
    (h1 : ¬ (p : ℤ) ∣ x 1) :
    (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℤ) * (p : ℤ) ^ k * x k) ≠ 0 := by
  set e := padicValNat p m
  have he : p ^ e ∣ m := pow_padicValNat_dvd
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one, one_mul, h0,
    mul_zero, add_zero]
  set R := ∑ k ∈ Finset.range n, ((n + 1).choose (k + 1 + 1) : ℤ) * (p : ℤ) ^ (k + 1 + 1) * x (k + 1 + 1)
  have hR : (p : ℤ) ^ (e + 2) ∣ R := by
    apply Finset.dvd_sum
    intro k hk
    simp only [Finset.mem_range] at hk
    apply Dvd.dvd.mul_right
    have := dvd_term hp3 (n + 1) (k + 1 + 1) e (by omega) (by omega) he
    exact_mod_cast this
  intro hsum
  have hlin : (p : ℤ) ^ (e + 2) ∣ ((n + 1 : ℕ) : ℤ) * p * x 1 := by
    have : ((n + 1 : ℕ) : ℤ) * p * x 1 = -R := by
      rw [Nat.choose_one_right] at hsum; push_cast at hsum ⊢; linarith
    rw [this]; exact (dvd_neg).mpr hR
  have hx' : ¬ p ∣ (x 1).natAbs := by
    intro hd; apply h1; exact Int.natCast_dvd.mpr hd
  apply not_dvd_lin (n + 1) (x 1).natAbs (by omega) hx'
  have := Int.natAbs_dvd_natAbs.mpr hlin
  simpa [Int.natAbs_mul, Int.natAbs_pow] using this

open Matrix

/-- `(1 + pD)^m = 1 + pW` for an integer matrix `W`. -/
lemma one_add_pow (p : ℕ) (D : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ) :
    ∃ W : Matrix (Fin 3) (Fin 3) ℤ, (1 + p • D) ^ m = 1 + p • W := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨W + D + p • (W * D), ?_⟩
    rw [pow_succ, hW]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

/-- The binomial expansion of the corner entry: `((1 + pD)^m)₂₀ = Σ C(m, k) pᵏ (Dᵏ)₂₀`. -/
lemma corner_pow (p : ℕ) (D : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ) :
    ((1 + p • D : Matrix (Fin 3) (Fin 3) ℤ) ^ m) 2 0 =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℤ) * (p : ℤ) ^ k * (D ^ k) 2 0 := by
  rw [show (1 + p • D : Matrix (Fin 3) (Fin 3) ℤ) = p • D + 1 from add_comm _ _,
    (Commute.one_right (p • D)).add_pow]
  simp only [one_pow, mul_one, smul_pow, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (Nat.cast_commute _ _).eq, ← nsmul_eq_mul, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul,
    nsmul_eq_mul]
  push_cast
  ring

/-- **The zero set of a corner entry of matrix powers, at an odd prime.**  If `A^M = 1 + pD`
with `p ∤ D₂₀`, and `p ∤ (A^r)₂₀` for `0 < r < M`, then `(A^N)₂₀ = 0` only for `N = 0`. -/
theorem corner_zero (hp3 : 3 ≤ p) {M : ℕ} (hM : 0 < M) {A D : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : A ^ M = 1 + p • D) (hD : ¬ (p : ℤ) ∣ D 2 0)
    (hr : ∀ r, 0 < r → r < M → ¬ (p : ℤ) ∣ (A ^ r) 2 0) (N : ℕ) (hN : (A ^ N) 2 0 = 0) : N = 0 := by
  obtain ⟨m, r, hrM, rfl⟩ : ∃ m r, r < M ∧ N = M * m + r :=
    ⟨N / M, N % M, Nat.mod_lt _ hM, (Nat.div_add_mod N M).symm⟩
  rw [pow_add, pow_mul, hA] at hN
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    simp only [pow_zero, mul_one] at hN
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · exfalso
      rw [corner_pow] at hN
      exact sum_ne_zero hp3 m hm (fun k => (D ^ k) 2 0) (by simp) (by simpa using hD) hN
  · exfalso
    obtain ⟨W, hW⟩ := one_add_pow p D m
    rw [hW, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at hN
    exact hr r hpos hrM ⟨-((W * A ^ r) 2 0), by linarith⟩

end PerfectPower.SkolemP
