import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# A 3-adic Skolem lemma, by integer valuations only

If `x₀ = 0` and `3 ∤ x₁`, then for every `m ≥ 1`
`Σ_{k=0}^{m} C(m, k) 3ᵏ xₖ ≠ 0`.

With `e = v₃(m)`: the `k = 1` term `3 m x₁` has valuation exactly `e + 1`, and every term with
`k ≥ 2` is divisible by `3^{e+2}`, because `k C(m, k) = m C(m − 1, k − 1)` gives
`v₃(C(m, k)) ≥ e − v₃(k)` and `k − v₃(k) ≥ 2`.  This is the zero-set step of Skolem's method for a
power `(1 + 3A)^m` with no `p`-adic analysis (`Plus2.lean`).
-/

namespace PerfectPower.Skolem3

/-- `t + 2 ≤ 3ᵗ` fails only at `t = 0`... used as: `v₃(k) + 2 ≤ k` for `k ≥ 2`. -/
lemma vk_le (k : ℕ) (hk : 2 ≤ k) : padicValNat 3 k + 2 ≤ k := by
  have hk0 : k ≠ 0 := by omega
  set t := padicValNat 3 k
  have hpow : 3 ^ t ∣ k := pow_padicValNat_dvd
  have hle : 3 ^ t ≤ k := Nat.le_of_dvd (by omega) hpow
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]; omega
  · have : t + 2 ≤ 3 ^ t := by
      have key : ∀ s : ℕ, 1 ≤ s → s + 2 ≤ 3 ^ s := by
        intro s hs
        induction s with
        | zero => omega
        | succ n ih =>
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn; norm_num
          · have := ih hn; rw [pow_succ]; omega
      exact key t hpos
    omega

/-- **`3^{e+2} ∣ C(m, k) 3ᵏ`** for `2 ≤ k ≤ m` and `3ᵉ ∣ m`. -/
lemma dvd_term (m k e : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) (he : 3 ^ e ∣ m) :
    3 ^ (e + 2) ∣ Nat.choose m k * 3 ^ k := by
  have hc : 0 < Nat.choose m k := Nat.choose_pos hkm
  have hkey : k * Nat.choose m k = m * Nat.choose (m - 1) (k - 1) := by
    have := Nat.succ_mul_choose_eq (m - 1) (k - 1)
    simp only [Nat.succ_eq_add_one] at this
    rw [show m - 1 + 1 = m by omega, show k - 1 + 1 = k by omega] at this
    linarith [this, mul_comm (Nat.choose m k) k]
  -- v₃(k) + v₃(C) ≥ e
  have h1 : 3 ^ e ∣ k * Nat.choose m k := by rw [hkey]; exact Dvd.dvd.mul_right he _
  have hv : e ≤ padicValNat 3 k + padicValNat 3 (Nat.choose m k) := by
    have hne : k * Nat.choose m k ≠ 0 := by positivity
    have := (padicValNat_dvd_iff_le (p := 3) hne).mp h1
    rwa [padicValNat.mul (by omega) hc.ne'] at this
  have hvk := vk_le k hk
  have hne2 : Nat.choose m k * 3 ^ k ≠ 0 := by positivity
  rw [padicValNat_dvd_iff_le hne2, padicValNat.mul hc.ne' (by positivity), padicValNat.prime_pow]
  omega

/-- The valuation of the linear term is exactly `e + 1`. -/
lemma not_dvd_lin (m x : ℕ) (hm : 0 < m) (hx : ¬ 3 ∣ x) :
    ¬ 3 ^ (padicValNat 3 m + 2) ∣ m * 3 * x := by
  intro h
  have hne : m * 3 * x ≠ 0 := by
    have : x ≠ 0 := by rintro rfl; exact hx (dvd_zero _)
    positivity
  rw [padicValNat_dvd_iff_le hne, padicValNat.mul (by positivity) (by rintro rfl; exact hx (dvd_zero _)),
    padicValNat.mul (by omega) (by norm_num)] at h
  have : padicValNat 3 x = 0 := padicValNat.eq_zero_of_not_dvd hx
  have h3 : padicValNat 3 3 = 1 := by simp
  omega

/-- **The Skolem lemma.** -/
theorem sum_ne_zero (m : ℕ) (hm : 0 < m) (x : ℕ → ℤ) (h0 : x 0 = 0) (h1 : ¬ (3 : ℤ) ∣ x 1) :
    (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℤ) * 3 ^ k * x k) ≠ 0 := by
  set e := padicValNat 3 m
  have he : 3 ^ e ∣ m := pow_padicValNat_dvd
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one, one_mul, h0,
    mul_zero, add_zero]
  set R := ∑ k ∈ Finset.range n, ((n + 1).choose (k + 1 + 1) : ℤ) * 3 ^ (k + 1 + 1) * x (k + 1 + 1)
  have hR : (3 : ℤ) ^ (e + 2) ∣ R := by
    apply Finset.dvd_sum
    intro k hk
    simp only [Finset.mem_range] at hk
    apply Dvd.dvd.mul_right
    have := dvd_term (n + 1) (k + 1 + 1) e (by omega) (by omega) he
    exact_mod_cast this
  intro hsum
  have hlin : (3 : ℤ) ^ (e + 2) ∣ ((n + 1 : ℕ) : ℤ) * 3 * x 1 := by
    have : ((n + 1 : ℕ) : ℤ) * 3 * x 1 = -R := by
      rw [Nat.choose_one_right] at hsum; push_cast at hsum ⊢; linarith
    rw [this]; exact (dvd_neg).mpr hR
  have hx' : ¬ 3 ∣ (x 1).natAbs := by
    intro hd; apply h1; exact Int.natAbs_dvd_natAbs.mp (by simpa using hd)
  apply not_dvd_lin (n + 1) (x 1).natAbs (by omega) hx'
  have := Int.natAbs_dvd_natAbs.mpr hlin
  simpa [Int.natAbs_mul, Int.natAbs_pow] using this

end PerfectPower.Skolem3
