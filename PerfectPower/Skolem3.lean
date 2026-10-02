import Batteries.Tactic.Lint.Misc
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
@[nolint unusedHavesSuffices]
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

namespace PerfectPower.Skolem3

open Matrix

/-- `(1 + 3D)^m = 1 + 3W` for an integer matrix `W`. -/
lemma one_add_three_pow (D : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ) :
    ∃ W : Matrix (Fin 3) (Fin 3) ℤ, (1 + 3 • D) ^ m = 1 + 3 • W := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨W + D + 3 • (W * D), ?_⟩
    rw [pow_succ, hW]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

/-- The binomial expansion of the corner entry: `((1 + 3D)^m)₂₀ = Σ C(m, k) 3ᵏ (Dᵏ)₂₀`. -/
lemma corner_pow (D : Matrix (Fin 3) (Fin 3) ℤ) (m : ℕ) :
    ((1 + 3 • D : Matrix (Fin 3) (Fin 3) ℤ) ^ m) 2 0 =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℤ) * 3 ^ k * (D ^ k) 2 0 := by
  rw [show (1 + 3 • D : Matrix (Fin 3) (Fin 3) ℤ) = 3 • D + 1 from add_comm _ _,
    (Commute.one_right (3 • D)).add_pow]
  simp only [one_pow, mul_one, smul_pow, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (Nat.cast_commute _ _).eq, ← nsmul_eq_mul, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul,
    nsmul_eq_mul]
  push_cast
  ring

/-- **The zero set of a corner entry of matrix powers.**  If `A³ = 1 + 3D` with `3 ∤ D₂₀`, and
`3 ∤ A₂₀`, `3 ∤ (A²)₂₀`, then `(A^N)₂₀ = 0` only for `N = 0`. -/
theorem corner_zero {A D : Matrix (Fin 3) (Fin 3) ℤ} (hA : A ^ 3 = 1 + 3 • D) (hD : ¬ (3 : ℤ) ∣ D 2 0)
    (h1 : ¬ (3 : ℤ) ∣ A 2 0) (h2 : ¬ (3 : ℤ) ∣ (A ^ 2) 2 0) (N : ℕ) (hN : (A ^ N) 2 0 = 0) : N = 0 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ N = 3 * m + r := ⟨N / 3, N % 3, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod N 3).symm⟩
  rw [pow_add, pow_mul, hA] at hN
  interval_cases r
  · -- r = 0: Skolem
    simp only [pow_zero, mul_one] at hN
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · exfalso
      rw [corner_pow] at hN
      exact sum_ne_zero m hm (fun k => (D ^ k) 2 0) (by simp) (by simpa using hD) hN
  all_goals
    exfalso
    obtain ⟨W, hW⟩ := one_add_three_pow D m
    rw [hW, add_mul, one_mul, smul_mul_assoc, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at hN
    try simp only [pow_one] at hN
    first
    | exact h1 ⟨-((W * A) 2 0), by push_cast at hN; linarith⟩
    | exact h2 ⟨-((W * A ^ 2) 2 0), by push_cast at hN; linarith⟩

end PerfectPower.Skolem3
