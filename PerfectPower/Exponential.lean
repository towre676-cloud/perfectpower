import PerfectPower.Certificates

open Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### Exponential sequences `c · a^n` (research notes, Theorem E)

The hit indicator of `c · a^n` is periodic with period `d`, so its density exists and is a
rational number `P / d` — in contrast with polynomials, where it is `0` or `1`. -/

/-- `c a^(n+d)` is a `d`-th power iff `c a^n` is (for `a ≠ 0`). -/
lemma isHit_exp_shift {d : ℕ} (hd : d ≠ 0) {a c : ℤ} (ha : a ≠ 0) (n : ℕ) :
    IsHit d (c * a ^ (n + d)) ↔ IsHit d (c * a ^ n) := by
  constructor
  · rintro ⟨M, hM⟩
    have hdvd : a ^ d ∣ M ^ d := ⟨c * a ^ n, by rw [← hM]; ring⟩
    obtain ⟨b, rfl⟩ := (Int.pow_dvd_pow_iff hd).mp hdvd
    refine ⟨b, ?_⟩
    have had : a ^ d ≠ 0 := pow_ne_zero d ha
    apply mul_left_cancel₀ had
    calc a ^ d * (c * a ^ n) = c * a ^ (n + d) := by ring
      _ = (a * b) ^ d := hM
      _ = a ^ d * b ^ d := by ring
  · rintro ⟨m, hm⟩
    exact ⟨m * a, by rw [pow_add, ← mul_assoc, hm, mul_pow]⟩

/-- **Theorem E (formal core).** For `a ≠ 0`, the hit density of `c · a^n` exists and equals
`P / d` for some natural number `P` (the number of hits in one period). -/
theorem exp_hasDensity {d : ℕ} (hd : 0 < d) (a c : ℤ) (ha : a ≠ 0) :
    ∃ P : ℕ, HasDensity (fun n => c * a ^ n) d 0 ((P : ℝ) / d) :=
  hasDensity_of_periodic hd fun n _ => by
    simpa using isHit_exp_shift (by omega) ha n

/-- Example: `2^n` is a square for exactly half of all `n`. -/
theorem two_pow_hasDensity_half : HasDensity (fun n => (1 : ℤ) * 2 ^ n) 2 0 (1 / 2) := by
  have hper : ∀ n, 1 ≤ n → (IsHit 2 ((fun n => (1 : ℤ) * 2 ^ n) (n + 2) + 0) ↔
      IsHit 2 ((fun n => (1 : ℤ) * 2 ^ n) n + 0)) := fun n _ => by
    simpa using isHit_exp_shift (d := 2) (c := 1) (by norm_num) (by norm_num : (2 : ℤ) ≠ 0) n
  have hA : A (fun n => (1 : ℤ) * 2 ^ n) 2 0 2 = 1 := by
    rw [A_succ, A_succ, A_zero]
    have h1 : ¬ IsHit 2 ((1 : ℤ) * 2 ^ (0 + 1) + 0) :=
      not_isHit_between (a := 1) (by norm_num) (by norm_num) (by norm_num)
    have h2 : IsHit 2 ((1 : ℤ) * 2 ^ (1 + 1) + 0) := ⟨2, by norm_num⟩
    rw [if_neg h1, if_pos h2]
  -- rerun the periodic argument with the explicit period count
  unfold HasDensity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ N = q * 2 + r :=
    ⟨N / 2, N % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod' N 2).symm⟩
  have hAq := A_mul_add (S := fun n => (1 : ℤ) * 2 ^ n) (d := 2) (k := 0) (T := 2) hper q r
  rw [hA] at hAq
  have hNpos : (0 : ℝ) < (q : ℝ) * 2 + r := by
    have : (1 : ℝ) ≤ ((q * 2 + r : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at this; linarith
  have hAr : (A (fun n => (1 : ℤ) * 2 ^ n) 2 0 r : ℝ) ≤ r := by
    exact_mod_cast A_le _ 2 0 r
  have hr' : (r : ℝ) ≤ 1 := by
    have : r ≤ 1 := by omega
    exact_mod_cast this
  unfold ratio
  rw [hAq]
  push_cast
  set X : ℝ := (A (fun n => (1 : ℤ) * 2 ^ n) 2 0 r : ℝ)
  have h0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have key : (X + q * 1) / (q * 2 + r) - 1 / 2 = (2 * X - r) / (2 * (q * 2 + r)) := by
    field_simp; ring
  rw [Real.norm_eq_abs, key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (q * 2 + r))]
  have hnum : |2 * X - r| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  calc |2 * X - r| / (2 * (q * 2 + r)) ≤ 2 / (2 * (q * 2 + r)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 2 / (q * 2 + r) := div_le_div_of_nonneg_left (by norm_num) hNpos (by linarith)

end PerfectPower
