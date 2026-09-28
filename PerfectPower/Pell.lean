import PerfectPower.Examples
import Mathlib.Data.Real.Sqrt

open Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### The Pell example `2n^2 + 1`: infinitely many hits, density zero

The monograph's example separating "infinitely many hits" from "positive density".  This is
the first *nonrigid* polynomial (leading coefficient `2` is not a square) whose density-zero
statement is machine-checked here.  The proof is elementary: every solution of
`m^2 - 2n^2 = 1` with `m, n ≥ 0` lies on the orbit of `(1, 0)` under
`(m, n) ↦ (3m + 4n, 2m + 3n)` (descent), and the orbit grows at least quadratically. -/

/-- A general squeeze: a count bound `A(N) ≤ B(N)` with `B(N)/N → 0` gives density zero. -/
theorem hasDensity_zero_of_count_le {S : ℕ → ℤ} {d : ℕ} {k : ℤ} (B : ℕ → ℝ)
    (hB : ∀ N, (A S d k N : ℝ) ≤ B N) (hlim : Tendsto (fun N : ℕ => B N / N) atTop (𝓝 0)) :
    HasDensity S d k 0 := by
  refine squeeze_zero (fun N => ratio_nonneg S d k N) (fun N => ?_) hlim
  unfold ratio
  exact div_le_div_of_nonneg_right (hB N) (Nat.cast_nonneg N)

/-- The orbit of the fundamental solution `(1, 0)` under `(m, n) ↦ (3m + 4n, 2m + 3n)`. -/
def pellSeq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => (3 * (pellSeq k).1 + 4 * (pellSeq k).2, 2 * (pellSeq k).1 + 3 * (pellSeq k).2)

/-- Invariants of the Pell orbit: norm one, `m_k ≥ 2k+1`, `n_k ≥ k^2`, `n_k ≥ 0`. -/
lemma pellSeq_spec (k : ℕ) :
    (pellSeq k).1 ^ 2 - 2 * (pellSeq k).2 ^ 2 = 1 ∧ 2 * k + 1 ≤ (pellSeq k).1 ∧
      (k : ℤ) ^ 2 ≤ (pellSeq k).2 ∧ 0 ≤ (pellSeq k).2 := by
  induction k with
  | zero => simp [pellSeq]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [pellSeq]
    push_cast
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Descent: every nonnegative solution of `m^2 - 2 n^2 = 1` is on the orbit. -/
theorem pell_descent : ∀ (n : ℕ) (m : ℤ), 0 ≤ m → m ^ 2 - 2 * (n : ℤ) ^ 2 = 1 →
    ∃ k, pellSeq k = (m, (n : ℤ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, ?_⟩
      have h' : (m - 1) * (m + 1) = 0 := by push_cast at h; ring_nf; linarith
      have : m = 1 := by
        rcases mul_eq_zero.mp h' with h1 | h1 <;> omega
      simp [pellSeq, this]
    · have hn2 : 2 ≤ n := by
        by_contra hlt
        have : n = 1 := by omega
        subst this
        have hm3 : m ^ 2 = 3 := by push_cast at h; linarith
        rcases le_or_lt m 1 with h1 | h1
        · nlinarith
        · nlinarith
      -- predecessor (3m - 4n, 3n - 2m)
      have hmn : (n : ℤ) < m := by nlinarith
      have hA : 0 ≤ 3 * m - 4 * n := by nlinarith
      have hB : 0 ≤ 3 * (n : ℤ) - 2 * m := by nlinarith
      have hlt : (3 * (n : ℤ) - 2 * m).toNat < n := by omega
      obtain ⟨k, hk⟩ := ih _ hlt (3 * m - 4 * n) hA (by
        rw [Int.toNat_of_nonneg hB]; nlinarith)
      refine ⟨k + 1, ?_⟩
      simp only [pellSeq, hk, Int.toNat_of_nonneg hB]
      ext <;> simp <;> ring

/-- Hits of `2n^2 + 1` (squares) are exactly the orbit values `n_k`, `k ≥ 1`. -/
theorem pell_hit_iff (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (2 * (n : ℤ) ^ 2 + 1) ↔ ∃ k, 1 ≤ k ∧ (pellSeq k).2 = n := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := pell_descent n |m| (abs_nonneg m) (by rw [sq_abs]; linarith)
    refine ⟨k, ?_, by rw [hk]⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [pellSeq] at hk; omega
    · exact h
  · rintro ⟨k, _, hk⟩
    obtain ⟨h1, -, -, -⟩ := pellSeq_spec k
    exact ⟨(pellSeq k).1, by rw [← hk]; linarith⟩

/-- **Infinitely many hits.** -/
theorem pell_hitSet_infinite :
    (hitSet (fun n => 2 * (n : ℤ) ^ 2 + 1) 2 0).Infinite := by
  have hmono : StrictMono (fun k => (pellSeq (k + 1)).2.toNat) := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨-, h2, -, h4⟩ := pellSeq_spec (k + 1)
    show (pellSeq (k + 1)).2.toNat < (pellSeq (k + 1 + 1)).2.toNat
    simp only [pellSeq] at h2 h4 ⊢
    omega
  refine Set.infinite_of_injective_forall_mem hmono.injective fun k => ?_
  obtain ⟨-, -, h3, h4⟩ := pellSeq_spec (k + 1)
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hpos : 1 ≤ (pellSeq (k + 1)).2 := by push_cast at h3; nlinarith
  refine ⟨by omega, ?_⟩
  simp only [add_zero]
  have := (pell_hit_iff (pellSeq (k + 1)).2.toNat (by omega)).mpr
    ⟨k + 1, by omega, by rw [Int.toNat_of_nonneg h4]⟩
  simpa using this

/-- The count is at most `√N`: the `k`-th hit is at least `k^2`. -/
theorem pell_count_le (N : ℕ) :
    A (fun n => 2 * (n : ℤ) ^ 2 + 1) 2 0 N ≤ Nat.sqrt N := by
  unfold A
  calc _ ≤ ((Finset.Icc 1 (Nat.sqrt N)).image (fun k => (pellSeq k).2.toNat)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc, add_zero] at hn
        obtain ⟨k, hk1, hk⟩ := (pell_hit_iff n hn.1.1).mp hn.2
        simp only [Finset.mem_image, Finset.mem_Icc]
        refine ⟨k, ⟨hk1, ?_⟩, by rw [hk]; simp⟩
        obtain ⟨-, -, h3, -⟩ := pellSeq_spec k
        rw [hk] at h3
        have : k * k ≤ N := by
          have : ((k * k : ℕ) : ℤ) ≤ (N : ℤ) := by push_cast; nlinarith [hn.1.2]
          exact_mod_cast this
        exact Nat.le_sqrt.mpr this
    _ ≤ (Finset.Icc 1 (Nat.sqrt N)).card := Finset.card_image_le
    _ = Nat.sqrt N := by simp

/-- **Density zero** for the Pell example, despite infinitely many hits. -/
theorem pell_hasDensity_zero : HasDensity (fun n => 2 * (n : ℤ) ^ 2 + 1) 2 0 0 := by
  refine hasDensity_zero_of_count_le (fun N => Real.sqrt N) (fun N => ?_) ?_
  · have h1 := pell_count_le N
    have h2 : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    exact le_trans (by exact_mod_cast h1) h2
  · -- √N / N = 1 / √N → 0
    have hsq : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b => ⟨⌈b⌉₊ ^ 2, fun a ha => ?_⟩
      have hle : ((⌈b⌉₊ : ℝ)) ^ 2 ≤ (a : ℝ) := by exact_mod_cast ha
      calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
        _ = Real.sqrt (((⌈b⌉₊ : ℝ)) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
        _ ≤ Real.sqrt a := Real.sqrt_le_sqrt hle
    refine (tendsto_inv_atTop_zero.comp hsq).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp]
    field_simp

end PerfectPower
