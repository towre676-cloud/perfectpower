import PerfectPower.Basic

open Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### Elementary count facts -/

/-- No indices are counted up to `0`. -/
lemma A_zero (S : ℕ → ℤ) (d : ℕ) (k : ℤ) : A S d k 0 = 0 := by
  simp [A]

/-- Recursion for the count: `A(N+1) = A(N) + [N+1 is a hit]`. -/
lemma A_succ (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (N : ℕ) :
    A S d k (N + 1) = A S d k N + if IsHit d (S (N + 1) + k) then 1 else 0 := by
  unfold A
  have hI : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  by_cases h : IsHit d (S (N + 1) + k)
  · rw [hI, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [hI, Finset.filter_insert, if_neg h, if_neg h, add_zero]

/-- At most `N` of the indices `1..N` are hits. -/
lemma A_le (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (N : ℕ) : A S d k N ≤ N := by
  induction N with
  | zero => simp [A_zero]
  | succ N ih =>
    rw [A_succ]
    split_ifs <;> omega

/-- The density ratio `A(N)/N` is nonnegative. -/
lemma ratio_nonneg (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (N : ℕ) : 0 ≤ ratio S d k N := by
  unfold ratio; positivity

/-- The density ratio `A(N)/N` is at most one. -/
lemma ratio_le_one (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (N : ℕ) : ratio S d k N ≤ 1 := by
  unfold ratio
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast A_le S d k N

/-! ### Finite hit sets -/

/-- A finite hit set has bounded count, hence density zero. -/
theorem hasDensity_zero_of_finite {S : ℕ → ℤ} {d : ℕ} {k : ℤ}
    (h : (hitSet S d k).Finite) : HasDensity S d k 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ N, A S d k N ≤ B := by
    refine ⟨h.toFinset.card, fun N => ?_⟩
    unfold A
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Set.Finite.mem_toFinset]
    exact ⟨hn.1.1, hn.2⟩
  refine squeeze_zero (fun N => by unfold ratio; positivity)
    (g := fun N : ℕ => (B : ℝ) / N) (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (B : ℝ))
  unfold ratio
  exact div_le_div_of_nonneg_right (by exact_mod_cast hB N) (Nat.cast_nonneg N)

/-! ### Finite surgery -/

/-- If `S` and `S'` agree from `N₀` on, the count difference is a constant `D` for `N ≥ N₀ - 1`. -/
theorem A_sub_eq_const {S S' : ℕ → ℤ} {d : ℕ} {k : ℤ} {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (h : ∀ n, N₀ ≤ n → S n = S' n) :
    ∃ D : ℤ, ∀ N, N₀ - 1 ≤ N → (A S d k N : ℤ) - A S' d k N = D := by
  refine ⟨(A S d k (N₀ - 1) : ℤ) - A S' d k (N₀ - 1), fun N hN => ?_⟩
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [A_succ, A_succ]
    have hs : S (N + 1) = S' (N + 1) := h _ (by omega)
    rw [hs]
    push_cast
    linarith

/-- If bounded-by-`[0,1]` sequences differ by a null sequence, their limsups compare. -/
lemma limsup_le_of_tendsto_sub {u v : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hv1 : ∀ n, v n ≤ 1)
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) : limsup u atTop ≤ limsup v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hbv : IsBoundedUnder (· ≤ ·) atTop v := isBoundedUnder_of ⟨1, hv1⟩
  have hcu : IsCoboundedUnder (· ≤ ·) atTop u :=
    isCoboundedUnder_le_of_le atTop (x := 0) hu0
  have h1 : limsup v atTop < limsup v atTop + ε / 2 := by linarith
  have e1 := eventually_lt_of_limsup_lt h1 hbv
  have e2 : ∀ᶠ n in atTop, u n - v n < ε / 2 := (tendsto_order.1 h).2 _ (by linarith)
  refine limsup_le_of_le hcu ?_
  filter_upwards [e1, e2] with n h1n h2n
  linarith

/-- Surgery for upper density. -/
theorem H_surgery {S S' : ℕ → ℤ} {d : ℕ} {k : ℤ} {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (h : ∀ n, N₀ ≤ n → S n = S' n) : H S d k = H S' d k := by
  obtain ⟨D, hD⟩ := A_sub_eq_const (d := d) (k := k) hN₀ h
  have hdiff : Tendsto (fun n => ratio S d k n - ratio S' d k n) atTop (𝓝 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat (D : ℝ)).congr' ?_
    filter_upwards [eventually_ge_atTop (N₀ - 1)] with N hN
    have := hD N hN
    unfold ratio
    rw [← sub_div]
    congr 1
    exact_mod_cast this.symm
  unfold H
  apply le_antisymm
  · exact limsup_le_of_tendsto_sub (ratio_nonneg S d k) (ratio_le_one S' d k) hdiff
  · refine limsup_le_of_tendsto_sub (ratio_nonneg S' d k) (ratio_le_one S d k) ?_
    have := hdiff.neg
    simpa [neg_sub] using this

/-! ### Periodic indicators -/

/-- For a `T`-periodic hit indicator, `A(N+T) = A(N) + A(T)`. -/
lemma A_add_period {S : ℕ → ℤ} {d : ℕ} {k : ℤ} {T : ℕ}
    (hper : ∀ n, 1 ≤ n → (IsHit d (S (n + T) + k) ↔ IsHit d (S n + k))) (N : ℕ) :
    A S d k (N + T) = A S d k N + A S d k T := by
  induction N with
  | zero => simp [A_zero]
  | succ N ih =>
    have e : N + 1 + T = (N + T) + 1 := by omega
    rw [e, A_succ, A_succ, ih]
    have hh : IsHit d (S (N + T + 1) + k) ↔ IsHit d (S (N + 1) + k) := by
      have := hper (N + 1) (by omega)
      rwa [show N + 1 + T = N + T + 1 by omega] at this
    rw [if_congr hh rfl rfl]
    ring

/-- For a `T`-periodic hit indicator, `A(qT + r) = A(r) + q·A(T)`. -/
lemma A_mul_add {S : ℕ → ℤ} {d : ℕ} {k : ℤ} {T : ℕ}
    (hper : ∀ n, 1 ≤ n → (IsHit d (S (n + T) + k) ↔ IsHit d (S n + k))) (q r : ℕ) :
    A S d k (q * T + r) = A S d k r + q * A S d k T := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : (q + 1) * T + r = (q * T + r) + T := by ring
    rw [e, A_add_period hper, ih]
    ring

/-- Periodic indicator: density `P/T`, with `P` the number of hits in one period. -/
theorem hasDensity_of_periodic {S : ℕ → ℤ} {d : ℕ} {k : ℤ} {T : ℕ} (hT : 0 < T)
    (hper : ∀ n, 1 ≤ n → (IsHit d (S (n + T) + k) ↔ IsHit d (S n + k))) :
    ∃ P : ℕ, HasDensity S d k ((P : ℝ) / T) := by
  refine ⟨A S d k T, ?_⟩
  unfold HasDensity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < T ∧ N = q * T + r :=
    ⟨N / T, N % T, Nat.mod_lt _ hT, (Nat.div_add_mod' N T).symm⟩
  have hA := A_mul_add hper q r
  have hAr : (A S d k r : ℝ) ≤ r := by exact_mod_cast A_le S d k r
  have hP : (A S d k T : ℝ) ≤ T := by exact_mod_cast A_le S d k T
  have hNpos : (0 : ℝ) < (q : ℝ) * T + r := by
    have : (1 : ℝ) ≤ ((q * T + r : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at this; linarith
  have hrT : (r : ℝ) ≤ T := by exact_mod_cast hr.le
  unfold ratio
  rw [hA]
  push_cast
  have hdiff : ((A S d k r : ℝ) + q * A S d k T) / (q * T + r) - (A S d k T : ℝ) / T
      = ((A S d k r : ℝ) - r * A S d k T / T) / (q * T + r) := by
    field_simp; ring
  rw [Real.norm_eq_abs, hdiff, abs_div, abs_of_pos hNpos]
  apply div_le_div_of_nonneg_right _ hNpos.le
  have h1 : (0 : ℝ) ≤ r * A S d k T / T := by positivity
  have h2 : (r : ℝ) * A S d k T / T ≤ A S d k T := by
    rw [div_le_iff₀ hTr]; nlinarith
  rw [abs_le]
  constructor <;> linarith

end PerfectPower
