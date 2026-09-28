import PerfectPower.RadicalValuation
import Mathlib.Data.Nat.Count

namespace PerfectPower

open Finset
open scoped Classical

/-! ### Counting the radical type (research notes, Theorem B)

After the reduction of Theorem B, the hits `n ≤ N` of `c (v n - u)^r` are the `n` with
`v n - u = z₀ w^t`.  This file proves

* `radical_hits_card`: the hits `n ∈ [1, N]` (with `v n > u`) are in bijection with the
  `w ∈ [1, W]` satisfying the congruence `v ∣ z₀ w^t + u`, where `W` is the largest `w` with
  `z₀ w^t + u ≤ v N`;
* `count_periodic_le` / `le_count_periodic`: a `q`-periodic predicate with `R` solutions per period
  has `R W / q + O(R)` solutions below `W`;
* `radical_count_bound`: together, `|v · A(N) - R · W| ≤ 2 R v`.

Since `W = ⌊((v N - u)/z₀)^{1/t}⌋`, this is `A(N) = (R/v) (v/z₀)^{1/t} N^{1/t} + O(1)`: the
constant `κ` of Theorem B, with `R` the number of good residues of `w` modulo `v`.  The final
step, from `W` to the real power `N^{1/t}`, is not formalised. -/

/-- Shifting a periodic count by whole periods. -/
lemma count_periodic_eq {p : ℕ → Prop} [DecidablePred p] {q : ℕ} (hper : ∀ w, p (w + q) ↔ p w)
    (a b : ℕ) : Nat.count p (q * a + b) = a * Nat.count p q + Nat.count p b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show q * (a + 1) + b = q + (q * a + b) by ring, Nat.count_add]
    have : Nat.count (fun k => p (q + k)) (q * a + b) = Nat.count p (q * a + b) := by
      simp only [Nat.count_eq_card_filter_range]
      exact congrArg _ (filter_congr fun k _ => by rw [add_comm]; exact hper k)
    rw [this, ih]
    ring

/-- **Periodic count, upper bound.** -/
theorem count_periodic_le {p : ℕ → Prop} [DecidablePred p] {q : ℕ} (hq : 0 < q)
    (hper : ∀ w, p (w + q) ↔ p w) (W : ℕ) :
    q * Nat.count p W ≤ Nat.count p q * W + q * Nat.count p q := by
  have hW := Nat.div_add_mod W q
  have h := count_periodic_eq hper (W / q) (W % q)
  rw [hW] at h
  have hb : Nat.count p (W % q) ≤ Nat.count p q :=
    Nat.count_monotone p (Nat.mod_lt W hq).le
  rw [h]
  calc q * (W / q * Nat.count p q + Nat.count p (W % q))
      ≤ q * (W / q) * Nat.count p q + q * Nat.count p q := by nlinarith
    _ ≤ Nat.count p q * W + q * Nat.count p q := by
      have : q * (W / q) ≤ W := Nat.mul_div_le W q
      nlinarith

/-- **Periodic count, lower bound.** -/
theorem le_count_periodic {p : ℕ → Prop} [DecidablePred p] {q : ℕ} (hq : 0 < q)
    (hper : ∀ w, p (w + q) ↔ p w) (W : ℕ) :
    Nat.count p q * W ≤ q * Nat.count p W + q * Nat.count p q := by
  have hW := Nat.div_add_mod W q
  have h := count_periodic_eq hper (W / q) (W % q)
  rw [hW] at h
  rw [h]
  have hm : W % q < q := Nat.mod_lt W hq
  calc Nat.count p q * W = Nat.count p q * (q * (W / q)) + Nat.count p q * (W % q) := by
        conv_lhs => rw [← hW]
        ring
    _ ≤ q * (W / q * Nat.count p q + Nat.count p (W % q)) + q * Nat.count p q := by
        nlinarith [Nat.zero_le (Nat.count p (W % q))]

/-- `#{w ∈ [1, W] | p w}` as a `Nat.count` of the shifted predicate. -/
lemma card_Icc_filter_eq_count (p : ℕ → Prop) [DecidablePred p] (W : ℕ) :
    #{w ∈ Icc 1 W | p w} = Nat.count (fun k => p (k + 1)) W := by
  rw [Nat.count_eq_card_filter_range]
  refine card_nbij' (fun w => w - 1) (fun k => k + 1) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_Icc, mem_range] at hw ⊢
    refine ⟨by omega, by rw [Nat.sub_add_cancel hw.1.1]; exact hw.2⟩
  · intro k hk
    simp only [mem_filter, mem_Icc, mem_range] at hk ⊢
    exact ⟨⟨by omega, by omega⟩, hk.2⟩
  · intro w hw
    simp only [mem_filter, mem_Icc] at hw
    simp only; omega
  · intro k _; simp

/-- **Bijection with the `w`-parameters.**  Under the hypotheses of `mul_pow_isPow_iff_param`
(with `z = v n - u`), and with `W` the largest `w ≥ 1` such that `z₀ w^t + u ≤ v N`, the hits
`n ∈ [1, N]` with `v n > u` correspond to the `w ∈ [1, W]` with `v ∣ z₀ w^t + u`. -/
theorem radical_hits_card {c z₀ r d u v N W : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hv : 0 < v) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d)
    (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d)
    (hW : ∀ w, 1 ≤ w → (z₀ * w ^ (d / Nat.gcd r d) + u ≤ v * N ↔ w ≤ W)) :
    #{n ∈ Icc 1 N | u < v * n ∧ ∃ w : ℕ, c * (v * n - u) ^ r = w ^ d} =
      #{w ∈ Icc 1 W | v ∣ z₀ * w ^ (d / Nat.gcd r d) + u} := by
  obtain ⟨t, htdef⟩ : ∃ t, t = d / Nat.gcd r d := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htdef]; exact Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
  rw [← htdef] at hW ⊢
  have hparam := fun z (hz : z ≠ 0) => mul_pow_isPow_iff_param (z := z) hd hc hz₀ hz h₀ hmin
  rw [← htdef] at hparam
  symm
  refine card_nbij' (fun w => (z₀ * w ^ t + u) / v)
    (fun n => Classical.epsilon fun w => v * n - u = z₀ * w ^ t) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_Icc] at hw ⊢
    obtain ⟨⟨hw1, hwW⟩, k, hk⟩ := hw
    have hle := (hW w hw1).mpr hwW
    have hpos : 0 < z₀ * w ^ t := Nat.mul_pos (Nat.pos_of_ne_zero hz₀) (pow_pos hw1 t)
    have hn : (z₀ * w ^ t + u) / v = k := by rw [hk, Nat.mul_div_cancel_left _ hv]
    rw [hn]
    have hvk : u < v * k := by omega
    refine ⟨⟨?_, ?_⟩, hvk, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hvk
      · exact h
    · by_contra hlt; push_neg at hlt
      have : v * N < v * k := Nat.mul_lt_mul_of_pos_left hlt hv
      omega
    · refine (hparam (v * k - u) (by omega)).mpr ⟨w, by omega⟩
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, hun, hhit⟩ := hn
    have hex := (hparam (v * n - u) (by omega)).mp hhit
    have hspec := Classical.epsilon_spec hex
    set w := Classical.epsilon fun w => v * n - u = z₀ * w ^ t
    have hw1 : 1 ≤ w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · rw [h, zero_pow ht.ne', mul_zero] at hspec; omega
      · exact h
    refine ⟨⟨hw1, (hW w hw1).mp ?_⟩, ⟨n, by omega⟩⟩
    have : v * n ≤ v * N := Nat.mul_le_mul_left v hnN
    omega
  · intro w hw
    simp only [mem_filter, mem_Icc] at hw
    obtain ⟨⟨hw1, -⟩, k, hk⟩ := hw
    have hn : (z₀ * w ^ t + u) / v = k := by rw [hk, Nat.mul_div_cancel_left _ hv]
    simp only [hn]
    have hex : ∃ w', v * k - u = z₀ * w' ^ t := ⟨w, by omega⟩
    have hspec := Classical.epsilon_spec hex
    have hz0 : 0 < z₀ := Nat.pos_of_ne_zero hz₀
    have : (Classical.epsilon fun w' => v * k - u = z₀ * w' ^ t) ^ t = w ^ t := by
      have h2 : z₀ * (Classical.epsilon fun w' => v * k - u = z₀ * w' ^ t) ^ t = z₀ * w ^ t := by
        omega
      exact Nat.eq_of_mul_eq_mul_left hz0 h2
    exact Nat.pow_left_injective ht.ne' this
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, -⟩, hun, hhit⟩ := hn
    have hex := (hparam (v * n - u) (by omega)).mp hhit
    have hspec := Classical.epsilon_spec hex
    simp only
    rw [← hspec, Nat.sub_add_cancel hun.le, Nat.mul_div_cancel_left _ hv]

/-- **Count of the radical type.**  With `R` the number of `w ∈ [1, v]` satisfying the
congruence (`R` good residues modulo `v`) and `W` as in `radical_hits_card`,
`|v · A(N) - R · W| ≤ 2 R v`, i.e. `A(N) = (R / v) W + O(R)`. -/
theorem radical_count_bound {c z₀ r d u v N W : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hv : 0 < v) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d)
    (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d)
    (hW : ∀ w, 1 ≤ w → (z₀ * w ^ (d / Nat.gcd r d) + u ≤ v * N ↔ w ≤ W)) :
    let AN := #{n ∈ Icc 1 N | u < v * n ∧ ∃ w : ℕ, c * (v * n - u) ^ r = w ^ d}
    let R := #{w ∈ Icc 1 v | v ∣ z₀ * w ^ (d / Nat.gcd r d) + u}
    v * AN ≤ R * W + 2 * R * v ∧ R * W ≤ v * AN + 2 * R * v := by
  intro AN R
  set t := d / Nat.gcd r d
  have hAN : AN = Nat.count (fun k => v ∣ z₀ * (k + 1) ^ t + u) W := by
    show #_ = _
    rw [radical_hits_card hd hc hz₀ hv h₀ hmin hW, card_Icc_filter_eq_count]
  have hR : R = Nat.count (fun k => v ∣ z₀ * (k + 1) ^ t + u) v := card_Icc_filter_eq_count _ v
  have hper : ∀ w, v ∣ z₀ * (w + v + 1) ^ t + u ↔ v ∣ z₀ * (w + 1) ^ t + u := by
    intro w
    have hmod : (w + v + 1) ^ t ≡ (w + 1) ^ t [MOD v] :=
      Nat.ModEq.pow t (by rw [show w + v + 1 = w + 1 + v by ring]; exact Nat.add_modEq_right)
    have : z₀ * (w + v + 1) ^ t + u ≡ z₀ * (w + 1) ^ t + u [MOD v] :=
      Nat.ModEq.add_right u (Nat.ModEq.mul_left z₀ hmod)
    exact ⟨fun h => (Nat.modEq_zero_iff_dvd.mp (this.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))),
      fun h => (Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr h)))⟩
  rw [hAN, hR]
  have h1 := count_periodic_le (p := fun k => v ∣ z₀ * (k + 1) ^ t + u) hv hper W
  have h2 := le_count_periodic (p := fun k => v ∣ z₀ * (k + 1) ^ t + u) hv hper W
  constructor <;> nlinarith

/-- Sanity instance: the squares `n ≤ 10` (`c = z₀ = r = v = 1`, `u = 0`, `d = 2`, `W = 3`).
The bound gives `A(10) ∈ [1, 5]`; the hypotheses are satisfiable. -/
example : let AN := #{n ∈ Icc 1 10 | 0 < 1 * n ∧ ∃ w : ℕ, 1 * (1 * n - 0) ^ 1 = w ^ 2}
    let R := #{w ∈ Icc 1 1 | 1 ∣ 1 * w ^ (2 / Nat.gcd 1 2) + 0}
    1 * AN ≤ R * 3 + 2 * R * 1 ∧ R * 3 ≤ 1 * AN + 2 * R * 1 := by
  refine radical_count_bound (by norm_num) one_ne_zero one_ne_zero one_pos ⟨1, by norm_num⟩
    (fun p => by simp) (fun w _ => ?_)
  simp only [Nat.gcd_one_left, Nat.reduceDiv, one_mul, add_zero]
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; interval_cases w <;> norm_num

end PerfectPower
