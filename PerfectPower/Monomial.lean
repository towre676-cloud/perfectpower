import PerfectPower.ZeroOne

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### Monomials: `n^r` is a `d`-th power iff `n` is a `t`-th power, `t = d / gcd(r, d)`

This is the simplest radical-type family of the atlas (research notes, Theorem B with
`c = 1`, `α = 0`), and it realises every exponent `1/t`, `t ∣ d`, of the exponent spectrum. -/

/-- A rational `t`-th root of a natural number is (the cast of) an integer. -/
lemma rat_pow_eq_nat {t : ℕ} (ht : t ≠ 0) {c : ℚ} {n : ℕ} (h : c ^ t = n) :
    ∃ z : ℤ, c = z := by
  have hden : (c ^ t).den = 1 := by rw [h]; rfl
  rw [Rat.den_pow] at hden
  have h1 : c.den = 1 := (pow_eq_one_iff ht).mp hden
  exact ⟨c.num, (Rat.den_eq_one_iff c).mp h1 ▸ rfl⟩

/-- Core arithmetic: for `n ≥ 1`, `n^r = m^d` has an integer solution `m` iff `n` is a
`t`-th power with `t = d / gcd r d`. -/
theorem monomial_isHit_iff {r d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) :
    IsHit d ((n : ℤ) ^ r) ↔ ∃ w : ℕ, n = w ^ (d / Nat.gcd r d) := by
  set g := Nat.gcd r d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r hd
  obtain ⟨t, ht⟩ : g ∣ d := Nat.gcd_dvd_right r d
  obtain ⟨r', hr'⟩ : g ∣ r := Nat.gcd_dvd_left r d
  have htd : d / g = t := by rw [ht, Nat.mul_div_cancel_left _ hg0]
  rw [htd]
  have ht0 : t ≠ 0 := by rintro rfl; omega
  have hcop : Nat.Coprime r' t := by
    have := Nat.coprime_div_gcd_div_gcd (m := r) (n := d) hg0
    rwa [← hg, hr', ht, Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  constructor
  · rintro ⟨m, hm⟩
    -- n^(g r') = m^(g t)  ⟹  n^r' = |m|^t
    have hnat : (n ^ r') ^ g = (m.natAbs ^ t) ^ g := by
      have h2 := congrArg Int.natAbs hm
      rw [Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, hr', ht] at h2
      rw [← pow_mul, ← pow_mul, mul_comm r', mul_comm t]; exact h2
    have hbase : n ^ r' = m.natAbs ^ t := Nat.pow_left_injective (by omega) hnat
    have hq : (n : ℚ) ^ r' = ((m.natAbs : ℕ) : ℚ) ^ t := by exact_mod_cast hbase
    obtain ⟨c, hc1, _⟩ := (pow_eq_pow_iff_of_coprime hcop).mp hq
    obtain ⟨z, rfl⟩ := rat_pow_eq_nat ht0 (n := n) hc1.symm
    refine ⟨z.natAbs, ?_⟩
    have hz : (n : ℤ) = z ^ t := by exact_mod_cast hc1
    have := congrArg Int.natAbs hz
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at this
  · rintro ⟨w, rfl⟩
    refine ⟨(w : ℤ) ^ r', ?_⟩
    push_cast
    rw [← pow_mul, ← pow_mul, hr', ht]
    ring_nf

/-- The hit set of `S(n) = n^r` is exactly the set of positive `t`-th powers. -/
theorem monomial_hitSet {r d : ℕ} (hd : 0 < d) :
    hitSet (fun n => (n : ℤ) ^ r) d 0 = {n | 1 ≤ n ∧ ∃ w : ℕ, n = w ^ (d / Nat.gcd r d)} := by
  ext n
  simp only [hitSet, Set.mem_setOf_eq, add_zero]
  constructor
  · rintro ⟨hn, h⟩; exact ⟨hn, (monomial_isHit_iff hd hn).mp h⟩
  · rintro ⟨hn, h⟩; exact ⟨hn, (monomial_isHit_iff hd hn).mpr h⟩

/-- Exact count: `A(N)` for `n^r` equals the number of `w ∈ [1, N]` with `w^t ≤ N`,
i.e. `⌊N^(1/t)⌋`. -/
theorem monomial_count {r d : ℕ} (hd : 0 < d) (N : ℕ) :
    A (fun n => (n : ℤ) ^ r) d 0 N =
      ((Finset.Icc 1 N).filter (fun w => w ^ (d / Nat.gcd r d) ≤ N)).card := by
  set t := d / Nat.gcd r d with htdef
  have ht0 : t ≠ 0 := by
    have := Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
    omega
  unfold A
  symm
  refine Finset.card_bij (fun w _ => w ^ t) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_Icc] at hw ⊢
    have hw1 : 1 ≤ w ^ t := Nat.one_le_pow _ _ (by omega)
    refine ⟨⟨hw1, hw.2⟩, ?_⟩
    simpa using (monomial_isHit_iff hd hw1).mpr ⟨w, rfl⟩
  · intro a _ b _ hab
    exact Nat.pow_left_injective ht0 hab
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, add_zero] at hn
    obtain ⟨w, hw⟩ := (monomial_isHit_iff hd hn.1.1).mp hn.2
    refine ⟨w, ?_, hw.symm⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hw1 : 1 ≤ w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · rw [h, zero_pow ht0] at hw; omega
      · exact h
    refine ⟨⟨hw1, ?_⟩, hw ▸ hn.1.2⟩
    calc w ≤ w ^ t := Nat.le_self_pow ht0 w
      _ = n := hw.symm
      _ ≤ N := hn.1.2

end PerfectPower
