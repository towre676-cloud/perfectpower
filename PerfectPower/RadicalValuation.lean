import PerfectPower.Monomial
import Mathlib.Data.Nat.Factorization.Basic

open Finsupp

namespace PerfectPower

/-! ### The valuation core of Theorem B (radical type)

Research notes, Theorem B: in the radical type, `n` is a hit iff `c₁ z^r` is a `d`-th power for
`z = v n - u`, and the solutions are `z = z₀ w^t`, `t = d / gcd(r, d)`.  This file proves the
arithmetic core:

* `exists_pow_iff_factorization`: `n ≠ 0` is a `d`-th power iff `d ∣ v_p(n)` for every `p`;
* `isHit_iff_natAbs`: the signed version (negative values need odd `d`);
* `isHit_iff_rat`: an integer that is a rational `d`-th power is an integer `d`-th power
  (the denominator step: multiplying by `v^(dK)` does not change hit status);
* `mul_pow_isPow_iff_congr`: if `c z₀^r` is a `d`-th power, then `c z^r` is one iff
  `v_p(z) ≡ v_p(z₀) (mod t)` for all `p`;
* `mul_pow_isPow_iff_param`: if moreover `v_p(z₀) < t` for all `p`, the solutions are exactly
  `z = z₀ w^t`. -/

/-- A nonzero natural number is a `d`-th power iff every exponent of its factorisation is
divisible by `d`. -/
theorem exists_pow_iff_factorization {n : ℕ} (d : ℕ) (hn : n ≠ 0) :
    (∃ w : ℕ, n = w ^ d) ↔ ∀ p, d ∣ n.factorization p := by
  constructor
  · rintro ⟨w, rfl⟩ p
    rw [Nat.factorization_pow]
    exact ⟨w.factorization p, by simp [mul_comm]⟩
  · intro h
    refine ⟨n.factorization.prod (fun p e => p ^ (e / d)), ?_⟩
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, Nat.div_mul_cancel (h p)]

/-- A nonzero integer is a `d`-th power (`d ≥ 1`) iff it is nonnegative when `d` is even and every
exponent of `|X|` is divisible by `d`. -/
theorem isHit_iff_natAbs {d : ℕ} {X : ℤ} (hX : X ≠ 0) :
    IsHit d X ↔ (Even d → 0 < X) ∧ ∀ p, d ∣ X.natAbs.factorization p := by
  have hXa : X.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hX
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨fun he => lt_of_le_of_ne (he.pow_nonneg m) (Ne.symm hX), ?_⟩
    exact (exists_pow_iff_factorization d hXa).mp ⟨m.natAbs, by rw [Int.natAbs_pow]⟩
  · rintro ⟨hsign, hfac⟩
    obtain ⟨w, hw⟩ := (exists_pow_iff_factorization d hXa).mpr hfac
    rcases Int.natAbs_eq X with h | h
    · exact ⟨w, by rw [h, hw]; push_cast; ring⟩
    · -- X < 0, so d is odd
      have hXneg : X < 0 := by omega
      have hodd : Odd d := by
        rcases Nat.even_or_odd d with he | ho
        · exact absurd (hsign he) (by omega)
        · exact ho
      exact ⟨-(w : ℤ), by rw [h, hw, hodd.neg_pow]; push_cast; ring⟩

/-- An integer is a `d`-th power of an integer iff it is a `d`-th power of a rational
(`d ≥ 1`). -/
theorem isHit_iff_rat {d : ℕ} (hd : d ≠ 0) (X : ℤ) : IsHit d X ↔ ∃ q : ℚ, (X : ℚ) = q ^ d := by
  constructor
  · rintro ⟨m, rfl⟩; exact ⟨m, by push_cast; ring⟩
  · rintro ⟨q, hq⟩
    have hden : (q ^ d).den = 1 := by rw [← hq]; rfl
    rw [Rat.den_pow] at hden
    have h1 : q.den = 1 := (pow_eq_one_iff hd).mp hden
    refine ⟨q.num, ?_⟩
    have hqnum : (q.num : ℚ) = q := Rat.coe_int_num_of_den_eq_one h1
    have : (X : ℚ) = ((q.num ^ d : ℤ) : ℚ) := by rw [hq]; push_cast; rw [hqnum]
    exact_mod_cast this

/-- Factorisation of `c z^r`. -/
lemma factorization_mul_pow {c z r : ℕ} (hc : c ≠ 0) (hz : z ≠ 0) (p : ℕ) :
    (c * z ^ r).factorization p = c.factorization p + r * z.factorization p := by
  rw [Nat.factorization_mul hc (pow_ne_zero r hz), Nat.factorization_pow]
  simp

/-- `d ∣ r x` iff `d / gcd(r, d) ∣ x` (over `ℤ`). -/
lemma dvd_mul_iff_div_gcd_dvd {d r : ℕ} (hd : 0 < d) (x : ℤ) :
    (d : ℤ) ∣ r * x ↔ ((d / Nat.gcd r d : ℕ) : ℤ) ∣ x := by
  set g := Nat.gcd r d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right r hd
  obtain ⟨t, ht⟩ : g ∣ d := Nat.gcd_dvd_right r d
  obtain ⟨r', hr'⟩ : g ∣ r := Nat.gcd_dvd_left r d
  have htd : d / g = t := by rw [ht, Nat.mul_div_cancel_left _ hg]
  have hcop : Nat.Coprime r' t := by
    have h0 : Nat.Coprime (r / g) (d / g) := Nat.coprime_div_gcd_div_gcd hg
    have e1 : r / g = r' := by
      conv_lhs => rw [hr']
      exact Nat.mul_div_cancel_left _ hg
    rwa [e1, htd] at h0
  rw [htd, hr', ht]
  push_cast
  rw [mul_assoc]
  have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [mul_dvd_mul_iff_left hg']
  constructor
  · intro h
    exact (Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hcop.symm)).dvd_of_dvd_mul_left h
  · intro h; exact Dvd.dvd.mul_left h _

/-- **Congruence form of Theorem B.**  Let `c, z₀, z > 0` with `c z₀^r` a `d`-th power.  Then
`c z^r` is a `d`-th power iff `v_p(z) ≡ v_p(z₀) (mod t)` for every prime `p`, `t = d / gcd(r, d)`. -/
theorem mul_pow_isPow_iff_congr {c z₀ z r d : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hz : z ≠ 0) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d) :
    (∃ w : ℕ, c * z ^ r = w ^ d) ↔
      ∀ p, ((d / Nat.gcd r d : ℕ) : ℤ) ∣ (z.factorization p : ℤ) - z₀.factorization p := by
  have hcz₀ : c * z₀ ^ r ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hz₀)
  have hcz : c * z ^ r ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hz)
  have H₀ := (exists_pow_iff_factorization d hcz₀).mp h₀
  rw [exists_pow_iff_factorization d hcz]
  refine forall_congr' fun p => ?_
  have e0 := H₀ p
  rw [factorization_mul_pow hc hz₀] at e0
  rw [factorization_mul_pow hc hz, ← dvd_mul_iff_div_gcd_dvd hd]
  have e0' : (d : ℤ) ∣ (c.factorization p : ℤ) + r * z₀.factorization p := by exact_mod_cast e0
  constructor
  · intro h
    have h' : (d : ℤ) ∣ (c.factorization p : ℤ) + r * z.factorization p := by exact_mod_cast h
    have := dvd_sub h' e0'
    rw [show (c.factorization p : ℤ) + r * z.factorization p - (c.factorization p + r * z₀.factorization p)
      = r * ((z.factorization p : ℤ) - z₀.factorization p) by ring] at this
    exact this
  · intro h
    have := dvd_add h e0'
    rw [show (r : ℤ) * ((z.factorization p : ℤ) - z₀.factorization p) + (c.factorization p + r * z₀.factorization p)
      = c.factorization p + r * z.factorization p by ring] at this
    exact_mod_cast this

/-- **Parametrisation form of Theorem B.**  If `c z₀^r` is a `d`-th power and `z₀` is minimal
(`v_p(z₀) < t` for every `p`), then `c z^r` (with `z > 0`) is a `d`-th power iff `z = z₀ w^t`. -/
theorem mul_pow_isPow_iff_param {c z₀ z r d : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hz : z ≠ 0) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d)
    (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d) :
    (∃ w : ℕ, c * z ^ r = w ^ d) ↔ ∃ w : ℕ, z = z₀ * w ^ (d / Nat.gcd r d) := by
  obtain ⟨t, htdef⟩ : ∃ t, t = d / Nat.gcd r d := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htdef]; exact Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
  rw [mul_pow_isPow_iff_congr hd hc hz₀ hz h₀, ← htdef]
  rw [← htdef] at hmin
  constructor
  · intro h
    -- each v_p(z) = v_p(z₀) + t k_p with k_p ≥ 0, since 0 ≤ v_p(z₀) < t
    have hle : ∀ p, z₀.factorization p ≤ z.factorization p := by
      intro p
      obtain ⟨k, hk⟩ := h p
      have hmin' : (z₀.factorization p : ℤ) < t := by exact_mod_cast hmin p
      by_contra hlt; push_neg at hlt
      rcases le_or_lt 0 k with hk0 | hk0
      · nlinarith
      · have : (t : ℤ) * k ≤ -t := by nlinarith
        nlinarith
    have hdvd : z₀ ∣ z := (Nat.factorization_le_iff_dvd hz₀ hz).mp (fun p => hle p)
    obtain ⟨q, rfl⟩ := hdvd
    have hq : q ≠ 0 := by rintro rfl; simp at hz
    refine ⟨q.factorization.prod (fun p e => p ^ (e / t)), ?_⟩
    congr 1
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hq]
    rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul]
    congr 1
    have hp := h p
    rw [Nat.factorization_mul hz₀ hq, Finsupp.add_apply] at hp
    push_cast at hp
    rw [show (z₀.factorization p : ℤ) + q.factorization p - z₀.factorization p
      = q.factorization p by ring] at hp
    exact (Nat.div_mul_cancel (by exact_mod_cast hp)).symm
  · rintro ⟨w, rfl⟩ p
    have hw : w ≠ 0 := by rintro rfl; simp [zero_pow ht.ne'] at hz
    rw [Nat.factorization_mul hz₀ (pow_ne_zero _ hw), Finsupp.add_apply, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    push_cast
    exact ⟨w.factorization p, by ring⟩

end PerfectPower
