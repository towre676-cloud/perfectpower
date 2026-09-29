import PerfectPower.Continuation.PellCountGeneral

/-!
# When is the counting constant positive?

`Decomposition.radical_count` and `Decomposition.pell_count` give `A(N) = κ N^{1/t} + O(1)` and
`A(N) = κ log N + O(1)` with some `κ ≥ 0`.  This file decides positivity.

1. *Uniqueness and meaning* (`kappa_pos_iff_rpow`, `kappa_pos_iff_log`,
   `infinite_iff_unbounded`): in either asymptotic, `κ > 0` iff `A(N)` is unbounded iff there are
   infinitely many hits.  Hence `radical_count_pos` and `pell_count_pos`: for a general `F`,
   `κ > 0 ↔ {n ≥ 1 : F(n) is a d-th power}` is infinite.
2. *A finite check, radical type* (`nat_radical_infinite_iff`): for `c (v n - u)^r` with natural
   data, the hit set is infinite iff some hit `n ≤ c^{t-1} v^t + u` has `v n > u`.  One hit with
   `z = v n - u > 0` gives `z = z₀ w^t`, and every `w' ≡ w (mod v)` gives another; taking `w' ≤ v`
   and `z₀ ∣ c^{t-1}` (`z0_dvd`) bounds the witness.
-/

open Finset Polynomial Filter
open scoped Classical

namespace PerfectPower.RationalYun

/-! ### Positivity of `κ` is infinitude -/

/-- A predicate holds for infinitely many `n ≥ 1` iff its counting function is unbounded. -/
theorem infinite_iff_unbounded (P : ℕ → Prop) :
    {n : ℕ | 1 ≤ n ∧ P n}.Infinite ↔ ∀ M : ℕ, ∃ N : ℕ, M < #((Icc 1 N).filter P) := by
  constructor
  · intro hinf M
    obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq (M + 1)
    refine ⟨t.sup id, ?_⟩
    calc M < #t := by omega
      _ ≤ _ := by
        apply card_le_card
        intro n hn
        have := ht hn
        simp only [Set.mem_setOf_eq] at this
        simp only [mem_filter, mem_Icc]
        exact ⟨⟨this.1, le_sup (f := id) hn⟩, this.2⟩
  · intro hunb hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨N, hN⟩ := hunb B
    have : #((Icc 1 N).filter P) ≤ #(Icc 1 B) := by
      apply card_le_card
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      exact ⟨hn.1.1, hB ⟨hn.1.1, hn.2⟩⟩
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    omega

/-- With `|A(N) - κ N^α| ≤ K` and `α > 0`, `κ > 0` iff `A` is unbounded. -/
theorem kappa_pos_iff_rpow {A : ℕ → ℕ} {κ K α : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ)
    (h : ∀ N : ℕ, |(A N : ℝ) - κ * (N : ℝ) ^ α| ≤ K) :
    0 < κ ↔ ∀ M : ℕ, ∃ N : ℕ, M < A N := by
  constructor
  · intro hpos M
    have hlim := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      ((M + K + 1) / κ)
    obtain ⟨N, hN⟩ := hlim.exists
    refine ⟨N, ?_⟩
    have hN' : (M + K + 1) / κ < (N : ℝ) ^ α := hN
    have h1 : M + K + 1 < κ * (N : ℝ) ^ α := by rwa [div_lt_iff₀ hpos, mul_comm] at hN'
    have h2 := (abs_le.mp (h N)).1
    have : (M : ℝ) < A N := by linarith
    exact_mod_cast this
  · intro hunb
    rcases hκ.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      obtain ⟨N, hN⟩ := hunb (Nat.ceil K)
      have h2 := (abs_le.mp (h N)).2
      rw [← hzero, zero_mul, sub_zero] at h2
      have : (Nat.ceil K : ℝ) < A N := by exact_mod_cast hN
      linarith [Nat.le_ceil K]

/-- With `|A(N) - κ log N| ≤ K` for `N ≥ N₀`, `κ > 0` iff `A` is unbounded (`A` monotone). -/
theorem kappa_pos_iff_log {A : ℕ → ℕ} {κ K : ℝ} {N₀ : ℕ} (hκ : 0 ≤ κ) (hmono : Monotone A)
    (h : ∀ N : ℕ, N₀ ≤ N → |(A N : ℝ) - κ * Real.log N| ≤ K) :
    0 < κ ↔ ∀ M : ℕ, ∃ N : ℕ, M < A N := by
  constructor
  · intro hpos M
    have hlim := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      ((M + K + 1) / κ)
    obtain ⟨N, hN, hNN₀⟩ := (hlim.and (eventually_ge_atTop N₀)).exists
    refine ⟨N, ?_⟩
    have hN' : (M + K + 1) / κ < Real.log N := hN
    have h1 : M + K + 1 < κ * Real.log N := by rwa [div_lt_iff₀ hpos, mul_comm] at hN'
    have h2 := (abs_le.mp (h N hNN₀)).1
    have : (M : ℝ) < A N := by linarith
    exact_mod_cast this
  · intro hunb
    rcases hκ.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      obtain ⟨N, hN⟩ := hunb (Nat.ceil K)
      have hmax := hmono (le_max_left N N₀)
      have h2 := (abs_le.mp (h (max N N₀) (le_max_right N N₀))).2
      rw [← hzero, zero_mul, sub_zero] at h2
      have : (Nat.ceil K : ℝ) < A (max N N₀) := by exact_mod_cast lt_of_lt_of_le hN hmax
      linarith [Nat.le_ceil K]

lemma count_mono (P : ℕ → Prop) : Monotone fun N => #((Icc 1 N).filter P) := by
  intro a b hab
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hab⟩, hn.2⟩

/-- **Theorem B, with positivity decided by infinitude.** -/
theorem Decomposition.radical_count_pos {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {d : ℕ} (hd : 2 ≤ d)
    (hbad : Y.badDegree d = 1) :
    ∃ t : ℕ, 2 ≤ t ∧ t ∣ d ∧ ∃ κ K : ℝ, 0 ≤ κ ∧
      (∀ N : ℕ, |(#((Icc 1 N).filter fun n : ℕ => IsHit d (F.eval (n : ℤ))) : ℝ) -
        κ * (N : ℝ) ^ ((t : ℝ)⁻¹)| ≤ K) ∧
      (0 < κ ↔ {n : ℕ | 1 ≤ n ∧ IsHit d (F.eval (n : ℤ))}.Infinite) := by
  obtain ⟨t, ht, htd, κ, K, hκ, hK⟩ := Y.radical_count hd hbad
  refine ⟨t, ht, htd, κ, K, hκ, hK, ?_⟩
  rw [infinite_iff_unbounded]
  exact kappa_pos_iff_rpow (by positivity) hκ hK

/-- **Theorem C, with positivity decided by infinitude.** -/
theorem Decomposition.pell_count_pos {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {e : ℕ} (he : e ≠ 0)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % (2 * e) = 0 ∨ (j + 1) % (2 * e) = e ∨ Y.part (j + 1) = 1)
    (hdegree : (∑ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e),
      (Y.part (j + 1)).natDegree) = 2) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(#((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) : ℝ) -
        κ * Real.log N| ≤ K) ∧
      (0 < κ ↔ {n : ℕ | 1 ≤ n ∧ IsHit (2 * e) (F.eval (n : ℤ))}.Infinite) := by
  obtain ⟨κ, K, hκ, N₀, hK⟩ := Y.pell_count he hres hdegree
  refine ⟨κ, K, hκ, ⟨N₀, hK⟩, ?_⟩
  rw [infinite_iff_unbounded]
  exact kappa_pos_iff_log hκ (count_mono _) hK

/-! ### A finite check for the radical type -/

/-- The minimal `z₀` divides `c^{t-1}`: its primes divide `c`, with exponents below `t`. -/
theorem z0_dvd {c r d z₀ : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d) (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d) :
    z₀ ∣ c ^ (d / Nat.gcd r d - 1) := by
  have hct : c ^ (d / Nat.gcd r d - 1) ≠ 0 := pow_ne_zero _ hc
  rw [← Nat.factorization_le_iff_dvd hz₀ hct]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hlt := hmin p
  by_cases hcp : c.factorization p = 0
  · -- `p ∤ c`: then `t ∣ v_p(z₀) < t`, so `v_p(z₀) = 0`
    have H := (exists_pow_iff_factorization d (mul_ne_zero hc (pow_ne_zero r hz₀))).mp h₀ p
    rw [factorization_mul_pow hc hz₀, hcp, zero_add] at H
    have H' : (d : ℤ) ∣ r * (z₀.factorization p : ℤ) := by exact_mod_cast H
    obtain ⟨k, hk⟩ := (dvd_mul_iff_div_gcd_dvd hd _).mp H'
    have hk0 : k = 0 := by
      have hlt' : (z₀.factorization p : ℤ) < (d / Nat.gcd r d : ℕ) := by exact_mod_cast hlt
      rcases lt_trichotomy k 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hk0, mul_zero] at hk
    omega
  · have : 1 ≤ c.factorization p := Nat.one_le_iff_ne_zero.mpr hcp
    calc z₀.factorization p ≤ d / Nat.gcd r d - 1 := by omega
      _ = (d / Nat.gcd r d - 1) * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ this

/-- From one hit with `z = v n - u > 0`: the parametrisation `z = z₀ w^t`, with `z₀` minimal. -/
lemma hit_param {c r d u v n : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hvn : u < v * n)
    (hhit : IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)) :
    ∃ z₀ w : ℕ, z₀ ≠ 0 ∧ (∃ W : ℕ, c * z₀ ^ r = W ^ d) ∧
      (∀ p, z₀.factorization p < d / Nat.gcd r d) ∧ 0 < w ∧
      v * n - u = z₀ * w ^ (d / Nat.gcd r d) := by
  have hz : v * n - u ≠ 0 := by omega
  have hcast : (((v * n - u : ℕ)) : ℤ) = (v : ℤ) * n - u := by
    push_cast [Nat.cast_sub hvn.le]; ring
  obtain ⟨m, hm⟩ := hhit
  have hpow : ∃ W : ℕ, c * (v * n - u) ^ r = W ^ d := by
    refine ⟨m.natAbs, ?_⟩
    have := congrArg Int.natAbs hm
    rw [Int.natAbs_pow, ← hcast] at this
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  rcases z0_dichotomy (r := r) hd hc with hno | ⟨z₀, hz₀, h₀, hmin⟩
  · exact absurd hpow (hno _ hz)
  · obtain ⟨w, hw⟩ := (mul_pow_isPow_iff_param hd hc hz₀ hz h₀ hmin).mp hpow
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · rw [h, zero_pow (by
          have := Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
          omega), mul_zero] at hw
        exact absurd hw hz
      · exact h
    exact ⟨z₀, w, hz₀, h₀, hmin, hw0, hw⟩

/-- The hit produced by a residue `w` with `v ∣ z₀ w^t + u`. -/
lemma hit_of_residue {c r d u v z₀ w : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h₀ : ∃ W : ℕ, c * z₀ ^ r = W ^ d) (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d)
    (hw : 0 < w) (hdiv : v ∣ z₀ * w ^ (d / Nat.gcd r d) + u) :
    let n := (z₀ * w ^ (d / Nat.gcd r d) + u) / v
    1 ≤ n ∧ u < v * n ∧ IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r) := by
  intro n
  set t := d / Nat.gcd r d
  have hvn : v * n = z₀ * w ^ t + u := Nat.mul_div_cancel' hdiv
  clear_value n
  have hpos : 0 < z₀ * w ^ t := Nat.mul_pos (Nat.pos_of_ne_zero hz₀) (pow_pos hw t)
  have hun : u < v * n := by rw [hvn]; omega
  refine ⟨?_, hun, ?_⟩
  · by_contra h; push_neg at h
    have : n = 0 := by omega
    rw [this, mul_zero] at hvn; omega
  · have hz : z₀ * w ^ t ≠ 0 := hpos.ne'
    obtain ⟨W, hW⟩ := (mul_pow_isPow_iff_param hd hc hz₀ hz h₀ hmin).mpr ⟨w, rfl⟩
    refine ⟨W, ?_⟩
    have : (v : ℤ) * n - u = ((z₀ * w ^ t : ℕ) : ℤ) := by
      push_cast; linarith
    rw [this]
    exact_mod_cast hW

/-- **One hit with `v n > u` gives infinitely many.** -/
theorem nat_infinite_of_hit {c r d u v : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hv : 0 < v) {n₀ : ℕ}
    (hvn : u < v * n₀) (hhit : IsHit d ((c : ℤ) * ((v : ℤ) * n₀ - u) ^ r)) :
    {n : ℕ | 1 ≤ n ∧ IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)}.Infinite := by
  set t := d / Nat.gcd r d
  obtain ⟨z₀, w, hz₀, h₀, hmin, hw, hzw⟩ := hit_param hd hc hvn hhit
  -- the hits for `w + k v`, `k ∈ ℕ`
  have hdivk : ∀ k : ℕ, v ∣ z₀ * (w + k * v) ^ t + u := by
    intro k
    have hmod : w + k * v ≡ w [MOD v] := by
      simp [Nat.ModEq, Nat.add_mul_mod_self_right]
    have h1 : z₀ * (w + k * v) ^ t + u ≡ z₀ * w ^ t + u [MOD v] :=
      Nat.ModEq.add_right u (Nat.ModEq.mul_left z₀ (Nat.ModEq.pow t hmod))
    rw [← hzw, Nat.sub_add_cancel hvn.le] at h1
    exact (Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr ⟨n₀, by ring⟩)))
  let f : ℕ → ℕ := fun k => (z₀ * (w + k * v) ^ t + u) / v
  have ht0 : 0 < t := Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
  apply Set.infinite_of_injective_forall_mem (f := f)
  · intro a b hab
    simp only [f] at hab
    have ha := Nat.mul_div_cancel' (hdivk a)
    have hb := Nat.mul_div_cancel' (hdivk b)
    rw [hab] at ha
    have h1 : z₀ * (w + a * v) ^ t = z₀ * (w + b * v) ^ t := by omega
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hz₀) h1
    have h3 := Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp ht0) h2
    have h4 : a * v = b * v := by omega
    exact Nat.eq_of_mul_eq_mul_right hv h4
  · intro k
    obtain ⟨h1, -, h3⟩ := hit_of_residue hd hc hz₀ h₀ hmin (by positivity) (hdivk k)
    exact ⟨h1, h3⟩

/-- **A finite check for infinitude, radical type.** -/
theorem nat_radical_infinite_iff {c r d u v : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hv : 0 < v) :
    {n : ℕ | 1 ≤ n ∧ IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)}.Infinite ↔
      ∃ n ∈ Icc 1 (c ^ (d / Nat.gcd r d - 1) * v ^ (d / Nat.gcd r d) + u),
        u < v * n ∧ IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r) := by
  set t := d / Nat.gcd r d
  constructor
  · intro hinf
    obtain ⟨n, ⟨hn1, hhit⟩, hnu⟩ := hinf.exists_gt u
    have hvn : u < v * n := lt_of_lt_of_le hnu (Nat.le_mul_of_pos_left n hv)
    obtain ⟨z₀, w, hz₀, h₀, hmin, hw, hzw⟩ := hit_param hd hc hvn hhit
    -- reduce `w` to a residue `w' ∈ [1, v]`
    set w' := (w - 1) % v + 1
    have hw'1 : 0 < w' := Nat.succ_pos _
    have hw'v : w' ≤ v := by have := Nat.mod_lt (w - 1) hv; omega
    have hmod : w' ≡ w [MOD v] := by
      have h1 : (w - 1) % v ≡ w - 1 [MOD v] := Nat.mod_modEq _ _
      have := Nat.ModEq.add_right 1 h1
      rwa [Nat.sub_add_cancel hw] at this
    have hdiv : v ∣ z₀ * w' ^ t + u := by
      have h1 : z₀ * w' ^ t + u ≡ z₀ * w ^ t + u [MOD v] :=
        Nat.ModEq.add_right u (Nat.ModEq.mul_left z₀ (Nat.ModEq.pow t hmod))
      rw [← hzw, Nat.sub_add_cancel hvn.le] at h1
      exact (Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr ⟨n, by ring⟩)))
    obtain ⟨h1, h2, h3⟩ := hit_of_residue hd hc hz₀ h₀ hmin hw'1 hdiv
    refine ⟨_, ?_, h2, h3⟩
    simp only [mem_Icc]
    refine ⟨h1, ?_⟩
    have hz0le : z₀ ≤ c ^ (t - 1) :=
      Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hc) _) (z0_dvd hd hc hz₀ h₀ hmin)
    have hwle : w' ^ t ≤ v ^ t := Nat.pow_le_pow_left hw'v t
    have hle : z₀ * w' ^ t + u ≤ c ^ (t - 1) * v ^ t + u := by
      have := Nat.mul_le_mul hz0le hwle; omega
    calc (z₀ * w' ^ t + u) / v ≤ z₀ * w' ^ t + u := Nat.div_le_self _ _
      _ ≤ _ := hle
  · rintro ⟨n₀, -, hvn, hhit⟩
    exact nat_infinite_of_hit hd hc hv hvn hhit


/-! ### Lifting the finite check to integer data and to `F` -/

/-- A shift by `k` does not change infinitude. -/
theorem infinite_shift (P : ℕ → Prop) (k : ℕ) :
    {n : ℕ | 1 ≤ n ∧ P (n + k)}.Infinite ↔ {n : ℕ | 1 ≤ n ∧ P n}.Infinite := by
  rw [infinite_iff_unbounded, infinite_iff_unbounded]
  constructor
  · intro h M
    obtain ⟨N, hN⟩ := h (M + k)
    obtain ⟨s1, -⟩ := shift_count P k N
    exact ⟨N, by omega⟩
  · intro h M
    obtain ⟨N, hN⟩ := h (M + k)
    obtain ⟨-, s2⟩ := shift_count P k N
    exact ⟨N, by omega⟩

/-- Adding a finite set of extra indices does not change infinitude. -/
theorem infinite_or_finite (Z P : ℕ → Prop) (hZ : {n : ℕ | Z n}.Finite) :
    {n : ℕ | 1 ≤ n ∧ (Z n ∨ P n)}.Infinite ↔ {n : ℕ | 1 ≤ n ∧ P n}.Infinite := by
  have e : {n : ℕ | 1 ≤ n ∧ (Z n ∨ P n)} = {n : ℕ | 1 ≤ n ∧ P n} ∪ {n : ℕ | 1 ≤ n ∧ Z n} := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
  rw [e, Set.infinite_union]
  have : ¬ {n : ℕ | 1 ≤ n ∧ Z n}.Infinite :=
    Set.not_infinite.mpr (hZ.subset fun n hn => hn.2)
  tauto

/-- The zeros of a nonzero integer polynomial at natural arguments are finite. -/
theorem zeros_finite (F : ℤ[X]) (hF : F ≠ 0) : {n : ℕ | F.eval (n : ℤ) = 0}.Finite := by
  apply (F.roots.toFinset.finite_toSet.preimage (Nat.cast_injective.injOn (f := ((↑) : ℕ → ℤ)))).subset
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  exact (mem_roots hF).mpr hn

/-- **The finite check for integer data** `C (V n - U)^r`, any `C ≠ 0`, any integer `U`. -/
theorem int_radical_infinite_iff {C U : ℤ} {r d V : ℕ} (hd : 0 < d) (hC : C ≠ 0) (hV : 0 < V) :
    {n : ℕ | 1 ≤ n ∧ IsHit d (C * ((V : ℤ) * n - U) ^ r)}.Infinite ↔
      ∃ n : ℤ, 1 - (U.natAbs : ℤ) ≤ n ∧
        n ≤ ((C.natAbs ^ (d / Nat.gcd r d - 1) * V ^ (d / Nat.gcd r d) +
          (U + V * U.natAbs).toNat : ℕ) : ℤ) ∧
        U < V * n ∧ IsHit d (C * ((V : ℤ) * n - U) ^ r) := by
  set k := U.natAbs
  set u := (U + V * k).toNat
  have hu : (u : ℤ) = U + V * k := by
    apply Int.toNat_of_nonneg
    have hk : (k : ℤ) = |U| := Int.natCast_natAbs U
    rw [hk]
    nlinarith [neg_abs_le U, abs_nonneg U]
  -- sign: `C < 0` with `d` even never hits at `V n > U`
  by_cases hbad : C < 0 ∧ Even d
  · have hno : ∀ n : ℤ, U < V * n → ¬ IsHit d (C * ((V : ℤ) * n - U) ^ r) := by
      rintro n hn ⟨m, hm⟩
      have hz : (0 : ℤ) < V * n - U := by linarith
      have h1 : C * ((V : ℤ) * n - U) ^ r < 0 := mul_neg_of_neg_of_pos hbad.1 (pow_pos hz r)
      have h2 : 0 ≤ m ^ d := Even.pow_nonneg hbad.2 m
      linarith
    constructor
    · intro hinf
      exfalso
      obtain ⟨n, ⟨-, hhit⟩, hn⟩ := hinf.exists_gt k
      apply hno n _ hhit
      have hk : (k : ℤ) = |U| := Int.natCast_natAbs U
      have : (n : ℤ) ≤ V * n := by nlinarith
      linarith [le_abs_self U]
    · rintro ⟨n, -, -, hn, hhit⟩
      exact absurd hhit (hno n hn)
  -- otherwise the sign can be dropped
  have hsign : ∀ X : ℤ, IsHit d (C * X) ↔ IsHit d ((C.natAbs : ℤ) * X) := by
    intro X
    rcases lt_or_gt_of_ne hC with hneg | hpos
    · have hodd : Odd d := by
        rcases Nat.even_or_odd d with he | ho
        · exact absurd ⟨hneg, he⟩ hbad
        · exact ho
      have hC' : (C.natAbs : ℤ) = -C := by rw [Int.natCast_natAbs, abs_of_neg hneg]
      rw [hC']
      constructor
      · rintro ⟨m, hm⟩; exact ⟨-m, by rw [Odd.neg_pow hodd, ← hm]; ring⟩
      · rintro ⟨m, hm⟩; exact ⟨-m, by rw [Odd.neg_pow hodd, ← hm]; ring⟩
    · rw [show (C.natAbs : ℤ) = C by rw [Int.natCast_natAbs, abs_of_pos hpos]]
  have hC0 : C.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hC
  have hshift : ∀ n : ℕ, (V : ℤ) * n - U = (V : ℤ) * ((n + k : ℕ) : ℤ) - u := by
    intro n; push_cast; rw [hu]; ring
  have eset : {n : ℕ | 1 ≤ n ∧ IsHit d (C * ((V : ℤ) * n - U) ^ r)} =
      {n : ℕ | 1 ≤ n ∧ IsHit d ((C.natAbs : ℤ) * ((V : ℤ) * ((n + k : ℕ) : ℤ) - u) ^ r)} := by
    ext n; simp only [Set.mem_setOf_eq]; rw [hsign, hshift]
  rw [eset, infinite_shift (fun m => IsHit d ((C.natAbs : ℤ) * ((V : ℤ) * (m : ℤ) - u) ^ r)) k]
  constructor
  · intro hinf
    obtain ⟨m, hm, hum, hhit⟩ := (nat_radical_infinite_iff hd hC0 hV).mp hinf
    simp only [mem_Icc] at hm
    refine ⟨(m : ℤ) - k, by omega, by omega, ?_, ?_⟩
    · linarith [hu]
    · rw [hsign]
      convert hhit using 3
      rw [hu]; ring
  · rintro ⟨n, hn1, -, hUn, hhit⟩
    rw [hsign] at hhit
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = n + k := ⟨(n + k).toNat, Int.toNat_of_nonneg (by omega)⟩
    apply nat_infinite_of_hit hd hC0 hV (n₀ := m)
    · have : (u : ℤ) < V * m := by rw [hu, hm]; linarith
      exact_mod_cast this
    · convert hhit using 3
      rw [hm, hu]; ring


/-- **Theorem B, positivity decided by a finite check.**  For `F` with one bad layer, the constant
`κ` of `A(N) = κ N^{1/t} + O(1)` is positive iff some integer `n` in an explicit finite range is a
hit of the reduced form `C (V n - U)^r` with `V n > U`.  Here `C = lc(F) v^{d-r}`, `U`, `V`, `r` are
the data of `integer_radical_reduction`. -/
theorem Decomposition.radical_kappa_decide {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {d : ℕ} (hd : 2 ≤ d)
    (hbad : Y.badDegree d = 1) :
    ∃ t : ℕ, 2 ≤ t ∧ t ∣ d ∧ ∃ κ K : ℝ, 0 ≤ κ ∧
      (∀ N : ℕ, |(#((Icc 1 N).filter fun n : ℕ => IsHit d (F.eval (n : ℤ))) : ℝ) -
        κ * (N : ℝ) ^ ((t : ℝ)⁻¹)| ≤ K) ∧
      ∃ C U : ℤ, ∃ V r : ℕ, C ≠ 0 ∧ 0 < V ∧
        (∀ n : ℤ, IsHit d (F.eval n) ↔ F.eval n = 0 ∨ IsHit d (C * ((V : ℤ) * n - U) ^ r)) ∧
        (0 < κ ↔ ∃ n : ℤ, 1 - (U.natAbs : ℤ) ≤ n ∧
          n ≤ ((C.natAbs ^ (d / Nat.gcd r d - 1) * V ^ (d / Nat.gcd r d) +
            (U + V * U.natAbs).toNat : ℕ) : ℤ) ∧
          U < V * n ∧ IsHit d (C * ((V : ℤ) * n - U) ^ r)) := by
  obtain ⟨t, ht, htd, κ, K, hκ, hK, hpos⟩ := Y.radical_count_pos hd hbad
  obtain ⟨u, v, hv, r, hr, hrd, hiff⟩ := Y.integer_radical_reduction hd hbad
  have hFq : F.map (Int.castRingHom ℚ) ≠ 0 := Y.ne_zero
  have hF : F ≠ 0 := by rintro rfl; exact hFq (Polynomial.map_zero _)
  have hC : F.leadingCoeff * v ^ (d - r) ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ hv.ne')
  set V := v.toNat
  have hV : (V : ℤ) = v := Int.toNat_of_nonneg hv.le
  have hV0 : 0 < V := by omega
  have hiff' : ∀ n : ℤ, IsHit d (F.eval n) ↔
      F.eval n = 0 ∨ IsHit d (F.leadingCoeff * v ^ (d - r) * ((V : ℤ) * n - u) ^ r) := by
    intro n; rw [hiff n, hV]
  refine ⟨t, ht, htd, κ, K, hκ, hK, _, u, V, r, hC, hV0, hiff', ?_⟩
  rw [hpos]
  have eset : {n : ℕ | 1 ≤ n ∧ IsHit d (F.eval (n : ℤ))} =
      {n : ℕ | 1 ≤ n ∧ (F.eval (n : ℤ) = 0 ∨
        IsHit d (F.leadingCoeff * v ^ (d - r) * ((V : ℤ) * n - u) ^ r))} := by
    ext n; simp only [Set.mem_setOf_eq]; rw [hiff' n]
  rw [eset, infinite_or_finite _ _ (zeros_finite F hF)]
  exact int_radical_infinite_iff (by omega) hC hV0

end PerfectPower.RationalYun
