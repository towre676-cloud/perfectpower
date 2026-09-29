import PerfectPower.Continuation.DenominatorReduction
import PerfectPower.Atlas

/-!
# Theorem B as a count, for a general integer polynomial

`Decomposition.integer_radical_reduction` says that, when `F ∈ ℤ[X]` has exactly one bad rational
layer, `F(n)` is a `d`-th power iff `F(n) = 0` or `C (v n - u)^r` is one, with integers `C ≠ 0`,
`u`, `v > 0`.  `Atlas.atlas_radical` counts `c (v n - u)^r` for *natural* `c`, `u`, `v`, given a
minimal `z₀`.  This file closes the gap:

* `card_zeros_le`: the exceptional zeros `F(n) = 0` number at most `deg F`;
* `shift_count`: a shift `n ↦ n + k` (used to make `u ≥ 0`) moves counts by at most `k`;
* sign of `C`: for odd `d` it can be flipped; for even `d` and `C < 0` only `n ≤ u` can hit;
* `z0_dichotomy` (the arithmetic solvability criterion): either no `z ≥ 1` makes `c z^r` a
  `d`-th power, and the count is bounded, or the least such `z₀` has `v_p(z₀) < t` for all `p`
  and the atlas count applies.

`Decomposition.radical_count`: every `F` with bad degree 1 satisfies
`|A(N) - κ N^{1/t}| ≤ K` for some `κ ≥ 0`, `K`, and `t = d / gcd(r, d)` with `2 ≤ t ∣ d`.  The
constant `κ` is `(R/v)(v/z₀)^{1/t}` in the solvable case and `0` otherwise; whether it is positive
is the residue count `R`, which this file does not decide.
-/

open Finset Polynomial
open scoped Classical

namespace PerfectPower.RationalYun

/-- At most `deg F` indices are zeros of a nonzero `F`. -/
theorem card_zeros_le (F : ℤ[X]) (hF : F ≠ 0) (N : ℕ) :
    #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0) ≤ F.natDegree := by
  calc #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0)
      ≤ #F.roots.toFinset := by
        apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ))
        · intro n hn
          rw [mem_filter] at hn
          rw [Multiset.mem_toFinset, mem_roots hF, IsRoot.def]
          exact hn.2
        · intro a _ b _ h
          simp only at h
          exact_mod_cast h
    _ ≤ Multiset.card F.roots := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := card_roots' F

/-- A disjunction adds at most the count of the extra alternative. -/
lemma count_or (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] (N Z : ℕ) (hZ : #((Icc 1 N).filter p) ≤ Z) :
    #((Icc 1 N).filter q) ≤ #((Icc 1 N).filter fun n => p n ∨ q n) ∧
      #((Icc 1 N).filter fun n => p n ∨ q n) ≤ #((Icc 1 N).filter q) + Z := by
  constructor
  · apply card_le_card
    intro n hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn.1, Or.inr hn.2⟩
  · rw [filter_or]
    calc _ ≤ #((Icc 1 N).filter p) + #((Icc 1 N).filter q) := card_union_le _ _
      _ ≤ _ := by omega

/-- **Shifting the index by `k` moves the count by at most `k`.** -/
theorem shift_count (p : ℕ → Prop) [DecidablePred p] (k N : ℕ) :
    #((Icc 1 N).filter fun n => p (n + k)) ≤ #((Icc 1 N).filter p) + k ∧
      #((Icc 1 N).filter p) ≤ #((Icc 1 N).filter fun n => p (n + k)) + k := by
  constructor
  · calc #((Icc 1 N).filter fun n => p (n + k))
        ≤ #(((Icc 1 N).filter p) ∪ Icc (N + 1) (N + k)) := by
          apply Finset.card_le_card_of_injOn (fun n => n + k)
          · intro n hn
            rw [mem_filter, mem_Icc] at hn
            rw [mem_union, mem_filter, mem_Icc, mem_Icc]
            by_cases h : n + k ≤ N
            · left; exact ⟨⟨by omega, h⟩, hn.2⟩
            · right; omega
          · intro a _ b _ h
            simpa using h
      _ ≤ #((Icc 1 N).filter p) + #(Icc (N + 1) (N + k)) := card_union_le _ _
      _ = #((Icc 1 N).filter p) + k := by simp
  · have hsplit : (Icc 1 N).filter p ⊆
        ((Icc 1 N).filter fun n => n ≤ k) ∪ ((Icc 1 N).filter fun n => k < n ∧ p n) := by
      intro n hn
      simp only [mem_filter, mem_union] at hn ⊢
      by_cases h : n ≤ k
      · left; exact ⟨hn.1, h⟩
      · right; exact ⟨hn.1, by omega, hn.2⟩
    calc #((Icc 1 N).filter p)
        ≤ #((Icc 1 N).filter fun n => n ≤ k) + #((Icc 1 N).filter fun n => k < n ∧ p n) :=
          (card_le_card hsplit).trans (card_union_le _ _)
      _ ≤ k + #((Icc 1 N).filter fun n => p (n + k)) := by
          apply add_le_add
          · calc #((Icc 1 N).filter fun n => n ≤ k) ≤ #(Icc 1 k) := by
                  apply card_le_card
                  intro n hn
                  simp only [mem_filter, mem_Icc] at hn ⊢
                  omega
              _ = k := by simp
          · apply Finset.card_le_card_of_injOn (fun n => n - k)
            · intro n hn
              rw [mem_filter, mem_Icc] at hn
              rw [mem_filter, mem_Icc]
              refine ⟨⟨by omega, by omega⟩, ?_⟩
              rw [Nat.sub_add_cancel (by omega)]
              exact hn.2.2
            · intro a ha b hb h
              simp only [coe_filter, Set.mem_setOf_eq, mem_Icc] at ha hb
              simp only at h
              omega
      _ = _ := by ring

/-- **The arithmetic solvability criterion.**  Either `c z^r` is never a `d`-th power for
`z ≥ 1`, or the least such `z₀` is minimal in the sense `v_p(z₀) < d / gcd(r, d)`. -/
theorem z0_dichotomy {c r d : ℕ} (hd : 0 < d) (hc : c ≠ 0) :
    (∀ z : ℕ, z ≠ 0 → ¬ ∃ w : ℕ, c * z ^ r = w ^ d) ∨
      ∃ z₀ : ℕ, z₀ ≠ 0 ∧ (∃ w : ℕ, c * z₀ ^ r = w ^ d) ∧
        ∀ p, z₀.factorization p < d / Nat.gcd r d := by
  by_cases h : ∃ z : ℕ, z ≠ 0 ∧ ∃ w : ℕ, c * z ^ r = w ^ d
  · right
    have hspec := Nat.find_spec h
    refine ⟨Nat.find h, hspec.1, hspec.2, ?_⟩
    intro p
    by_contra hge
    push_neg at hge
    set t := d / Nat.gcd r d with ht
    have ht0 : 0 < t := Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
    have hpmem : p ∈ (Nat.find h).primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hdvd : p ^ t ∣ Nat.find h := (hp.pow_dvd_iff_le_factorization hspec.1).mpr hge
    obtain ⟨z', hz'⟩ := hdvd
    have hz'0 : z' ≠ 0 := by rintro rfl; apply hspec.1; simp at hz'
    have hpt : 2 ≤ p ^ t := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos ht0
    have hlt : z' < Nat.find h := by
      rw [hz']
      have : 0 < z' := Nat.pos_of_ne_zero hz'0
      nlinarith
    apply Nat.find_min h hlt
    refine ⟨hz'0, (mul_pow_isPow_iff_congr hd hc hspec.1 hz'0 hspec.2).mpr fun q => ?_⟩
    rw [hz', Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hz'0, hp.factorization_pow]
    rw [← ht]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs
    · exact ⟨-1, by push_cast; ring⟩
    · exact ⟨0, by push_cast; ring⟩
  · left
    intro z hz hw
    exact h ⟨z, hz, hw⟩

/-- The count of `c (v n - u)^r` for natural data, solvable or not. -/
theorem nat_radical_count {c r d u v : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hv : 0 < v) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)) : ℝ) -
        κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤ K := by
  rcases z0_dichotomy (r := r) hd hc with hno | ⟨z₀, hz₀, h₀, hmin⟩
  · refine ⟨0, u, le_refl _, fun N => ?_⟩
    have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)) ⊆
        Icc 1 u := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1.1, ?_⟩
      by_contra hlt
      push_neg at hlt
      obtain ⟨m, hm⟩ := hn.2
      have hvn : u < v * n := by nlinarith
      apply hno (v * n - u) (by omega)
      refine ⟨m.natAbs, ?_⟩
      have hcast : (((v * n - u : ℕ)) : ℤ) = (v : ℤ) * n - u := by push_cast [Nat.cast_sub hvn.le]; ring
      have := congrArg Int.natAbs hm
      rw [Int.natAbs_pow, ← hcast] at this
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    have hcard := card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
    simp only [zero_mul, sub_zero, Nat.abs_cast]
    exact_mod_cast hcard
  · obtain ⟨κ, K, hκ, hK⟩ := atlas_radical (u := u) hd hc hz₀ hv h₀ hmin (fun _ => 1) (Z := 0)
      (fun N => by simp)
    refine ⟨κ, K, hκ, fun N => ?_⟩
    simpa using hK N

/-- The count of `C (V n - u)^r` for an integer coefficient `C ≠ 0` of either sign. -/
theorem int_coeff_count {C : ℤ} {r d u V : ℕ} (hd : 0 < d) (hC : C ≠ 0) (hV : 0 < V) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - u) ^ r)) : ℝ) -
        κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤ K := by
  rcases lt_or_gt_of_ne hC with hneg | hpos
  · rcases Nat.even_or_odd d with hev | hodd
    · -- even `d`, `C < 0`: only `V n ≤ u` can hit
      refine ⟨0, u, le_refl _, fun N => ?_⟩
      have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - u) ^ r)) ⊆
          Icc 1 u := by
        intro n hn
        simp only [mem_filter, mem_Icc] at hn ⊢
        refine ⟨hn.1.1, ?_⟩
        by_contra hlt
        push_neg at hlt
        obtain ⟨m, hm⟩ := hn.2
        have hz : (0 : ℤ) < (V : ℤ) * n - u := by
          have hn1 : (n : ℤ) ≤ V * n := by nlinarith
          linarith [hn1]
        have h1 : C * ((V : ℤ) * n - u) ^ r < 0 := mul_neg_of_neg_of_pos hneg (pow_pos hz r)
        have h2 : 0 ≤ m ^ d := Even.pow_nonneg hev m
        linarith
      have hcard := card_le_card hsub
      simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
      simp only [zero_mul, sub_zero, Nat.abs_cast]
      exact_mod_cast hcard
    · -- odd `d`: flip the sign
      obtain ⟨κ, K, hκ, hK⟩ := nat_radical_count (c := C.natAbs) (r := r) (u := u) hd
        (Int.natAbs_ne_zero.mpr hC) hV
      refine ⟨κ, K, hκ, fun N => ?_⟩
      have e : ((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - u) ^ r)) =
          ((Icc 1 N).filter fun n : ℕ =>
            IsHit d ((C.natAbs : ℤ) * ((V : ℤ) * n - u) ^ r)) := by
        apply filter_congr
        intro n _
        have hC' : (C.natAbs : ℤ) = -C := by rw [Int.natCast_natAbs, abs_of_neg hneg]
        rw [hC']
        constructor
        · rintro ⟨m, hm⟩; exact ⟨-m, by rw [Odd.neg_pow hodd, ← hm]; ring⟩
        · rintro ⟨m, hm⟩
          exact ⟨-m, by rw [Odd.neg_pow hodd, ← hm]; ring⟩
      rw [e]; exact hK N
  · obtain ⟨κ, K, hκ, hK⟩ := nat_radical_count (c := C.natAbs) (r := r) (u := u) hd
      (Int.natAbs_ne_zero.mpr hC) hV
    refine ⟨κ, K, hκ, fun N => ?_⟩
    have hC' : (C.natAbs : ℤ) = C := by rw [Int.natCast_natAbs, abs_of_pos hpos]
    simpa [hC'] using hK N

/-- The count of `C (V n - U)^r` for an arbitrary integer shift `U`. -/
theorem int_count {C U : ℤ} {r d V : ℕ} (hd : 0 < d) (hC : C ≠ 0) (hV : 0 < V) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - U) ^ r)) : ℝ) -
        κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤ K := by
  set k := U.natAbs
  set u := (U + V * k).toNat
  have hu : (u : ℤ) = U + V * k := by
    apply Int.toNat_of_nonneg
    have hk : (k : ℤ) = |U| := Int.natCast_natAbs U
    rw [hk]
    nlinarith [neg_abs_le U, abs_nonneg U]
  obtain ⟨κ, K, hκ, hK⟩ := int_coeff_count (C := C) (r := r) (u := u) hd hC hV
  refine ⟨κ, K + k, hκ, fun N => ?_⟩
  set Q : ℕ → Prop := fun m => IsHit d (C * ((V : ℤ) * m - u) ^ r)
  have e : ((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - U) ^ r)) =
      ((Icc 1 N).filter fun n => Q (n + k)) := by
    apply filter_congr
    intro n _
    simp only [Q]
    have : ((V : ℤ) * n - U) = (V : ℤ) * ((n + k : ℕ) : ℤ) - u := by push_cast; rw [hu]; ring
    rw [this]
  rw [e]
  obtain ⟨s1, s2⟩ := shift_count Q k N
  have hQ := hK N
  have s1' : (#((Icc 1 N).filter fun n => Q (n + k)) : ℝ) ≤ #((Icc 1 N).filter Q) + k := by
    exact_mod_cast s1
  have s2' : (#((Icc 1 N).filter Q) : ℝ) ≤ #((Icc 1 N).filter fun n => Q (n + k)) + k := by
    exact_mod_cast s2
  rw [abs_le] at hQ ⊢
  constructor <;> linarith [hQ.1, hQ.2]

/-- **Theorem B as a count.**  If `F ∈ ℤ[X]` has exactly one bad rational layer for the exponent
`d ≥ 2`, then `A(N) = κ N^{1/t} + O(1)` with `κ ≥ 0` and `t = d / gcd(r, d)`, `2 ≤ t ∣ d`; the
exceptional zeros of `F`, both signs and all shifts are included. -/
theorem Decomposition.radical_count {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {d : ℕ} (hd : 2 ≤ d)
    (hbad : Y.badDegree d = 1) :
    ∃ t : ℕ, 2 ≤ t ∧ t ∣ d ∧ ∃ κ K : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d (F.eval (n : ℤ))) : ℝ) -
        κ * (N : ℝ) ^ ((t : ℝ)⁻¹)| ≤ K := by
  obtain ⟨u, v, hv, r, hr, hrd, hiff⟩ := Y.integer_radical_reduction hd hbad
  have hFq : F.map (Int.castRingHom ℚ) ≠ 0 := Y.ne_zero
  have hF : F ≠ 0 := by rintro rfl; exact hFq (Polynomial.map_zero _)
  have hC : F.leadingCoeff * v ^ (d - r) ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ hv.ne')
  set V := v.toNat
  have hV : (V : ℤ) = v := Int.toNat_of_nonneg hv.le
  have hV0 : 0 < V := by omega
  obtain ⟨κ, K, hκ, hK⟩ := int_count (C := F.leadingCoeff * v ^ (d - r)) (U := u) (r := r) (d := d) (V := V)
    (by omega) hC hV0
  have hg : Nat.gcd r d < d := lt_of_le_of_lt (Nat.gcd_le_left d hr) hrd
  have hgd : Nat.gcd r d ∣ d := Nat.gcd_dvd_right r d
  refine ⟨d / Nat.gcd r d, ?_, Nat.div_dvd_of_dvd hgd, κ, K + F.natDegree, hκ, fun N => ?_⟩
  · have hg0 : 0 < Nat.gcd r d := Nat.gcd_pos_of_pos_left d hr
    obtain ⟨m, hm⟩ := hgd
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push_neg at hlt
      interval_cases m <;> omega
    exact (Nat.le_div_iff_mul_le hg0).mpr (by nlinarith [hm])
  set Q : ℕ → Prop := fun n => IsHit d (F.leadingCoeff * v ^ (d - r) * ((V : ℤ) * n - u) ^ r)
  have e : ((Icc 1 N).filter fun n : ℕ => IsHit d (F.eval (n : ℤ))) =
      ((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ Q n) := by
    apply filter_congr
    intro n _
    rw [hiff n]
    simp only [Q, hV]
  rw [e]
  obtain ⟨c1, c2⟩ := count_or (fun n : ℕ => F.eval (n : ℤ) = 0) Q N F.natDegree
    (card_zeros_le F hF N)
  have hQ := hK N
  have c1' : (#((Icc 1 N).filter Q) : ℝ) ≤
      #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ Q n) := by exact_mod_cast c1
  have c2' : (#((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ Q n) : ℝ) ≤
      #((Icc 1 N).filter Q) + F.natDegree := by exact_mod_cast c2
  rw [abs_le] at hQ ⊢
  constructor <;> linarith [hQ.1, hQ.2]

end PerfectPower.RationalYun
