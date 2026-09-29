import PerfectPower.Continuation.PellPositive

/-!
# Explicit error constants: the radical type

`Decomposition.radical_count` proves `|A(N) - κ N^{1/t}| ≤ K` for some `K`.  Here `K` is explicit.
The atlas bound `2R + (R/v)((u/z₀)^{1/t} + 1) + u` (`radical_asymptotic_int`) is at most
`2v + 2u + 2`, because the residue count satisfies `R ≤ v`, `z₀ ≥ 1` and
`x^{1/t} ≤ x + 1` (`rpow_inv_le`).  Every other case (unsolvable, even `d` with a negative
coefficient) has error at most `u`.  The integer shift adds `|U|` and the zeros of `F` add
`deg F`.

`Decomposition.radical_count_explicit`: for `F` with one bad layer, with the data `(C, U, V, r)`
of the pointwise reduction,

  `|A(N) - κ N^{1/t}| ≤ 2V + 2(U + V|U|) + |U| + 2 + deg F`   for every `N`.
-/

open Finset Polynomial
open scoped Classical

namespace PerfectPower.RationalYun

lemma rpow_inv_le {x : ℝ} (hx : 0 ≤ x) {t : ℕ} (ht : 1 ≤ t) : x ^ ((t : ℝ)⁻¹) ≤ x + 1 := by
  have ht' : (0 : ℝ) < (t : ℝ)⁻¹ := by positivity
  have ht1 : (t : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast ht)
  rcases le_or_lt x 1 with h | h
  · have := Real.rpow_le_one hx h ht'.le
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h.le ht1
    rw [Real.rpow_one] at this
    linarith

/-- The count of `c (v n - u)^r` for natural data, with the explicit error `2v + 2u + 2`. -/
theorem nat_radical_count_explicit {c r d u v : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hv : 0 < v) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)) : ℝ) -
        κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤ 2 * v + 2 * u + 2 := by
  rcases z0_dichotomy (r := r) hd hc with hno | ⟨z₀, hz₀, h₀, hmin⟩
  · refine ⟨0, le_refl _, fun N => ?_⟩
    have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)) ⊆
        Icc 1 u := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1.1, ?_⟩
      by_contra hlt
      push_neg at hlt
      have hvn : u < v * n := lt_of_lt_of_le hlt (Nat.le_mul_of_pos_left n hv)
      obtain ⟨z₀, w, hz₀, h₀', -, -, -⟩ := hit_param hd hc hvn hn.2
      exact hno z₀ hz₀ h₀'
    have hcard := card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
    simp only [zero_mul, sub_zero, Nat.abs_cast]
    have : ((#((Icc 1 N).filter fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r)) : ℕ) :
        ℝ) ≤ u := by exact_mod_cast hcard
    linarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
  · set t := d / Nat.gcd r d
    have ht : 1 ≤ t := Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
    set R := #{w ∈ Icc 1 v | v ∣ z₀ * w ^ t + u}
    refine ⟨(R : ℝ) / v * ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹), by positivity, fun N => ?_⟩
    have h := radical_asymptotic_int (u := u) hd hc hz₀ hv h₀ hmin (fun _ => (1 : ℤ)) (Z := 0)
      (fun N => by simp) N
    simp only [one_pow, mul_one, Nat.cast_zero, add_zero] at h
    refine h.trans ?_
    have hRv : (R : ℝ) ≤ v := by
      have : R ≤ v := by
        calc R ≤ #(Icc 1 v) := card_filter_le _ _
          _ = v := by simp
      exact_mod_cast this
    have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
    have hRv' : (R : ℝ) / v ≤ 1 := (div_le_one hvpos).mpr hRv
    have hz : (1 : ℝ) ≤ z₀ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz₀
    have huz : (u : ℝ) / z₀ ≤ u := div_le_self (Nat.cast_nonneg u) hz
    have hpow := rpow_inv_le (div_nonneg (Nat.cast_nonneg u) (by linarith : (0 : ℝ) ≤ z₀)) ht
    have hA : (0 : ℝ) ≤ ((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1 := by positivity
    have : (R : ℝ) / v * (((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1) ≤ 1 * (u + 2) :=
      mul_le_mul hRv' (by linarith) hA zero_le_one
    linarith

/-- The count of `C (V n - u)^r`, any sign of `C`, with the explicit error `2V + 2u + 2`. -/
theorem int_coeff_count_explicit {C : ℤ} {r d u V : ℕ} (hd : 0 < d) (hC : C ≠ 0) (hV : 0 < V) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - u) ^ r)) : ℝ) -
        κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤ 2 * V + 2 * u + 2 := by
  rcases lt_or_gt_of_ne hC with hneg | hpos
  · rcases Nat.even_or_odd d with hev | hodd
    · refine ⟨0, le_refl _, fun N => ?_⟩
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
          linarith
        have h1 : C * ((V : ℤ) * n - u) ^ r < 0 := mul_neg_of_neg_of_pos hneg (pow_pos hz r)
        have h2 : 0 ≤ m ^ d := Even.pow_nonneg hev m
        linarith
      have hcard := card_le_card hsub
      simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
      simp only [zero_mul, sub_zero, Nat.abs_cast]
      have : ((#((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - u) ^ r)) : ℕ) :
          ℝ) ≤ u := by exact_mod_cast hcard
      linarith [(Nat.cast_nonneg V : (0 : ℝ) ≤ V)]
    · obtain ⟨κ, hκ, hK⟩ := nat_radical_count_explicit (c := C.natAbs) (r := r) (u := u) hd
        (Int.natAbs_ne_zero.mpr hC) hV
      refine ⟨κ, hκ, fun N => ?_⟩
      have e : ((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - u) ^ r)) =
          ((Icc 1 N).filter fun n : ℕ =>
            IsHit d ((C.natAbs : ℤ) * ((V : ℤ) * n - u) ^ r)) := by
        apply filter_congr
        intro n _
        have hC' : (C.natAbs : ℤ) = -C := by rw [Int.natCast_natAbs, abs_of_neg hneg]
        rw [hC']
        constructor
        · rintro ⟨m, hm⟩; exact ⟨-m, by rw [Odd.neg_pow hodd, ← hm]; ring⟩
        · rintro ⟨m, hm⟩; exact ⟨-m, by rw [Odd.neg_pow hodd, ← hm]; ring⟩
      rw [e]; exact hK N
  · obtain ⟨κ, hκ, hK⟩ := nat_radical_count_explicit (c := C.natAbs) (r := r) (u := u) hd
      (Int.natAbs_ne_zero.mpr hC) hV
    refine ⟨κ, hκ, fun N => ?_⟩
    have hC' : (C.natAbs : ℤ) = C := by rw [Int.natCast_natAbs, abs_of_pos hpos]
    simpa [hC'] using hK N

/-- The count of `C (V n - U)^r` for an integer shift `U`, error `2V + 2(U + V|U|) + |U| + 2`. -/
theorem int_count_explicit {C U : ℤ} {r d V : ℕ} (hd : 0 < d) (hC : C ≠ 0) (hV : 0 < V) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |(#((Icc 1 N).filter fun n : ℕ => IsHit d (C * ((V : ℤ) * n - U) ^ r)) : ℝ) -
        κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤
          2 * V + 2 * ((U : ℝ) + V * |U|) + |U| + 2 := by
  set k := U.natAbs
  set u := (U + V * k).toNat
  have hu : (u : ℤ) = U + V * k := by
    apply Int.toNat_of_nonneg
    have hk : (k : ℤ) = |U| := Int.natCast_natAbs U
    rw [hk]
    nlinarith [neg_abs_le U, abs_nonneg U]
  have hk : (k : ℝ) = |U| := by
    have : ((k : ℤ) : ℝ) = ((|U| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
    simpa using this
  have huR : (u : ℝ) = U + V * |U| := by
    have : ((u : ℤ) : ℝ) = ((U + V * k : ℤ) : ℝ) := by rw [hu]
    push_cast at this; rw [← hk]; exact_mod_cast this
  obtain ⟨κ, hκ, hK⟩ := int_coeff_count_explicit (C := C) (r := r) (u := u) hd hC hV
  refine ⟨κ, hκ, fun N => ?_⟩
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
  rw [← huR, ← hk]
  rw [abs_le] at hQ ⊢
  constructor <;> linarith [hQ.1, hQ.2]

/-- **Theorem B with an explicit error constant.**  For `F` with one bad layer, with the data
`(C, U, V, r)` of the pointwise reduction and `t = d / gcd(r, d)`:
`|A(N) - κ N^{1/t}| ≤ 2V + 2(U + V|U|) + |U| + 2 + deg F` for every `N`. -/
theorem Decomposition.radical_count_explicit {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {d : ℕ} (hd : 2 ≤ d)
    (hbad : Y.badDegree d = 1) :
    ∃ C U : ℤ, ∃ V r : ℕ, C ≠ 0 ∧ 0 < V ∧ 0 < r ∧ r < d ∧
      (∀ n : ℤ, IsHit d (F.eval n) ↔ F.eval n = 0 ∨ IsHit d (C * ((V : ℤ) * n - U) ^ r)) ∧
      2 ≤ d / Nat.gcd r d ∧ d / Nat.gcd r d ∣ d ∧
      ∃ κ : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
        |(#((Icc 1 N).filter fun n : ℕ => IsHit d (F.eval (n : ℤ))) : ℝ) -
          κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤
            2 * V + 2 * ((U : ℝ) + V * |U|) + |U| + 2 + F.natDegree := by
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
  have hg0 : 0 < Nat.gcd r d := Nat.gcd_pos_of_pos_left d hr
  have hgd : Nat.gcd r d ∣ d := Nat.gcd_dvd_right r d
  have ht2 : 2 ≤ d / Nat.gcd r d := by
    have hg : Nat.gcd r d < d := lt_of_le_of_lt (Nat.gcd_le_left d hr) hrd
    obtain ⟨m, hm⟩ := hgd
    have hm2 : 2 ≤ m := by
      by_contra hlt; push_neg at hlt
      interval_cases m <;> omega
    exact (Nat.le_div_iff_mul_le hg0).mpr (by nlinarith [hm])
  obtain ⟨κ, hκ, hK⟩ := int_count_explicit (C := F.leadingCoeff * v ^ (d - r)) (U := u) (r := r)
    (d := d) (V := V) (by omega) hC hV0
  refine ⟨_, u, V, r, hC, hV0, hr, hrd, hiff', ht2, Nat.div_dvd_of_dvd hgd, κ, hκ, fun N => ?_⟩
  set Q : ℕ → Prop := fun n => IsHit d (F.leadingCoeff * v ^ (d - r) * ((V : ℤ) * n - u) ^ r)
  have e : ((Icc 1 N).filter fun n : ℕ => IsHit d (F.eval (n : ℤ))) =
      ((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ Q n) := by
    apply filter_congr
    intro n _
    rw [hiff' n]
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
