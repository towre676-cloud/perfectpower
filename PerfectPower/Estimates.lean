import PerfectPower.Rigid

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-- Discreteness: a nonzero element of `(1/D)ℤ` has absolute value at least `1/|D|`. -/
lemma abs_sub_ge_inv (D P y : ℤ) (hD : D ≠ 0) (h : (y : ℝ) - (P : ℝ) / D ≠ 0) :
    1 / |(D : ℝ)| ≤ |(y : ℝ) - (P : ℝ) / D| := by
  have hDq : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have e : (y : ℝ) - (P : ℝ) / D = ((D * y - P : ℤ) : ℝ) / D := by
    push_cast; field_simp; ring
  have hn : D * y - P ≠ 0 := by
    intro h0; apply h; rw [e, h0]; simp
  rw [e, abs_div]
  have h1 : (1 : ℝ) ≤ |((D * y - P : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  exact div_le_div_of_nonneg_right h1 (abs_nonneg _)

/-- `D * Q(n) = P(n)` over `ℚ`. -/
lemma Qeval_mul_D {Q : ℚ[X]} {D : ℤ} {P : ℤ[X]}
    (hP : C (D : ℚ) * Q = P.map (Int.castRingHom ℚ)) (n : ℕ) :
    (D : ℚ) * Q.eval (n : ℚ) = ((P.eval (n : ℤ) : ℤ) : ℚ) := by
  have := congrArg (Polynomial.eval (n : ℚ)) hP
  simpa [Polynomial.eval_intCast_map] using this

/-- Evaluation commutes with the cast `ℚ → ℝ`. -/
lemma eval_cast_real (P : ℚ[X]) (n : ℕ) :
    ((P.eval (n : ℚ) : ℚ) : ℝ) = (P.map (Rat.castHom ℝ)).eval (n : ℝ) := by
  rw [eval_map]
  simp

lemma abs_sub_one_le_abs_pow_sub_one {t : ℝ} (ht : 0 ≤ t) {d : ℕ} (hd : d ≠ 0) :
    |t - 1| ≤ |t ^ d - 1| := by
  rcases le_total 1 t with h | h
  · have := le_self_pow₀ h hd
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · have := pow_le_of_le_one ht h hd
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- For `R ≠ 0` with `deg R < deg Q^(d-1)`, eventually in `n`: `Q(n) ≠ 0`, `R(n) ≠ 0`,
`|R(n)| ≤ |Q(n)|^d / 2`, and `|R(n)| / |Q(n)|^(d-1) < ε`. -/
lemma analytic_eventually {d : ℕ} (hd : 2 ≤ d) (Q R : ℚ[X]) (hR : R ≠ 0)
    (hdeg : R.degree < (Q ^ (d - 1)).degree) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((Q.eval (n : ℚ) : ℚ) : ℝ) ≠ 0 ∧ 0 < |((R.eval (n : ℚ) : ℚ) : ℝ)| ∧
      |((R.eval (n : ℚ) : ℚ) : ℝ)| ≤ |((Q.eval (n : ℚ) : ℚ) : ℝ)| ^ d / 2 ∧
      |((R.eval (n : ℚ) : ℚ) : ℝ)| / |((Q.eval (n : ℚ) : ℚ) : ℝ)| ^ (d - 1) < ε := by
  have hnd : 0 < Q.natDegree := by
    have h1 := natDegree_lt_natDegree hR hdeg
    rw [natDegree_pow] at h1
    rcases Nat.eq_zero_or_pos Q.natDegree with h0 | h0
    · rw [h0, mul_zero] at h1; omega
    · exact h0
  have hf : Function.Injective (Rat.castHom ℝ) := (Rat.castHom ℝ).injective
  set Qr : ℝ[X] := Q.map (Rat.castHom ℝ) with hQr
  set Rr : ℝ[X] := R.map (Rat.castHom ℝ) with hRr
  have hQrdeg : 0 < Qr.degree := by
    rw [hQr, degree_map]; exact natDegree_pos_iff_degree_pos.mp hnd
  have hdeg' : Rr.degree < (Qr ^ (d - 1)).degree := by
    rw [hRr, hQr, ← Polynomial.map_pow, degree_map, degree_map]; exact hdeg
  have hRr0 : Rr ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hR
  have h1 := Polynomial.div_tendsto_zero_of_degree_lt Rr (Qr ^ (d - 1)) hdeg'
  have h1' : Tendsto (fun x : ℝ => |Rr.eval x| / |Qr.eval x| ^ (d - 1)) atTop (𝓝 0) := by
    have := h1.abs
    simpa [abs_div, eval_pow, abs_pow] using this
  have hbig := Polynomial.abs_tendsto_atTop Qr hQrdeg
  obtain ⟨B, hB⟩ := (Polynomial.finite_setOf_isRoot hRr0).bddAbove
  have e1 := (tendsto_order.1 h1').2 (min ε 1) (lt_min hε one_pos)
  have e2 := hbig.eventually_ge_atTop 2
  have e3 := eventually_gt_atTop B
  have hev : ∀ᶠ x : ℝ in atTop, Qr.eval x ≠ 0 ∧ 0 < |Rr.eval x| ∧
      |Rr.eval x| ≤ |Qr.eval x| ^ d / 2 ∧ |Rr.eval x| / |Qr.eval x| ^ (d - 1) < ε := by
    filter_upwards [e1, e2, e3] with x h1x h2x h3x
    have hQpos : 0 < |Qr.eval x| := by linarith
    have hpow : 0 < |Qr.eval x| ^ (d - 1) := pow_pos hQpos _
    have hRne : Rr.eval x ≠ 0 := fun h0 => by
      have : x ≤ B := hB (show x ∈ {x | Rr.IsRoot x} from h0)
      linarith
    refine ⟨abs_pos.mp hQpos, abs_pos.mpr hRne, ?_, lt_of_lt_of_le h1x (min_le_left _ _)⟩
    have h1a : |Rr.eval x| / |Qr.eval x| ^ (d - 1) < 1 := lt_of_lt_of_le h1x (min_le_right _ _)
    have h1b : |Rr.eval x| < |Qr.eval x| ^ (d - 1) := by
      rwa [div_lt_one hpow] at h1a
    have hpd : |Qr.eval x| ^ d = |Qr.eval x| * |Qr.eval x| ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpd]; nlinarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev] with n hn
  rw [eval_cast_real Q n, eval_cast_real R n]
  exact hn

/-- If `m^d = x^d + r` with `|r| ≤ |x|^d/2`, `x ≠ 0`, then for `y = m` or `y = -m`
(same `d`-th power), `|y - x| ≤ |r| / |x|^(d-1)`. -/
lemma pow_diff_bound {d : ℕ} (hd : 2 ≤ d) (m : ℤ) (x r : ℝ) (hx : x ≠ 0)
    (hr : |r| ≤ |x| ^ d / 2) (h : (m : ℝ) ^ d = x ^ d + r) :
    ∃ y : ℤ, y ^ d = m ^ d ∧ |(y : ℝ) - x| ≤ |r| / |x| ^ (d - 1) := by
  have hxd : 0 < |x| ^ d := pow_pos (abs_pos.mpr hx) d
  have hxd0 : x ^ d ≠ 0 := pow_ne_zero d hx
  have hxpos : 0 < (x ^ d) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hxd0))
  have hyex : ∃ y : ℤ, y ^ d = m ^ d ∧ 0 ≤ (y : ℝ) * x := by
    by_cases hmx : 0 ≤ (m : ℝ) * x
    · exact ⟨m, rfl, hmx⟩
    · push_neg at hmx
      have heven : Even d := by
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        have h1 : ((m : ℝ) * x) ^ d < 0 := hodd.pow_neg hmx
        rw [mul_pow] at h1
        have h2 : |r| ^ 2 ≤ (|x| ^ d / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
        rw [sq_abs] at h2
        have e : (|x| ^ d) ^ 2 = (x ^ d) ^ 2 := by rw [← abs_pow, sq_abs]
        have hrr : r = (m : ℝ) ^ d - x ^ d := by linarith
        rw [hrr] at h2
        nlinarith [sq_nonneg ((m : ℝ) ^ d), e, h2, h1, hxpos]
      exact ⟨-m, heven.neg_pow m, by push_cast; linarith⟩
  obtain ⟨y, hyd, hyx⟩ := hyex
  refine ⟨y, hyd, ?_⟩
  have hy' : (y : ℝ) ^ d = (m : ℝ) ^ d := by exact_mod_cast hyd
  obtain ⟨t, ht, hyt⟩ : ∃ t : ℝ, 0 ≤ t ∧ (y : ℝ) = t * x := by
    refine ⟨(y : ℝ) / x, ?_, by field_simp⟩
    have : (y : ℝ) / x = ((y : ℝ) * x) / x ^ 2 := by field_simp; ring
    rw [this]; exact div_nonneg hyx (sq_nonneg _)
  have hrr : r = x ^ d * (t ^ d - 1) := by
    have h' := h
    rw [← hy', hyt, mul_pow] at h'
    linear_combination (-1 : ℝ) * h'
  have hxd1 : 0 < |x| ^ (d - 1) := pow_pos (abs_pos.mpr hx) _
  rw [le_div_iff₀ hxd1]
  have e1 : t * x - x = (t - 1) * x := by ring
  have hpd : |x| * |x| ^ (d - 1) = |x| ^ d := by
    rw [← pow_succ']; congr 1; omega
  have key := abs_sub_one_le_abs_pow_sub_one ht (d := d) (by omega)
  rw [hyt, hrr, e1]
  simp only [abs_mul, abs_pow]
  calc |t - 1| * |x| * |x| ^ (d - 1) = |t - 1| * |x| ^ d := by rw [mul_assoc, hpd]
    _ ≤ |t ^ d - 1| * |x| ^ d := mul_le_mul_of_nonneg_right key hxd.le
    _ = |x| ^ d * |t ^ d - 1| := mul_comm _ _

/-- Eventually no hits when the truncated-root remainder is nonzero. -/
theorem eventually_no_hit {d : ℕ} (hd : 2 ≤ d) {F : ℤ[X]} {Q : ℚ[X]}
    (hQ : (F.map (Int.castRingHom ℚ) - Q ^ d).degree < (Q ^ (d - 1)).degree)
    (hne : F.map (Int.castRingHom ℚ) ≠ Q ^ d) :
    ∀ᶠ n : ℕ in atTop, ¬ IsHit d (F.eval (n : ℤ)) := by
  obtain ⟨D, hD, P, hP⟩ := exists_denominator Q
  have hR : F.map (Int.castRingHom ℚ) - Q ^ d ≠ 0 := sub_ne_zero.mpr hne
  have hDpos : (0 : ℝ) < |(D : ℝ)| := abs_pos.mpr (by exact_mod_cast hD)
  have hE := analytic_eventually hd Q _ hR hQ (1 / (2 * |(D : ℝ)|)) (by positivity)
  filter_upwards [hE] with n hn
  rintro ⟨m, hm⟩
  obtain ⟨hx0, hr0, hrx, hsmall⟩ := hn
  have hrq : (F.map (Int.castRingHom ℚ) - Q ^ d).eval (n : ℚ)
      = ((m ^ d : ℤ) : ℚ) - (Q.eval (n : ℚ)) ^ d := by
    rw [eval_sub, eval_pow, ← hm]; simp [Polynomial.eval_intCast_map]
  have hy : (m : ℝ) ^ d = ((Q.eval (n : ℚ) : ℚ) : ℝ) ^ d
      + (((F.map (Int.castRingHom ℚ) - Q ^ d).eval (n : ℚ) : ℚ) : ℝ) := by
    rw [hrq]; push_cast; ring
  have hxD : ((Q.eval (n : ℚ) : ℚ) : ℝ) = ((P.eval (n : ℤ) : ℤ) : ℝ) / D := by
    have h := congrArg (fun z : ℚ => (z : ℝ)) (Qeval_mul_D hP n)
    have hDq : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    push_cast at h
    field_simp
    linarith [h]
  obtain ⟨y, hyd, hyb⟩ := pow_diff_bound hd m _ _ hx0 hrx hy
  have hy' : (y : ℝ) ^ d = (m : ℝ) ^ d := by exact_mod_cast hyd
  have hyx : (y : ℝ) - ((Q.eval (n : ℚ) : ℚ) : ℝ) ≠ 0 := by
    intro h0
    have hyeq : (y : ℝ) = ((Q.eval (n : ℚ) : ℚ) : ℝ) := by linarith
    rw [hyeq] at hy'
    have : (((F.map (Int.castRingHom ℚ) - Q ^ d).eval (n : ℚ) : ℚ) : ℝ) = 0 := by
      linarith [hy, hy']
    rw [this] at hr0; simp at hr0
  have hlow := abs_sub_ge_inv D (P.eval (n : ℤ)) y hD (by rw [← hxD]; exact hyx)
  rw [← hxD] at hlow
  have hup := lt_of_le_of_lt hyb hsmall
  have hcmp : 1 / (2 * |(D : ℝ)|) < 1 / |(D : ℝ)| := by
    rw [div_lt_div_iff₀ (by positivity) hDpos]; nlinarith
  linarith

end PerfectPower
