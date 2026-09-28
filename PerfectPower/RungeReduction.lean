import PerfectPower.Pell

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### Theorem R, pointwise and uniform (integer form)

Research notes, Theorem R.  With `P = D·Q` and `R' = D^d F - P^d = D^d R`, the Runge bound
`|D y - P(n)| ≤ D |R(n)| / |Q(n)|^(d-1)` reads `|D y - P(n)| ≤ |R'(n)| / |P(n)|^(d-1)`, so every
hypothesis below is an inequality between integers. -/

/-- Real-variable core: if `m^d = x^d + r`, `x ≠ 0`, and (for odd `d`) `|r| < |x|^d`, then some
`y ∈ {m, -m}` with `y^d = m^d` satisfies `|y - x| · |x|^(d-1) ≤ |r|`. -/
lemma pow_diff_bound' {d : ℕ} (hd : 2 ≤ d) (m : ℤ) (x r : ℝ) (hx : x ≠ 0)
    (hodd : Odd d → |r| < |x| ^ d) (h : (m : ℝ) ^ d = x ^ d + r) :
    ∃ y : ℤ, y ^ d = m ^ d ∧ |(y : ℝ) - x| * |x| ^ (d - 1) ≤ |r| := by
  have hxd : 0 < |x| ^ d := pow_pos (abs_pos.mpr hx) d
  have hyex : ∃ y : ℤ, y ^ d = m ^ d ∧ 0 ≤ (y : ℝ) * x := by
    by_cases hmx : 0 ≤ (m : ℝ) * x
    · exact ⟨m, rfl, hmx⟩
    · push_neg at hmx
      rcases Nat.even_or_odd d with heven | hodd'
      · exact ⟨-m, heven.neg_pow m, by push_cast; linarith⟩
      · exfalso
        have h1 : ((m : ℝ) * x) ^ d < 0 := hodd'.pow_neg hmx
        rw [mul_pow] at h1
        have hr : r = (m : ℝ) ^ d - x ^ d := by linarith
        have hlt := hodd hodd'
        rw [hr] at hlt
        -- m^d and x^d have opposite signs, so |m^d - x^d| ≥ |x^d|
        have hge : |x ^ d| ≤ |(m : ℝ) ^ d - x ^ d| := by
          rcases lt_or_le 0 (x ^ d) with hxp | hxn
          · have hm : (m : ℝ) ^ d ≤ 0 := by
              by_contra hc; push_neg at hc; nlinarith
            rw [abs_of_pos hxp, abs_of_nonpos (by linarith)]; linarith
          · have hm : 0 ≤ (m : ℝ) ^ d := by
              by_contra hc; push_neg at hc; nlinarith
            rw [abs_of_nonpos hxn, abs_of_nonneg (by linarith)]; linarith
        rw [abs_pow] at hge
        linarith
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
  have hpd : |x| * |x| ^ (d - 1) = |x| ^ d := by
    rw [← pow_succ']; congr 1; omega
  have key := abs_sub_one_le_abs_pow_sub_one ht (d := d) (by omega)
  rw [hyt, hrr, show t * x - x = (t - 1) * x by ring]
  simp only [abs_mul, abs_pow]
  calc |t - 1| * |x| * |x| ^ (d - 1) = |t - 1| * |x| ^ d := by rw [mul_assoc, hpd]
    _ ≤ |t ^ d - 1| * |x| ^ d := mul_le_mul_of_nonneg_right key hxd.le
    _ = |x| ^ d * |t ^ d - 1| := mul_comm _ _

/-- **Theorem R, pointwise.**  Let `p = P(n) ≠ 0`, `R' = D^d F(n) - p^d`, and suppose
`|R'| < (T + 1) |p|^(d-1)` and, for odd `d`, `|R'| < |p|^d`.  If `F(n)` is a `d`-th power then
`D^d F(n) = (p + t)^d` for some integer `|t| ≤ T`. -/
theorem runge_pointwise {d : ℕ} (hd : 2 ≤ d) {Fn p D : ℤ} {T : ℕ} (hp : p ≠ 0)
    (hodd : Odd d → |D ^ d * Fn - p ^ d| < |p| ^ d)
    (hsmall : |D ^ d * Fn - p ^ d| < (T + 1) * |p| ^ (d - 1))
    (hit : IsHit d Fn) :
    ∃ t : ℤ, |t| ≤ T ∧ D ^ d * Fn = (p + t) ^ d := by
  obtain ⟨m, hm⟩ := hit
  set r : ℤ := D ^ d * Fn - p ^ d with hr
  have hreal : ((D * m : ℤ) : ℝ) ^ d = (p : ℝ) ^ d + (r : ℝ) := by
    push_cast [hr, hm]; ring
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  obtain ⟨y, hyd, hyb⟩ := pow_diff_bound' hd (D * m) (p : ℝ) (r : ℝ) hpR
    (fun ho => by have := hodd ho; rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast this)
    hreal
  refine ⟨y - p, ?_, ?_⟩
  · -- |y - p| · |p|^(d-1) ≤ |r| < (T+1) |p|^(d-1)  ⟹  |y - p| < T + 1
    have hpp : (0 : ℝ) < |(p : ℝ)| ^ (d - 1) := pow_pos (abs_pos.mpr hpR) _
    have h1 : |((y - p : ℤ) : ℝ)| * |(p : ℝ)| ^ (d - 1) < ((T : ℝ) + 1) * |(p : ℝ)| ^ (d - 1) := by
      have hs : ((|r| : ℤ) : ℝ) < (((T + 1 : ℤ) * |p| ^ (d - 1) : ℤ) : ℝ) := by exact_mod_cast hsmall
      push_cast at hs hyb ⊢
      linarith
    have h2 : |((y - p : ℤ) : ℝ)| < (T : ℝ) + 1 := lt_of_mul_lt_mul_right h1 hpp.le
    have h3 : (|y - p| : ℤ) < (T : ℤ) + 1 := by
      have : ((|y - p| : ℤ) : ℝ) < (((T : ℤ) + 1 : ℤ) : ℝ) := by push_cast at h2 ⊢; exact h2
      exact_mod_cast this
    omega
  · rw [show p + (y - p) = y by ring, hyd, hm]; ring

/-- **Theorem R, uniform.**  If the two Runge inequalities hold at every `n ≥ x0`, then every hit
`n ≥ x0` of `F` is a root of `G_t = D^d F - (P + t)^d` for some integer `|t| ≤ T`. -/
theorem runge_uniform {d : ℕ} (hd : 2 ≤ d) {F P : ℤ[X]} {D : ℤ} {T x0 : ℕ}
    (hP : ∀ n : ℕ, x0 ≤ n → P.eval (n : ℤ) ≠ 0)
    (hodd : ∀ n : ℕ, x0 ≤ n → Odd d →
      |D ^ d * F.eval (n : ℤ) - (P.eval (n : ℤ)) ^ d| < |P.eval (n : ℤ)| ^ d)
    (hsmall : ∀ n : ℕ, x0 ≤ n →
      |D ^ d * F.eval (n : ℤ) - (P.eval (n : ℤ)) ^ d| < (T + 1) * |P.eval (n : ℤ)| ^ (d - 1)) :
    ∀ n ∈ hitSet (fun n => F.eval (n : ℤ)) d 0, x0 ≤ n →
      ∃ t : ℤ, |t| ≤ T ∧ (C (D ^ d) * F - (P + C t) ^ d).eval (n : ℤ) = 0 := by
  intro n hn hx
  obtain ⟨-, hit⟩ := hn
  simp only [add_zero] at hit
  obtain ⟨t, ht, heq⟩ := runge_pointwise hd (hP n hx) (hodd n hx) (hsmall n hx) hit
  exact ⟨t, ht, by simp [eval_sub, eval_mul, eval_pow, eval_add, heq]⟩

/-- Consequence: under the uniform Runge inequalities, if every `G_t`, `|t| ≤ T`, is nonzero,
the hit set is finite. -/
theorem runge_finite {d : ℕ} (hd : 2 ≤ d) {F P : ℤ[X]} {D : ℤ} {T x0 : ℕ}
    (hP : ∀ n : ℕ, x0 ≤ n → P.eval (n : ℤ) ≠ 0)
    (hodd : ∀ n : ℕ, x0 ≤ n → Odd d →
      |D ^ d * F.eval (n : ℤ) - (P.eval (n : ℤ)) ^ d| < |P.eval (n : ℤ)| ^ d)
    (hsmall : ∀ n : ℕ, x0 ≤ n →
      |D ^ d * F.eval (n : ℤ) - (P.eval (n : ℤ)) ^ d| < (T + 1) * |P.eval (n : ℤ)| ^ (d - 1))
    (hG : ∀ t : ℤ, |t| ≤ T → C (D ^ d) * F - (P + C t) ^ d ≠ 0) :
    (hitSet (fun n => F.eval (n : ℤ)) d 0).Finite := by
  have hfinT : (Finset.Icc (-(T : ℤ)) T : Set ℤ).Finite := Finset.finite_toSet _
  have hroots : ∀ t ∈ (Finset.Icc (-(T : ℤ)) T : Set ℤ),
      {z : ℤ | (C (D ^ d) * F - (P + C t) ^ d).IsRoot z}.Finite := by
    intro t ht
    have ht' : |t| ≤ T := by
      simp only [Finset.coe_Icc, Set.mem_Icc] at ht; exact abs_le.mpr ht
    exact Polynomial.finite_setOf_isRoot (hG t ht')
  have hU := hfinT.biUnion hroots
  refine ((Set.finite_Iio x0).union (hU.preimage Nat.cast_injective.injOn)).subset ?_
  intro n hn
  by_cases hx : x0 ≤ n
  · right
    obtain ⟨t, ht, hz⟩ := runge_uniform hd hP hodd hsmall n hn hx
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Finset.coe_Icc, Set.mem_Icc]
    exact ⟨t, abs_le.mp ht, hz⟩
  · left; exact not_le.mp hx

end PerfectPower

namespace PerfectPower

/-- **Theorem P over `ℚ[X]`.**  If `F = c · G^d` with `G ∈ ℚ[X]` nonzero and `c ∈ ℤ` not an integer
`d`-th power, then `F` has only finitely many hits. -/
theorem power_type_finite {d : ℕ} (hd : 2 ≤ d) {F : ℤ[X]} {G : ℚ[X]} {c : ℤ}
    (hc : ¬ ∃ b : ℤ, c = b ^ d) (hG : G ≠ 0)
    (hFG : F.map (Int.castRingHom ℚ) = C (c : ℚ) * G ^ d) :
    (hitSet (fun n => F.eval (n : ℤ)) d 0).Finite := by
  obtain ⟨D, hD, P, hP⟩ := exists_denominator G
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hPne : P ≠ 0 := by
    rintro rfl
    have : C (D : ℚ) * G = 0 := by simpa using hP
    rcases mul_eq_zero.mp this with h | h
    · exact hD (by exact_mod_cast (Polynomial.C_eq_zero.mp h))
    · exact hG h
  refine twisted_finite hd hc (D := D) (H := P) ?_ hPne
  apply Polynomial.map_injective _ hinj
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, hFG, ← hP]
  simp only [eq_intCast, Int.cast_pow, mul_pow, ← C_pow]
  ring

end PerfectPower
