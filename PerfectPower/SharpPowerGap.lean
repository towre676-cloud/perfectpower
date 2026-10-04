import PerfectPower.ExceptionalPowerSearch
import Mathlib
namespace PerfectPower.SharpPowerGap
/-- Factoring nonnegative powers controls the base gap by either base's power. -/
theorem increasing_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a)
    (d : ℕ) (hd : 1 ≤ d) : (a-b)*b^(d-1) ≤ a^d-b^d := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    have hm := mul_le_mul_of_nonneg_left ih hb
    have he : 0 ≤ (a-b)*a^d := mul_nonneg (sub_nonneg.mpr hab) (pow_nonneg ha d)
    have hi : d-1+1=d := by omega
    rw [mul_left_comm b,← pow_succ',hi] at hm
    simp only [Nat.add_sub_cancel,pow_succ]
    nlinarith

theorem decreasing_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    (d : ℕ) (hd : 1 ≤ d) : (b-a)*b^(d-1) ≤ b^d-a^d := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    have hm := mul_le_mul_of_nonneg_left ih hb
    have he : 0 ≤ (b-a)*a^d := mul_nonneg (sub_nonneg.mpr hab) (pow_nonneg ha d)
    have hi : d-1+1=d := by omega
    rw [mul_left_comm b,← pow_succ',hi] at hm
    simp only [Nat.add_sub_cancel,pow_succ]
    nlinarith

theorem magnitude_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) (hd : 1 ≤ d) :
    |a-b| *b^(d-1) ≤ |a^d-b^d| := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hb h d))]
    exact increasing_gap a b ha hb h d hd
  · rw [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ ha h d))]
    simpa only [neg_sub] using decreasing_gap a b ha hb h d hd

/-- A checked rational-grid gap cannot contain a different integer numerator. -/
theorem numerator_forced (D z p : ℤ) (hD : 0 < D)
    (h : |(z:ℝ)-(p:ℝ)/D| < 1/(D:ℝ)) : D*z=p := by
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  have hg : |(D:ℝ)*z-p|<1 := by
    have he : (D:ℝ)*z-p=(D:ℝ)*((z:ℝ)-(p:ℝ)/D) := by field_simp;ring
    rw [he,abs_mul,abs_of_pos hDr]
    simpa only [mul_comm] using (lt_div_iff₀ hDr).mp h
  apply ExceptionalPowerSearch.integer_gap
  exact_mod_cast hg
/-- The nonnegative sign branch of the sharp rational power-gap exclusion. -/
theorem nonnegative_tail (D z p : ℤ) (hD : 0 < D) (hz : 0 ≤ (z:ℝ))
    (hp : 0 ≤ (p:ℝ)/D) (d : ℕ) (hd : 1 ≤ d) (R : ℝ)
    (hidentity : (z:ℝ)^d=((p:ℝ)/D)^d+R)
    (hsmall : (D:ℝ)*|R| < ((p:ℝ)/D)^(d-1)) : R=0 := by
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  have hg := magnitude_gap (z:ℝ) ((p:ℝ)/D) hz hp d hd
  have he : (z:ℝ)^d-((p:ℝ)/D)^d=R := by linarith
  rw [he] at hg
  have hm := mul_le_mul_of_nonneg_left hg hDr.le
  have hpow : 0 < ((p:ℝ)/D)^(d-1) := by
    have := mul_nonneg hDr.le (abs_nonneg R)
    linarith
  have hc : |(z:ℝ)-(p:ℝ)/D| *(D:ℝ)<1 := by nlinarith
  have hi := numerator_forced D z p hD ((lt_div_iff₀ hDr).mpr hc)
  have hq : (p:ℝ)/D=(z:ℝ) := by
    rw [← hi]
    push_cast
    field_simp
  rw [hq] at hidentity
  linarith

end PerfectPower.SharpPowerGap
