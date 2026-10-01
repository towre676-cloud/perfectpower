import PerfectPower.UnitGen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Verified rational interval arithmetic with outward rounding

An interval is a pair of rationals; `Mem x A` says the real `x` lies in it.  Every operation has a
soundness lemma, so an interval expression evaluated by the kernel encloses the real expression
it mirrors.  Results are rounded outward to `2^-p` (`rnd`), which keeps the rationals small.

* `logI`: `log` of a positive interval.  `y = 2^m w` with `w ≥ 1` (checked; `m` from bit lengths), and
  `log w = 2 Σ z^{2k+1}/(2k+1)`, `z = (w − 1)/(w + 1) ∈ [0, 1/3)`, with the tail bounded by
  `2 z^{2J+1} / ((2J + 1)(1 − z²))`; `log 2` is the same series at `z = 1/3`.
* `expHi`: an upper bound for `exp r`, `r ≥ 0`: `exp s ≤ 1/(1 − s)` at `s = r/2^m`, squared `m`
  times.
-/

namespace PerfectPower.RatInterval

open Real Finset

/-- An interval of rationals. -/
abbrev I := ℚ × ℚ

/-- `x ∈ [A.1, A.2]`. -/
def Mem (x : ℝ) (A : I) : Prop := (A.1 : ℝ) ≤ x ∧ x ≤ A.2

/-! ### Rounding -/

/-- Round down to the grid `2^-p`. -/
def rdn (p : ℕ) (x : ℚ) : ℚ := ((⌊x * 2 ^ p⌋ : ℤ) : ℚ) / 2 ^ p
/-- Round up to the grid `2^-p`. -/
def rup (p : ℕ) (x : ℚ) : ℚ := ((⌈x * 2 ^ p⌉ : ℤ) : ℚ) / 2 ^ p

lemma rdn_le (p : ℕ) (x : ℚ) : rdn p x ≤ x := by
  unfold rdn
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

lemma le_rup (p : ℕ) (x : ℚ) : x ≤ rup p x := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

lemma rdn_nonneg (p : ℕ) {x : ℚ} (h : 0 ≤ x) : 0 ≤ rdn p x := by
  unfold rdn
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (by positivity)

lemma rdn_le_R (p : ℕ) (x : ℚ) : ((rdn p x : ℚ) : ℝ) ≤ x := by exact_mod_cast rdn_le p x
lemma le_rup_R (p : ℕ) (x : ℚ) : (x : ℝ) ≤ ((rup p x : ℚ) : ℝ) := by exact_mod_cast le_rup p x

/-! ### Interval operations -/

/-- Outward rounding. -/
def rnd (p : ℕ) (A : I) : I := (rdn p A.1, rup p A.2)
/-- A point. -/
def ofQ (q : ℚ) : I := (q, q)
/-- Sum. -/
def add (A B : I) : I := (A.1 + B.1, A.2 + B.2)
/-- Negation. -/
def neg (A : I) : I := (-A.2, -A.1)
/-- Difference. -/
def sub (A B : I) : I := add A (neg B)
/-- Product. -/
def mul (A B : I) : I := (UnitGenProof.imin A.1 A.2 B.1 B.2, UnitGenProof.imax A.1 A.2 B.1 B.2)
/-- Reciprocal (valid when the interval excludes `0`). -/
def inv (A : I) : I := (1 / A.2, 1 / A.1)
/-- Quotient. -/
def div (A B : I) : I := mul A (inv B)
/-- Absolute value. -/
def absI (A : I) : I :=
  if 0 ≤ A.1 then A else if A.2 ≤ 0 then neg A else (0, max (-A.1) A.2)
/-- The interval excludes `0`. -/
def nz (A : I) : Bool := decide (0 < A.1) || decide (A.2 < 0)

lemma mem_rnd {x : ℝ} {A : I} (p : ℕ) (h : Mem x A) : Mem x (rnd p A) :=
  ⟨le_trans (rdn_le_R p _) h.1, le_trans h.2 (le_rup_R p _)⟩

lemma mem_ofQ (q : ℚ) : Mem (q : ℝ) (ofQ q) := ⟨le_rfl, le_rfl⟩

lemma mem_add {x y : ℝ} {A B : I} (hx : Mem x A) (hy : Mem y B) : Mem (x + y) (add A B) := by
  simp only [Mem, add, Rat.cast_add] at *
  exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩

lemma mem_neg {x : ℝ} {A : I} (hx : Mem x A) : Mem (-x) (neg A) := by
  simp only [Mem, neg, Rat.cast_neg] at *
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

lemma mem_sub {x y : ℝ} {A B : I} (hx : Mem x A) (hy : Mem y B) : Mem (x - y) (sub A B) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

lemma mem_mul {x y : ℝ} {A B : I} (hx : Mem x A) (hy : Mem y B) : Mem (x * y) (mul A B) :=
  UnitGenProof.imul_sound hx.1 hx.2 hy.1 hy.2

lemma mem_inv {x : ℝ} {A : I} (hx : Mem x A) (hnz : nz A = true) : Mem x⁻¹ (inv A) := by
  simp only [nz, Bool.or_eq_true, decide_eq_true_eq] at hnz
  obtain ⟨h1, h2⟩ := hx
  simp only [Mem, inv, one_div, Rat.cast_inv]
  rcases hnz with h | h
  · have h' : (0 : ℝ) < A.1 := by exact_mod_cast h
    have hx0 : 0 < x := lt_of_lt_of_le h' h1
    exact ⟨inv_anti₀ hx0 h2, inv_anti₀ h' h1⟩
  · have h' : (A.2 : ℝ) < 0 := by exact_mod_cast h
    have hx0 : x < 0 := lt_of_le_of_lt h2 h'
    constructor
    · rw [inv_le_inv_of_neg h' hx0]; exact h2
    · rw [inv_le_inv_of_neg hx0 (lt_of_le_of_lt h1 (lt_of_le_of_lt h2 h'))]; exact h1

lemma mem_div {x y : ℝ} {A B : I} (hx : Mem x A) (hy : Mem y B) (hnz : nz B = true) :
    Mem (x / y) (div A B) := by
  rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv hy hnz)

lemma mem_abs {x : ℝ} {A : I} (hx : Mem x A) : Mem |x| (absI A) := by
  obtain ⟨h1, h2⟩ := hx
  unfold absI
  split_ifs with ha hb
  · have : (0 : ℝ) ≤ A.1 := by exact_mod_cast ha
    rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
  · have : (A.2 : ℝ) ≤ 0 := by exact_mod_cast hb
    rw [abs_of_nonpos (by linarith)]
    simp only [Mem, neg, Rat.cast_neg]; exact ⟨by linarith, by linarith⟩
  · simp only [Mem, Rat.cast_max, Rat.cast_neg, Rat.cast_zero]
    refine ⟨abs_nonneg _, ?_⟩
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; exact le_trans h2 (le_max_right _ _)
    · rw [abs_of_nonpos h]; exact le_trans (by linarith) (le_max_left _ _)

lemma nz_ne {x : ℝ} {A : I} (hx : Mem x A) (h : nz A = true) : x ≠ 0 := by
  simp only [nz, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have : (0 : ℝ) < A.1 := by exact_mod_cast h
    exact (lt_of_lt_of_le this hx.1).ne'
  · have : (A.2 : ℝ) < 0 := by exact_mod_cast h
    exact (lt_of_le_of_lt hx.2 this).ne

/-! ### The atanh series -/

/-- Lower bounds for `z^{2k+1}`, rounded down. -/
def pwLo (p : ℕ) (z z2 : ℚ) : ℕ → ℚ
  | 0 => z
  | k + 1 => rdn p (pwLo p z z2 k * z2)

/-- Upper bounds for `z^{2k+1}`, rounded up. -/
def pwHi (p : ℕ) (z z2 : ℚ) : ℕ → ℚ
  | 0 => z
  | k + 1 => rup p (pwHi p z z2 k * z2)

lemma pwLo_sound (p : ℕ) {z z2 : ℚ} (hz : 0 ≤ z) (hz2 : 0 ≤ z2) (h2 : (z2 : ℝ) ≤ (z : ℝ) ^ 2) :
    ∀ k, 0 ≤ pwLo p z z2 k ∧ ((pwLo p z z2 k : ℚ) : ℝ) ≤ (z : ℝ) ^ (2 * k + 1)
  | 0 => ⟨hz, by simp [pwLo]⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := pwLo_sound p hz hz2 h2 k
    refine ⟨rdn_nonneg p (mul_nonneg h0 hz2), le_trans (rdn_le_R p _) ?_⟩
    push_cast
    calc ((pwLo p z z2 k : ℚ) : ℝ) * z2 ≤ (z : ℝ) ^ (2 * k + 1) * z ^ 2 :=
          mul_le_mul h1 h2 (by exact_mod_cast hz2) (by positivity)
      _ = (z : ℝ) ^ (2 * (k + 1) + 1) := by ring

lemma pwHi_sound (p : ℕ) {z z2 : ℚ} (hz : 0 ≤ z) (h2 : (z : ℝ) ^ 2 ≤ (z2 : ℝ)) :
    ∀ k, (z : ℝ) ^ (2 * k + 1) ≤ ((pwHi p z z2 k : ℚ) : ℝ)
  | 0 => by simp [pwHi]
  | k + 1 => by
    have h1 := pwHi_sound p hz h2 k
    refine le_trans ?_ (le_rup_R p _)
    push_cast
    have hz' : (0 : ℝ) ≤ z := by exact_mod_cast hz
    calc (z : ℝ) ^ (2 * (k + 1) + 1) = (z : ℝ) ^ (2 * k + 1) * z ^ 2 := by ring
      _ ≤ ((pwHi p z z2 k : ℚ) : ℝ) * z2 := mul_le_mul h1 h2 (by positivity)
          (le_trans (by positivity) h1)

/-- Lower bound for `Σ_{k<J} z^{2k+1}/(2k+1)`. -/
def sumLo (p J : ℕ) (z : ℚ) : ℚ :=
  ∑ k ∈ range J, rdn p (pwLo p z (rdn p (z * z)) k / (2 * k + 1))

/-- Upper bound for `Σ_{k<J} z^{2k+1}/(2k+1)`, plus the tail. -/
def sumHi (p J : ℕ) (z : ℚ) : ℚ :=
  (∑ k ∈ range J, rup p (pwHi p z (rup p (z * z)) k / (2 * k + 1))) +
    rup p (pwHi p z (rup p (z * z)) J / ((2 * J + 1) * (1 - rup p (z * z))))

lemma atanh_hasSum {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) :
    HasSum (fun k : ℕ => z ^ (2 * k + 1) / (2 * k + 1)) (Real.log ((1 + z) / (1 - z)) / 2) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_of_nonneg h0]; exact h1)
  rw [← Real.log_div (by linarith) (by linarith)] at h
  have := h.div_const 2
  convert this using 1
  funext k
  ring

lemma sumLo_sound (p J : ℕ) {z : ℚ} (h0 : 0 ≤ z) (h1 : (z : ℝ) < 1) :
    2 * ((sumLo p J z : ℚ) : ℝ) ≤ Real.log ((1 + z) / (1 - z)) := by
  have hz : (0 : ℝ) ≤ z := by exact_mod_cast h0
  have hs := atanh_hasSum hz h1
  have z2a : (0 : ℚ) ≤ rdn p (z * z) := rdn_nonneg p (mul_nonneg h0 h0)
  have z2b : ((rdn p (z * z) : ℚ) : ℝ) ≤ (z : ℝ) ^ 2 := by
    have := rdn_le_R p (z * z); push_cast at this; nlinarith
  have hp := pwLo_sound p h0 z2a z2b
  have hle : ((sumLo p J z : ℚ) : ℝ) ≤ ∑ k ∈ range J, (z : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
    simp only [sumLo]
    push_cast
    apply Finset.sum_le_sum
    intro k _
    refine le_trans (rdn_le_R p _) ?_
    push_cast
    exact div_le_div_of_nonneg_right (hp k).2 (by positivity)
  have hpart : ∑ k ∈ range J, (z : ℝ) ^ (2 * k + 1) / (2 * k + 1) ≤ Real.log ((1 + z) / (1 - z)) / 2 :=
    sum_le_hasSum _ (fun k _ => by positivity) hs
  linarith

lemma sumHi_sound (p J : ℕ) {z : ℚ} (h0 : 0 ≤ z) (hz2 : rup p (z * z) < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ 2 * ((sumHi p J z : ℚ) : ℝ) := by
  have hz : (0 : ℝ) ≤ z := by exact_mod_cast h0
  set z2 := rup p (z * z) with hz2def
  have z2b : (z : ℝ) ^ 2 ≤ ((z2 : ℚ) : ℝ) := by
    have := le_rup_R p (z * z); push_cast at this; nlinarith
  have hz2R : ((z2 : ℚ) : ℝ) < 1 := by exact_mod_cast hz2
  have h1 : (z : ℝ) < 1 := by nlinarith
  have hs := atanh_hasSum hz h1
  have hp := pwHi_sound p h0 z2b
  -- split off the first J terms
  have htail := (hasSum_nat_add_iff' J).mpr hs
  -- the tail is dominated by a geometric series
  have hq : (0 : ℝ) ≤ (z : ℝ) ^ 2 := by positivity
  have hq1 : (z : ℝ) ^ 2 < 1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hq hq1).mul_left ((z : ℝ) ^ (2 * J + 1) / (2 * J + 1))
  have hcmp : ∀ n : ℕ, (z : ℝ) ^ (2 * (n + J) + 1) / (2 * ((n + J : ℕ) : ℝ) + 1) ≤
      (z : ℝ) ^ (2 * J + 1) / (2 * J + 1) * ((z : ℝ) ^ 2) ^ n := by
    intro n
    have e : (z : ℝ) ^ (2 * (n + J) + 1) = (z : ℝ) ^ (2 * J + 1) * ((z : ℝ) ^ 2) ^ n := by ring
    rw [e, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    push_cast; linarith
  have htle := hasSum_le hcmp htail hgeo
  have hbound : (z : ℝ) ^ (2 * J + 1) / (2 * J + 1) * (1 - (z : ℝ) ^ 2)⁻¹ ≤
      ((rup p (pwHi p z z2 J / ((2 * J + 1) * (1 - z2))) : ℚ) : ℝ) := by
    refine le_trans ?_ (le_rup_R p _)
    push_cast
    have hne : (1 : ℝ) - (z : ℝ) ^ 2 ≠ 0 := by linarith
    rw [show (z : ℝ) ^ (2 * J + 1) / (2 * J + 1) * (1 - (z : ℝ) ^ 2)⁻¹ =
      (z : ℝ) ^ (2 * J + 1) / ((2 * J + 1) * (1 - (z : ℝ) ^ 2)) by field_simp]
    have hd : (0 : ℝ) < (2 * J + 1) * (1 - (z2 : ℝ)) := by
      have : (0 : ℝ) < 1 - z2 := by linarith
      positivity
    apply div_le_div₀ (le_trans (by positivity) (hp J)) (hp J) hd
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hhead : ∑ k ∈ range J, (z : ℝ) ^ (2 * k + 1) / (2 * k + 1) ≤
      ∑ k ∈ range J, ((rup p (pwHi p z z2 k / (2 * k + 1)) : ℚ) : ℝ) := by
    apply Finset.sum_le_sum
    intro k _
    refine le_trans ?_ (le_rup_R p _)
    push_cast
    exact div_le_div_of_nonneg_right (hp k) (by positivity)
  simp only [sumHi]
  push_cast
  push_cast at hhead hbound
  linarith

/-! ### Logarithms -/

/-- `⌊log₂ n⌋` with fuel (structural, so the kernel evaluates it). -/
def blen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else blen fuel (n / 2) + 1

/-- A guess for `⌊log₂ y⌋` from the bit lengths (correctness is not needed, only `1 ≤ w`, which
`logOK` checks). -/
def mOf (y : ℚ) : ℤ :=
  let m : ℤ := (blen 100000 y.num.natAbs : ℤ) - (blen 100000 y.den : ℤ)
  if 1 ≤ y / 2 ^ m then m else m - 1

/-- The reduction `y = 2^m w`. -/
def red (y : ℚ) : ℤ × ℚ := (mOf y, y / 2 ^ (mOf y))

/-- `z = (w − 1)/(w + 1)`. -/
def zOf (w : ℚ) : ℚ := (w - 1) / (w + 1)

/-- An interval for `log 2` (`z = 1/3`). -/
def log2I (p J : ℕ) : I := (2 * sumLo p J (1 / 3), 2 * sumHi p J (1 / 3))

lemma mem_log2 (p J : ℕ) (h : rup p (1 / 3 * (1 / 3)) < 1) : Mem (Real.log 2) (log2I p J) := by
  have e : ((1 : ℝ) + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) = 2 := by push_cast; norm_num
  constructor
  · have := sumLo_sound p J (z := 1 / 3) (by norm_num) (by push_cast; norm_num)
    rw [e] at this; simp only [log2I]; push_cast; linarith
  · have := sumHi_sound p J (z := 1 / 3) (by norm_num) h
    rw [e] at this; simp only [log2I]; push_cast; linarith

/-- `m · log 2`, as an interval. -/
def mlog2 (p J : ℕ) (m : ℤ) : I := mul (ofQ m) (log2I p J)

/-- Lower bound for `log y`, `y > 0`. -/
def logLo (p J : ℕ) (y : ℚ) : ℚ := (mlog2 p J (red y).1).1 + 2 * sumLo p J (zOf (red y).2)

/-- Upper bound for `log y`, `y > 0`. -/
def logHi (p J : ℕ) (y : ℚ) : ℚ := (mlog2 p J (red y).1).2 + 2 * sumHi p J (zOf (red y).2)

/-- `log` of a positive interval. -/
def logI (p J : ℕ) (A : I) : I := (logLo p J A.1, logHi p J A.2)

/-- The side conditions of `logI` (all decidable). -/
def logOK (p : ℕ) (A : I) : Bool :=
  decide (0 < A.1) && decide (rup p (1 / 3 * (1 / 3)) < 1) &&
    decide (rup p (zOf (red A.2).2 * zOf (red A.2).2) < 1) &&
    decide (1 ≤ (red A.1).2) && decide (1 ≤ (red A.2).2)

lemma red_eq {y : ℚ} : (y : ℝ) = (2 : ℝ) ^ (red y).1 * ((red y).2 : ℝ) := by
  simp only [red]
  push_cast
  field_simp

lemma log_red {y : ℚ} (hw1 : 1 ≤ (red y).2) :
    Real.log y = (red y).1 * Real.log 2 +
      Real.log ((1 + (zOf (red y).2 : ℝ)) / (1 - (zOf (red y).2 : ℝ))) := by
  have hw : (1 : ℝ) ≤ (red y).2 := by exact_mod_cast hw1
  have hz : (1 + (zOf (red y).2 : ℝ)) / (1 - (zOf (red y).2 : ℝ)) = (red y).2 := by
    simp only [zOf]; push_cast; field_simp; ring
  rw [hz, red_eq, Real.log_mul (by positivity) (by positivity), Real.log_zpow]

lemma zOf_bounds {w : ℚ} (h1 : 1 ≤ w) : 0 ≤ zOf w ∧ ((zOf w : ℚ) : ℝ) < 1 := by
  simp only [zOf]
  constructor
  · apply div_nonneg <;> linarith
  · push_cast
    rw [div_lt_one (by have : (1 : ℝ) ≤ w := by exact_mod_cast h1
                       linarith)]
    linarith

lemma logLo_sound (p J : ℕ) {y : ℚ} (h1 : 1 ≤ (red y).2) (h3 : rup p (1 / 3 * (1 / 3)) < 1) :
    ((logLo p J y : ℚ) : ℝ) ≤ Real.log y := by
  obtain ⟨z0, z1⟩ := zOf_bounds h1
  have hs := sumLo_sound p J z0 z1
  have hm := (mem_mul (mem_ofQ ((red y).1 : ℚ)) (mem_log2 p J h3)).1
  rw [log_red h1]
  simp only [logLo, mlog2]
  push_cast at hm ⊢
  linarith

lemma logHi_sound (p J : ℕ) {y : ℚ} (h1 : 1 ≤ (red y).2) (h3 : rup p (1 / 3 * (1 / 3)) < 1)
    (hz : rup p (zOf (red y).2 * zOf (red y).2) < 1) :
    Real.log y ≤ ((logHi p J y : ℚ) : ℝ) := by
  obtain ⟨z0, -⟩ := zOf_bounds h1
  have hs := sumHi_sound p J z0 hz
  have hm := (mem_mul (mem_ofQ ((red y).1 : ℚ)) (mem_log2 p J h3)).2
  rw [log_red h1]
  simp only [logHi, mlog2]
  push_cast at hm ⊢
  linarith

/-- **`log` of a positive interval.** -/
lemma mem_log {x : ℝ} {A : I} (p J : ℕ) (hx : Mem x A) (h : logOK p A = true) :
    Mem (Real.log x) (logI p J A) := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, h3⟩, hz⟩, hw1⟩, hw2⟩ := h
  have h0' : (0 : ℝ) < A.1 := by exact_mod_cast h0
  have hxpos : 0 < x := lt_of_lt_of_le h0' hx.1
  constructor
  · exact le_trans (logLo_sound p J hw1 h3) (Real.log_le_log h0' hx.1)
  · exact le_trans (Real.log_le_log hxpos hx.2) (logHi_sound p J hw2 h3 hz)

/-! ### An upper bound for `exp` -/

/-- Repeated squaring with upward rounding. -/
def sqIter (p : ℕ) : ℕ → ℚ → ℚ
  | 0, v => v
  | k + 1, v => sqIter p k (rup p (v * v))

/-- An upper bound for `exp r`: `exp(r/2^m) ≤ 1/(1 − r/2^m)`, squared `m` times. -/
def expHi (p m : ℕ) (r : ℚ) : ℚ := sqIter p m (rup p (1 / (1 - r / 2 ^ m)))

lemma sqIter_sound (p : ℕ) : ∀ (k : ℕ) (x : ℝ) (v : ℚ), Real.exp x ≤ v →
    Real.exp (2 ^ k * x) ≤ ((sqIter p k v : ℚ) : ℝ)
  | 0, x, v, h => by simpa [sqIter] using h
  | k + 1, x, v, h => by
    simp only [sqIter]
    have h2 : Real.exp (2 * x) ≤ ((rup p (v * v) : ℚ) : ℝ) := by
      refine le_trans ?_ (le_rup_R p _)
      push_cast
      rw [show 2 * x = x + x by ring, Real.exp_add]
      exact mul_le_mul h h (Real.exp_pos x).le (le_trans (Real.exp_pos x).le h)
    have := sqIter_sound p k (2 * x) _ h2
    rw [show (2 : ℝ) ^ (k + 1) * x = 2 ^ k * (2 * x) by ring]
    exact this

/-- **`exp r ≤ expHi r`**, for `r/2^m < 1`. -/
lemma exp_le_expHi (p m : ℕ) {r : ℚ} (h : r / 2 ^ m < 1) : Real.exp r ≤ ((expHi p m r : ℚ) : ℝ) := by
  set s : ℝ := ((r / 2 ^ m : ℚ) : ℝ)
  have hs : s < 1 := by simp only [s]; exact_mod_cast h
  have hs1 : Real.exp s ≤ ((rup p (1 / (1 - r / 2 ^ m)) : ℚ) : ℝ) := by
    refine le_trans ?_ (le_rup_R p _)
    have := Real.add_one_le_exp (-s)
    have hpos : 0 < 1 - s := by linarith
    have hexp : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    push_cast
    rw [show (1 : ℝ) / (1 - (r : ℝ) / 2 ^ m) = 1 / (1 - s) by simp [s]]
    rw [le_div_iff₀ hpos]
    nlinarith [Real.exp_pos s, Real.exp_pos (-s)]
  have := sqIter_sound p m s _ hs1
  simp only [expHi]
  convert this using 2
  simp only [s]
  push_cast
  field_simp

end PerfectPower.RatInterval
