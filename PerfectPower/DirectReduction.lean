import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Rat.Floor

/-!
# The direct maximum-exponent reduction (Dujella–Pethő form, keeping `H`)

For a rank-two unit equation the analytic estimates give, with `H = max(|e₁|, |e₂|)`,

  `|κ e₁ + e₂ + μ| ≤ A e^{−c H}`  and a first bound `H ≤ M`.

* `reduce`: if `|q κ − p| ≤ η`, every integer `z` has `|q μ − z| ≥ δ`, and `ε = δ − M η > 0`, then
  `ε ≤ q A e^{−c H}`.  So a finite Taylor sum `Σ_{k<J} (c (B + 1))^k / k! > q A / ε` forces
  `H ≤ B`.  Both exponents are bounded at once; no sign or second-coordinate step is needed.
* `stepCheck` / `step_sound`: the same, with every real number replaced by a rational enclosure
  (`κ ∈ [kl, ku]`, `μ ∈ [ml, mu]`, `c ≥ cl`, `A ≤ Au`), checked by evaluation.
* `chainCheck` / `chain_sound`: iterated steps, each starting from the previous bound.

The analytic input itself (the inequality, the first bound from Matveev's theorem, and the
enclosures of the logarithms) is a hypothesis here.
-/

namespace PerfectPower.DirectReduction

open Real Finset

/-- The integer `H = max(|e₁|, |e₂|)`. -/
def hmax (e1 e2 : ℤ) : ℤ := max |e1| |e2|

/-- **The direct reduction.** -/
theorem reduce (κ μ A c η δ M : ℝ) (q p : ℤ) (B J : ℕ) (hq : 0 < q)
    (hκ : |(q : ℝ) * κ - p| ≤ η) (hμ : ∀ z : ℤ, δ ≤ |(q : ℝ) * μ - z|) (hε : 0 < δ - M * η)
    (hA : 0 ≤ A) (hc : 0 ≤ c)
    (ht : (q : ℝ) * A / (δ - M * η) < ∑ k ∈ range J, (c * (B + 1)) ^ k / (k.factorial : ℝ))
    (e1 e2 : ℤ) (h1 : (|e1| : ℝ) ≤ M)
    (hlin : |κ * e1 + e2 + μ| ≤ A * exp (-(c * (hmax e1 e2 : ℝ)))) :
    hmax e1 e2 ≤ B := by
  by_contra hcon
  push_neg at hcon
  have hH : (B : ℝ) + 1 ≤ (hmax e1 e2 : ℝ) := by exact_mod_cast hcon
  set ε := δ - M * η with hεdef
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hM : 0 ≤ M := le_trans (abs_nonneg _) h1
  -- `q μ − z = q (κ e₁ + e₂ + μ) − e₁ (q κ − p)` at `z = −p e₁ − q e₂`
  have hz := hμ (-p * e1 - q * e2)
  have hid : (q : ℝ) * μ - ((-p * e1 - q * e2 : ℤ) : ℝ) =
      (q : ℝ) * (κ * e1 + e2 + μ) - e1 * ((q : ℝ) * κ - p) := by push_cast; ring
  rw [hid] at hz
  have h2 : |(q : ℝ) * (κ * e1 + e2 + μ) - e1 * ((q : ℝ) * κ - p)| ≤
      (q : ℝ) * (A * exp (-(c * (hmax e1 e2 : ℝ)))) + M * η := by
    calc _ ≤ |(q : ℝ) * (κ * e1 + e2 + μ)| + |(e1 : ℝ) * ((q : ℝ) * κ - p)| := abs_sub _ _
      _ = (q : ℝ) * |κ * e1 + e2 + μ| + |(e1 : ℝ)| * |(q : ℝ) * κ - p| := by
          rw [abs_mul, abs_mul, abs_of_pos hqr]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hlin hqr.le
          have := mul_le_mul h1 hκ (abs_nonneg _) hM
          push_cast at *
          linarith
  have hexp : exp (-(c * (hmax e1 e2 : ℝ))) ≤ exp (-(c * ((B : ℝ) + 1))) := by
    apply exp_le_exp.mpr
    nlinarith
  have h3 : ε ≤ (q : ℝ) * A * exp (-(c * ((B : ℝ) + 1))) := by
    have : (q : ℝ) * (A * exp (-(c * (hmax e1 e2 : ℝ)))) ≤ (q : ℝ) * A * exp (-(c * ((B : ℝ) + 1))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    linarith
  have hsum : ∑ k ∈ range J, (c * (B + 1)) ^ k / (k.factorial : ℝ) ≤ exp (c * ((B : ℝ) + 1)) :=
    Real.sum_le_exp_of_nonneg (by positivity) J
  have h4 : (q : ℝ) * A < ε * exp (c * ((B : ℝ) + 1)) := by
    have := lt_of_lt_of_le ht hsum
    rw [div_lt_iff₀ hε] at this
    linarith
  have h5 : (q : ℝ) * A * exp (-(c * ((B : ℝ) + 1))) < ε := by
    have he : exp (-(c * ((B : ℝ) + 1))) * exp (c * ((B : ℝ) + 1)) = 1 := by
      rw [← exp_add]; simp
    have hpos := exp_pos (-(c * ((B : ℝ) + 1)))
    nlinarith
  linarith

/-- Every integer is at least `min(lo − k, k + 1 − hi)` from a point of `[lo, hi] ⊂ (k, k + 1)`. -/
lemma dist_int (x lo hi : ℝ) (k : ℤ) (h1 : lo ≤ x) (h2 : x ≤ hi) (z : ℤ) :
    min (lo - k) (k + 1 - hi) ≤ |x - z| := by
  rcases le_or_lt z k with hz | hz
  · have : (z : ℝ) ≤ k := by exact_mod_cast hz
    calc min (lo - k) (k + 1 - hi) ≤ lo - k := min_le_left _ _
      _ ≤ x - z := by linarith
      _ ≤ |x - z| := le_abs_self _
  · have : (k : ℝ) + 1 ≤ z := by exact_mod_cast hz
    calc min (lo - k) (k + 1 - hi) ≤ k + 1 - hi := min_le_right _ _
      _ ≤ -(x - z) := by linarith
      _ ≤ |x - z| := neg_le_abs _

/-- `Σ_{k<J} x^k / k!` over `ℚ`. -/
def taylor (x : ℚ) (J : ℕ) : ℚ := ∑ k ∈ range J, x ^ k / (k.factorial : ℚ)

/-- The nearest integer to `q (kl + ku) / 2`. -/
def pOf (kl ku : ℚ) (q : ℕ) : ℤ := ⌊(q : ℚ) * (kl + ku) / 2 + 1 / 2⌋

/-- An upper bound for `|q κ − p|`, for `κ ∈ [kl, ku]`. -/
def etaOf (kl ku : ℚ) (q : ℕ) : ℚ := max |(q : ℚ) * kl - pOf kl ku q| |(q : ℚ) * ku - pOf kl ku q|
/-- A lower bound for the distance from `q μ` to the integers, for `μ ∈ [ml, mu]`. -/
def deltaOf (ml mu : ℚ) (q : ℕ) : ℚ :=
  min ((q : ℚ) * ml - ⌊(q : ℚ) * ml⌋) (⌊(q : ℚ) * ml⌋ + 1 - (q : ℚ) * mu)

/-- One reduction step, checked by evaluation: from `H ≤ M` to `H ≤ B`. -/
def stepCheck (kl ku ml mu cl Au : ℚ) (M q B J : ℕ) : Bool :=
  decide (0 < q) && decide (0 ≤ cl) && decide (0 ≤ Au) && decide (kl ≤ ku) && decide (ml ≤ mu) &&
    decide (0 < deltaOf ml mu q - M * etaOf kl ku q) &&
    decide ((q : ℚ) * Au / (deltaOf ml mu q - M * etaOf kl ku q) < taylor (cl * (B + 1)) J)

lemma abs_le_of_between {x a b : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : |x| ≤ max |a| |b| := by
  rw [abs_le]
  constructor
  · have := neg_abs_le a
    have := le_max_left |a| |b|
    linarith
  · have := le_abs_self b
    have := le_max_right |a| |b|
    linarith

/-- **A checked step is sound.** -/
theorem step_sound {kl ku ml mu cl Au : ℚ} {M q B J : ℕ}
    (h : stepCheck kl ku ml mu cl Au M q B J = true)
    (κ μ c A : ℝ) (hk1 : (kl : ℝ) ≤ κ) (hk2 : κ ≤ ku) (hm1 : (ml : ℝ) ≤ μ) (hm2 : μ ≤ mu)
    (hc : (cl : ℝ) ≤ c) (hA : A ≤ Au)
    (e1 e2 : ℤ) (hH : hmax e1 e2 ≤ M)
    (hlin : |κ * e1 + e2 + μ| ≤ A * exp (-(c * (hmax e1 e2 : ℝ)))) : hmax e1 e2 ≤ B := by
  simp only [stepCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hq, hcl⟩, hAu⟩, -⟩, -⟩, hε⟩, ht⟩ := h
  have hH0 : (0 : ℝ) ≤ (hmax e1 e2 : ℝ) := by
    have : 0 ≤ hmax e1 e2 := le_trans (abs_nonneg e1) (le_max_left _ _)
    exact_mod_cast this
  have hlin' : |κ * e1 + e2 + μ| ≤ (Au : ℝ) * exp (-((cl : ℝ) * (hmax e1 e2 : ℝ))) := by
    have hA0 : 0 ≤ A := by
      rcases le_or_lt 0 A with h0 | h0
      · exact h0
      · have := mul_neg_of_neg_of_pos h0 (exp_pos (-(c * (hmax e1 e2 : ℝ))))
        linarith [abs_nonneg (κ * e1 + e2 + μ)]
    have he : exp (-(c * (hmax e1 e2 : ℝ))) ≤ exp (-((cl : ℝ) * (hmax e1 e2 : ℝ))) :=
      exp_le_exp.mpr (by nlinarith)
    calc _ ≤ A * exp (-(c * (hmax e1 e2 : ℝ))) := hlin
      _ ≤ A * exp (-((cl : ℝ) * (hmax e1 e2 : ℝ))) := mul_le_mul_of_nonneg_left he hA0
      _ ≤ _ := mul_le_mul_of_nonneg_right hA (exp_pos _).le
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hκ : |((q : ℤ) : ℝ) * κ - (pOf kl ku q : ℝ)| ≤ ((etaOf kl ku q : ℚ) : ℝ) := by
    have := abs_le_of_between (x := ((q : ℤ) : ℝ) * κ - (pOf kl ku q : ℝ))
      (a := (q : ℝ) * kl - pOf kl ku q) (b := (q : ℝ) * ku - pOf kl ku q)
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    simpa [etaOf] using this
  have hμ : ∀ z : ℤ, ((deltaOf ml mu q : ℚ) : ℝ) ≤ |((q : ℤ) : ℝ) * μ - z| := by
    intro z
    have := dist_int (((q : ℤ) : ℝ) * μ) ((q : ℝ) * ml) ((q : ℝ) * mu) ⌊(q : ℚ) * ml⌋
      (by push_cast; nlinarith) (by push_cast; nlinarith) z
    have e : ((deltaOf ml mu q : ℚ) : ℝ) = min ((q : ℝ) * ml - (⌊(q : ℚ) * ml⌋ : ℝ))
        ((⌊(q : ℚ) * ml⌋ : ℝ) + 1 - (q : ℝ) * mu) := by
      unfold deltaOf; push_cast; rfl
    rw [e]
    exact this
  have h1 : (|e1| : ℝ) ≤ (M : ℝ) := by
    have : |e1| ≤ (M : ℤ) := le_trans (le_max_left _ _) hH
    exact_mod_cast this
  refine reduce κ μ Au cl (etaOf kl ku q) (deltaOf ml mu q) M q (pOf kl ku q) B J hq'
    hκ hμ (by exact_mod_cast hε) (by exact_mod_cast hAu) (by exact_mod_cast hcl) ?_ e1 e2 h1 hlin'
  have ht' : (((q : ℚ) * Au / (deltaOf ml mu q - M * etaOf kl ku q) : ℚ) : ℝ) <
      ((taylor (cl * (B + 1)) J : ℚ) : ℝ) := by exact_mod_cast ht
  simpa [taylor] using ht'

/-- A chain of steps from `H ≤ M₀`; `steps` lists `(q, B, J)`. -/
def chainCheck (kl ku ml mu cl Au : ℚ) : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | M, (q, B, J) :: rest => stepCheck kl ku ml mu cl Au M q B J && chainCheck kl ku ml mu cl Au B rest

/-- The final bound of a chain. -/
def chainEnd : ℕ → List (ℕ × ℕ × ℕ) → ℕ
  | M, [] => M
  | _, (_, B, _) :: rest => chainEnd B rest

/-- **A checked chain is sound.** -/
theorem chain_sound {kl ku ml mu cl Au : ℚ} (κ μ c A : ℝ) (hk1 : (kl : ℝ) ≤ κ) (hk2 : κ ≤ ku)
    (hm1 : (ml : ℝ) ≤ μ) (hm2 : μ ≤ mu) (hc : (cl : ℝ) ≤ c) (hA : A ≤ Au) (e1 e2 : ℤ)
    (hlin : |κ * e1 + e2 + μ| ≤ A * exp (-(c * (hmax e1 e2 : ℝ)))) :
    ∀ (M : ℕ) (steps : List (ℕ × ℕ × ℕ)), chainCheck kl ku ml mu cl Au M steps = true →
      hmax e1 e2 ≤ M → hmax e1 e2 ≤ chainEnd M steps
  | M, [], _, hH => by simpa [chainEnd] using hH
  | M, (q, B, J) :: rest, h, hH => by
    simp only [chainCheck, Bool.and_eq_true] at h
    have hB := step_sound h.1 κ μ c A hk1 hk2 hm1 hm2 hc hA e1 e2 hH hlin
    exact chain_sound κ μ c A hk1 hk2 hm1 hm2 hc hA e1 e2 hlin B rest h.2 hB

end PerfectPower.DirectReduction
