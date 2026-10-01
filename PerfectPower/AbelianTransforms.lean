import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Abelian theorems for the heat transform of a hit set

For a set `X ⊆ ℕ` (the hits, `n ≥ 1`), let `A(x) = #{1 ≤ n ≤ x : n ∈ X}` and
`K(t) = Σ_{n ∈ X} e^{−tn}` (`heat`).

* `heat_eq_integral`: `K(t) = ∫₀^∞ e^{−u} A₋(u/t) du` for `t > 0`, where `A₋(x) = #{n < x}`
  (Tonelli: `e^{−tn} = ∫_{u > tn} e^{−u} du`).
* **`heat_abelian`**: if `A(x) ~ c x^α (log x)^β` with `α > 0`, `β ≥ 0`, then
  `K(t) ~ c Γ(α + 1) t^{−α} (log(1/t))^β` as `t → 0⁺`.  The proof is dominated convergence:
  `t^α A₋(u/t)/(log 1/t)^β → c u^α` for each `u > 0`, dominated by `C (e + 1)^β (u^α + u^{α+β})`.
-/

namespace PerfectPower.AbelianTransforms

open Real Filter Topology MeasureTheory Set

variable (X : ℕ → Prop) [DecidablePred X]

/-- `A(x) = #{1 ≤ n ≤ x : n ∈ X}`. -/
noncomputable def cnt (x : ℝ) : ℝ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter (fun n => 1 ≤ n ∧ X n)).card

/-- `A₋(x) = #{1 ≤ n < x : n ∈ X}`. -/
noncomputable def cntLt (x : ℝ) : ℝ :=
  ((Finset.range ⌈x⌉₊).filter (fun n => 1 ≤ n ∧ X n)).card

/-- The heat transform `K(t) = Σ_{n ∈ X, n ≥ 1} e^{−tn}`. -/
noncomputable def heat (t : ℝ) : ℝ := ∑' n : ℕ, if 1 ≤ n ∧ X n then rexp (-(t * n)) else 0

/-! ### The integral form -/

lemma integral_term {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∫ u in Ioi 0, (Ioi (t * n)).indicator (fun u => rexp (-u)) u = rexp (-(t * n)) := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, sup_eq_left.mpr (by positivity), integral_exp_neg_Ioi]

lemma summable_exp {t : ℝ} (ht : 0 < t) : Summable fun n : ℕ => rexp (-(t * n)) := by
  have : (fun n : ℕ => rexp (-(t * n))) = fun n => rexp (-t) ^ n := by
    funext n; rw [← Real.exp_nat_mul]; ring_nf
  rw [this]
  exact summable_geometric_of_lt_one (exp_pos _).le
    (by simpa using Real.exp_lt_exp.mpr (show -t < 0 by linarith))

lemma tsum_indicator {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ∑' n : ℕ, (if 1 ≤ n ∧ X n then (Ioi (t * n)).indicator (fun u => rexp (-u)) u else 0) =
      rexp (-u) * cntLt X (u / t) := by
  rw [tsum_eq_sum (s := Finset.range ⌈u / t⌉₊)]
  · rw [cntLt, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : t * n < u := by
      have := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
      rw [lt_div_iff₀ ht] at this; linarith
    split_ifs <;> simp_all
  · intro n hn
    have : u ≤ t * n := by
      rw [Finset.mem_range, not_lt, Nat.ceil_le, div_le_iff₀ ht] at hn; linarith
    split_ifs <;> simp [indicator, not_lt.mpr this]

/-- **The heat transform as an integral of the count.** -/
theorem heat_eq_integral {t : ℝ} (ht : 0 < t) :
    heat X t = ∫ u in Ioi 0, rexp (-u) * cntLt X (u / t) := by
  set f : ℕ → ℝ → ℝ := fun n u =>
    if 1 ≤ n ∧ X n then (Ioi (t * n)).indicator (fun u => rexp (-u)) u else 0
  have hf : ∀ n, ∫ u in Ioi 0, f n u = if 1 ≤ n ∧ X n then rexp (-(t * n)) else 0 := by
    intro n; simp only [f]; split_ifs
    · exact integral_term ht n
    · simp
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)) := by
    intro n; simp only [f]; split_ifs
    · exact ((measurable_neg.exp).indicator measurableSet_Ioi).aestronglyMeasurable
    · exact aestronglyMeasurable_const
  have hlin : ∀ n, ∫⁻ u in Ioi 0, ‖f n u‖ₑ =
      ENNReal.ofReal (if 1 ≤ n ∧ X n then rexp (-(t * n)) else 0) := by
    intro n
    rw [← hf n, ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun u => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg]
      simp only [f]; split_ifs
      · exact indicator_nonneg (fun _ _ => (exp_pos _).le) _
      · exact le_rfl
    · simp only [f]; split_ifs
      · have h1 : IntegrableOn (fun u : ℝ => rexp (-u)) (Ioi 0) :=
          (exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun u _ => by simp) measurableSet_Ioi
        exact h1.indicator measurableSet_Ioi
      · exact integrable_zero _ _ _
    · exact Eventually.of_forall fun u => by
        simp only [f]; split_ifs
        · exact indicator_nonneg (fun _ _ => (exp_pos _).le) _
        · exact le_rfl
  have hsum : ∑' n, ∫⁻ u in Ioi 0, ‖f n u‖ₑ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro n; split_ifs <;> positivity
    · exact (summable_exp ht).of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> first | exact le_rfl | positivity)
  rw [heat, ← tsum_congr hf, ← integral_tsum hmeas hsum]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  exact tsum_indicator X ht u

/-! ### Counting bounds -/

lemma cntLt_mono : Monotone (cntLt X) := by
  intro x y hxy
  unfold cntLt
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_subset.mpr (Nat.ceil_mono hxy)))

lemma cntLt_le_cnt (x : ℝ) : cntLt X x ≤ cnt X x := by
  unfold cntLt cnt
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_subset.mpr (Nat.ceil_le_floor_add_one x)))

lemma cnt_le_cntLt_add_one (x : ℝ) : cnt X x ≤ cntLt X x + 1 := by
  unfold cntLt cnt
  have h : (Finset.range (⌊x⌋₊ + 1)).filter (fun n => 1 ≤ n ∧ X n) ⊆
      insert ⌊x⌋₊ ((Finset.range ⌈x⌉₊).filter (fun n => 1 ≤ n ∧ X n)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rcases Nat.lt_or_ge n ⌊x⌋₊ with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_of_lt_of_le h (Nat.floor_le_ceil x)), hn.2⟩)
    · rw [show n = ⌊x⌋₊ by omega]; exact Finset.mem_insert_self _ _
  have := (Finset.card_le_card h).trans (Finset.card_insert_le _ _)
  exact_mod_cast this

lemma cnt_nonneg (x : ℝ) : 0 ≤ cnt X x := by unfold cnt; positivity

lemma cnt_of_lt_one {x : ℝ} (hx : x < 1) : cnt X x = 0 := by
  unfold cnt
  rw [Nat.floor_eq_zero.mpr hx]
  simp only [zero_add, Finset.range_one, Nat.cast_eq_zero, Finset.card_eq_zero]
  ext n; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
  rintro ⟨rfl, h, _⟩; omega

lemma cnt_le_add_one {x : ℝ} (hx : 0 ≤ x) : cnt X x ≤ x + 1 := by
  unfold cnt
  have := (Finset.card_filter_le (Finset.range (⌊x⌋₊ + 1)) (fun n => 1 ≤ n ∧ X n))
  rw [Finset.card_range] at this
  have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1 := by push_cast; linarith [Nat.floor_le hx]
  exact le_trans (by exact_mod_cast this) h2

/-- **A Potter-type bound**: from `A(x) ~ c x^α (log x)^β`, `A(x) ≤ C x^α (log(e + x))^β` for all
`x > 0`. -/
lemma cnt_bound {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c)) :
    ∃ C, 0 ≤ C ∧ ∀ x, 0 < x → cnt X x ≤ C * (x ^ α * Real.log (rexp 1 + x) ^ β) := by
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp (hA.eventually_lt_const (lt_add_one c))
  set x0 := max x1 (rexp 1)
  refine ⟨max (|c| + 1) (x0 + 1), by positivity, fun x hx => ?_⟩
  have hlog1 : 1 ≤ Real.log (rexp 1 + x) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith
  rcases lt_or_ge x x0 with h | h
  · rcases lt_or_ge x 1 with h1 | h1
    · rw [cnt_of_lt_one X h1]; positivity
    · have e1 : 1 ≤ x ^ α := Real.one_le_rpow h1 hα.le
      have e2 : 1 ≤ Real.log (rexp 1 + x) ^ β := Real.one_le_rpow hlog1 hβ
      calc cnt X x ≤ x + 1 := cnt_le_add_one X hx.le
        _ ≤ x0 + 1 := by linarith
        _ ≤ max (|c| + 1) (x0 + 1) * 1 := by rw [mul_one]; exact le_max_right _ _
        _ ≤ max (|c| + 1) (x0 + 1) * (x ^ α * Real.log (rexp 1 + x) ^ β) := by
          gcongr; nlinarith
  · have hx1' : x1 ≤ x := le_trans (le_max_left _ _) h
    have he : rexp 1 ≤ x := le_trans (le_max_right _ _) h
    have hl : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx]; exact he
    have hD : 0 < x ^ α * Real.log x ^ β := by positivity
    have := (div_lt_iff₀ hD).mp (hx1 x hx1')
    calc cnt X x ≤ (c + 1) * (x ^ α * Real.log x ^ β) := this.le
      _ ≤ max (|c| + 1) (x0 + 1) * (x ^ α * Real.log x ^ β) := by
          gcongr; exact le_trans (by linarith [le_abs_self c]) (le_max_left _ _)
      _ ≤ max (|c| + 1) (x0 + 1) * (x ^ α * Real.log (rexp 1 + x) ^ β) := by
          gcongr
          linarith [exp_pos 1]

/-! ### The Abelian theorem -/

lemma tendsto_div_t {u : ℝ} (hu : 0 < u) : Tendsto (fun t : ℝ => u / t) (𝓝[>] 0) atTop := by
  simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hu

lemma tendsto_L : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
  exact (tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).congr (fun t => by rw [Function.comp, one_div])

/-- The strict count has the same asymptotics. -/
lemma cntLt_asymp {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c)) :
    Tendsto (fun x => cntLt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c) := by
  have hD : Tendsto (fun x : ℝ => x ^ α * Real.log x ^ β) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_rpow_atTop hα)
    filter_upwards [eventually_ge_atTop (rexp 1)] with x hx
    have hl : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le (by linarith [exp_pos 1])]; exact hx
    have : 1 ≤ Real.log x ^ β := Real.one_le_rpow hl hβ
    have : 0 ≤ x ^ α := Real.rpow_nonneg (by linarith [exp_pos 1]) _
    nlinarith
  have hinv := hD.inv_tendsto_atTop
  have hlow : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β) - (x ^ α * Real.log x ^ β)⁻¹)
      atTop (𝓝 c) := by simpa using hA.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hA ?_ ?_
  · filter_upwards [hD.eventually_gt_atTop 0] with x hx
    have e : cnt X x / (x ^ α * Real.log x ^ β) - (x ^ α * Real.log x ^ β)⁻¹ =
        (cnt X x - 1) / (x ^ α * Real.log x ^ β) := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith [cnt_le_cntLt_add_one X x]) hx.le
  · filter_upwards [hD.eventually_gt_atTop 0] with x hx
    exact div_le_div_of_nonneg_right (cntLt_le_cnt X x) hx.le

/-- The rescaled count converges pointwise: `t^α A₋(u/t) / (log 1/t)^β → c u^α`. -/
lemma pointwise {α β c u : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hu : 0 < u)
    (hA : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c)) :
    Tendsto (fun t => cntLt X (u / t) * t ^ α / Real.log (1 / t) ^ β) (𝓝[>] 0)
      (𝓝 (c * u ^ α)) := by
  have h1 := (cntLt_asymp X hα hβ hA).comp (tendsto_div_t hu)
  have hratio : Tendsto (fun t => Real.log (u / t) / Real.log (1 / t)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun t => Real.log u / Real.log (1 / t)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_L.const_div_atTop _ |> fun h => by simpa using h
    have := h0.const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, tendsto_L.eventually_gt_atTop 0] with t ht hL
    have ht' : 0 < t := ht
    rw [show Real.log (u / t) = Real.log u + Real.log (1 / t) by
      rw [one_div, Real.log_inv, Real.log_div hu.ne' ht'.ne']; ring]
    field_simp
    ring
  have h2 := hratio.rpow_const (p := β) (Or.inr hβ)
  rw [Real.one_rpow] at h2
  have h3 := (h1.mul_const (u ^ α)).mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin, (tendsto_div_t hu).eventually_gt_atTop (rexp 1),
    tendsto_L.eventually_gt_atTop 0] with t ht hx hL
  have ht' : 0 < t := ht
  have hx0 : 0 < u / t := by positivity
  have hlx : 0 < Real.log (u / t) := Real.log_pos (by linarith [Real.add_one_le_exp 1])
  simp only [Function.comp]
  have e1 : (u / t) ^ α * t ^ α = u ^ α := by
    rw [← Real.mul_rpow hx0.le ht'.le, div_mul_cancel₀ _ ht'.ne']
  have e2 : (Real.log (u / t) / Real.log (1 / t)) ^ β =
      Real.log (u / t) ^ β / Real.log (1 / t) ^ β := Real.div_rpow hlx.le hL.le _
  rw [e2, ← e1]
  field_simp
  ring

lemma one_add_log_le {u : ℝ} (hu : 0 ≤ u) (β : ℝ) (hβ : 0 ≤ β) :
    (1 + Real.log (rexp 1 + u)) ^ β ≤ (rexp 1 + 1) ^ β * (1 + u ^ β) := by
  have h1 : 1 + Real.log (rexp 1 + u) ≤ rexp 1 + u := by
    have := Real.log_le_sub_one_of_pos (show 0 < rexp 1 + u by positivity); linarith
  have h0 : 0 ≤ 1 + Real.log (rexp 1 + u) := by
    have := Real.log_nonneg (show 1 ≤ rexp 1 + u by linarith [Real.add_one_le_exp 1]); linarith
  have hE : 0 ≤ (rexp 1 + 1) ^ β := by positivity
  calc (1 + Real.log (rexp 1 + u)) ^ β ≤ (rexp 1 + u) ^ β := Real.rpow_le_rpow h0 h1 hβ
    _ ≤ (rexp 1 + 1) ^ β * (1 + u ^ β) := by
      rcases le_or_lt u 1 with h | h
      · calc (rexp 1 + u) ^ β ≤ (rexp 1 + 1) ^ β :=
            Real.rpow_le_rpow (by positivity) (by linarith) hβ
          _ ≤ (rexp 1 + 1) ^ β * (1 + u ^ β) := by
            have : 0 ≤ u ^ β := by positivity
            nlinarith
      · calc (rexp 1 + u) ^ β ≤ ((rexp 1 + 1) * u) ^ β :=
            Real.rpow_le_rpow (by positivity) (by nlinarith [exp_pos 1]) hβ
          _ = (rexp 1 + 1) ^ β * u ^ β := Real.mul_rpow (by positivity) hu
          _ ≤ (rexp 1 + 1) ^ β * (1 + u ^ β) := by nlinarith

/-- The domination: for `0 < t ≤ e^{-1}` and `u > 0`,
`A₋(u/t) t^α / (log 1/t)^β ≤ C (e + 1)^β (u^α + u^{α+β})`. -/
lemma dominated {α β C t u : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hb : ∀ x, 0 < x → cnt X x ≤ C * (x ^ α * Real.log (rexp 1 + x) ^ β))
    (ht : 0 < t) (ht1 : t ≤ rexp (-1)) (hu : 0 < u) :
    cntLt X (u / t) * t ^ α / Real.log (1 / t) ^ β ≤ C * (rexp 1 + 1) ^ β * (u ^ α + u ^ (α + β)) := by
  have hL : 1 ≤ Real.log (1 / t) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ ht]
    have := Real.exp_add 1 (-1); rw [add_neg_cancel, Real.exp_zero] at this
    nlinarith [exp_pos 1]
  have ht1' : t ≤ 1 := le_trans ht1 (by rw [Real.exp_le_one_iff]; norm_num)
  have hx : 0 < u / t := by positivity
  -- log(e + u/t) ≤ log(1/t) (1 + log(e + u))
  have hlog : Real.log (rexp 1 + u / t) ≤ Real.log (1 / t) * (1 + Real.log (rexp 1 + u)) := by
    have e1 : rexp 1 + u / t ≤ (rexp 1 + u) * (1 / t) := by
      rw [add_mul, mul_one_div, mul_one_div]
      have : rexp 1 ≤ rexp 1 / t := by rw [le_div_iff₀ ht]; nlinarith [exp_pos 1]
      linarith
    have e2 := Real.log_le_log (by positivity) e1
    rw [Real.log_mul (by positivity) (by positivity)] at e2
    have : 0 ≤ Real.log (rexp 1 + u) := Real.log_nonneg (by linarith [Real.add_one_le_exp 1])
    nlinarith
  have hl0 : 0 ≤ Real.log (rexp 1 + u / t) :=
    Real.log_nonneg (by linarith [Real.add_one_le_exp 1, hx.le])
  calc cntLt X (u / t) * t ^ α / Real.log (1 / t) ^ β
      ≤ C * ((u / t) ^ α * Real.log (rexp 1 + u / t) ^ β) * t ^ α / Real.log (1 / t) ^ β := by
        gcongr; exact le_trans (cntLt_le_cnt X _) (hb _ hx)
    _ = C * u ^ α * (Real.log (rexp 1 + u / t) / Real.log (1 / t)) ^ β := by
        have e : (u / t) ^ α * t ^ α = u ^ α := by
          rw [← Real.mul_rpow hx.le ht.le, div_mul_cancel₀ _ ht.ne']
        rw [Real.div_rpow hl0 (by linarith), ← e]
        field_simp
        ring
    _ ≤ C * u ^ α * (1 + Real.log (rexp 1 + u)) ^ β := by
        gcongr
        rw [div_le_iff₀ (by linarith)]; linarith
    _ ≤ C * u ^ α * ((rexp 1 + 1) ^ β * (1 + u ^ β)) := by
        gcongr; exact one_add_log_le hu.le β hβ
    _ = C * (rexp 1 + 1) ^ β * (u ^ α + u ^ (α + β)) := by
        rw [Real.rpow_add hu]; ring

/-- **The Abelian theorem for the heat transform.**  If `A(x) ~ c x^α (log x)^β` with `α > 0`
and `β ≥ 0`, then `t^α K(t) / (log 1/t)^β → c Γ(α + 1)` as `t → 0⁺`. -/
theorem heat_abelian {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c)) :
    Tendsto (fun t => heat X t * t ^ α / Real.log (1 / t) ^ β) (𝓝[>] 0)
      (𝓝 (c * Real.Gamma (α + 1))) := by
  obtain ⟨C, hC, hb⟩ := cnt_bound X hα hβ hA
  set F : ℝ → ℝ → ℝ := fun t u => rexp (-u) * (cntLt X (u / t) * t ^ α / Real.log (1 / t) ^ β)
  have hG : c * Real.Gamma (α + 1) = ∫ u in Ioi 0, c * (rexp (-u) * u ^ α) := by
    rw [Real.Gamma_eq_integral (by linarith), integral_const_mul]; simp
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      heat X t * t ^ α / Real.log (1 / t) ^ β = ∫ u in Ioi 0, F t u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [heat_eq_integral X ht, mul_div_assoc, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [F]; ring
  rw [hG]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  set g : ℝ → ℝ := fun u => rexp (-u) * (C * (rexp 1 + 1) ^ β * (u ^ α + u ^ (α + β)))
  refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    have hm : Measurable fun u => cntLt X (u / t) :=
      ((cntLt_mono X).comp fun a b hab => div_le_div_of_nonneg_right hab ht'.le).measurable
    exact ((measurable_neg.exp).mul ((hm.mul_const _).div_const _)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (exp_pos (-1))] with t ht ht2
    have ht' : 0 < t := ht
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu' : 0 < u := hu
    have hF0 : 0 ≤ F t u := by
      have : 0 ≤ cntLt X (u / t) := le_trans (by unfold cntLt; positivity) le_rfl
      have : 0 < Real.log (1 / t) := by
        rw [one_div]; exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨ht', lt_of_lt_of_le ht2.2
          (by rw [Real.exp_le_one_iff]; norm_num)⟩ |> fun h => by
            exact (one_lt_inv_iff₀.mpr ⟨ht', lt_of_lt_of_le ht2.2 (by
              rw [Real.exp_le_one_iff]; norm_num)⟩))
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    exact mul_le_mul_of_nonneg_left (dominated X hβ hC hb ht' ht2.2.le hu') (exp_pos _).le
  · have i1 : IntegrableOn (fun u : ℝ => rexp (-u) * u ^ α) (Ioi 0) := by
      have := Real.GammaIntegral_convergent (show 0 < α + 1 by linarith)
      simpa using this
    have i2 : IntegrableOn (fun u : ℝ => rexp (-u) * u ^ (α + β)) (Ioi 0) := by
      have := Real.GammaIntegral_convergent (show 0 < α + β + 1 by linarith)
      simpa using this
    have := (i1.add i2).const_mul (C * (rexp 1 + 1) ^ β)
    have hfun : g = fun x => C * (rexp 1 + 1) ^ β *
        (((fun u => rexp (-u) * u ^ α) + fun u => rexp (-u) * u ^ (α + β)) x) := by
      funext u; simp only [g, Pi.add_apply]; ring
    rw [hfun]; exact this
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have h := (pointwise X hα hβ (show 0 < u from hu) hA).const_mul (rexp (-u))
    convert h using 2
    ring

/-! ### The Dirichlet transform -/

/-- The Dirichlet series `Z(s) = Σ_{n ∈ X, n ≥ 1} n^{−s}`. -/
noncomputable def dirichlet (s : ℝ) : ℝ := ∑' n : ℕ, if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0

lemma integral_term_d {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) :
    ∫ v in Ioi 0, (Ioi (Real.log n)).indicator (fun v => s * rexp (-(s * v))) v = (n : ℝ) ^ (-s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, sup_eq_left.mpr hl, integral_const_mul]
  have := integral_exp_mul_Ioi (show -s < 0 by linarith) (Real.log n)
  simp only [neg_mul] at this
  rw [this, Real.rpow_def_of_pos hn']
  field_simp
  ring_nf

/-- `Z(s) = s ∫₀^∞ e^{−sv} A₋(e^v) dv` for `s > 0`, when `Z(s)` converges absolutely. -/
theorem dirichlet_eq_integral {s : ℝ} (hs : 0 < s)
    (hsum : Summable fun n : ℕ => if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0) :
    dirichlet X s = ∫ v in Ioi 0, s * rexp (-(s * v)) * cntLt X (rexp v) := by
  set f : ℕ → ℝ → ℝ := fun n v =>
    if 1 ≤ n ∧ X n then (Ioi (Real.log n)).indicator (fun v => s * rexp (-(s * v))) v else 0
  have hf : ∀ n, ∫ v in Ioi 0, f n v = if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0 := by
    intro n; simp only [f]; split_ifs with h
    · exact integral_term_d hs h.1
    · simp
  have hnn : ∀ n v, 0 ≤ f n v := by
    intro n v; simp only [f]; split_ifs
    · exact indicator_nonneg (fun _ _ => by positivity) _
    · exact le_rfl
  have hint : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := by
    intro n; simp only [f]; split_ifs
    · have h1 : IntegrableOn (fun v : ℝ => s * rexp (-(s * v))) (Ioi 0) := by
        simpa [neg_mul] using (exp_neg_integrableOn_Ioi 0 hs).const_mul s
      exact h1.indicator measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hlin : ∀ n, ∫⁻ v in Ioi 0, ‖f n v‖ₑ =
      ENNReal.ofReal (if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0) := by
    intro n
    rw [← hf n, ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun v => hnn n v)]
    refine lintegral_congr fun v => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn n v)]
  have hsum' : ∑' n, ∫⁻ v in Ioi 0, ‖f n v‖ₑ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> positivity) hsum]
    exact ENNReal.ofReal_ne_top
  rw [dirichlet, ← tsum_congr hf,
    ← integral_tsum (fun n => (hint n).aestronglyMeasurable) hsum']
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [tsum_eq_sum (s := Finset.range ⌈rexp v⌉₊)]
  · rw [cntLt, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hlt := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    simp only [f]
    split_ifs with h
    · have hn' : (0 : ℝ) < n := by exact_mod_cast h.1
      have : Real.log n < v := by rw [Real.log_lt_iff_lt_exp hn']; exact hlt
      simp [indicator, this]
    · simp
  · intro n hn
    rw [Finset.mem_range, not_lt, Nat.ceil_le] at hn
    simp only [f]; split_ifs with h
    · have hn' : (0 : ℝ) < n := by exact_mod_cast h.1
      have : v ≤ Real.log n := by rw [Real.le_log_iff_exp_le hn']; exact hn
      simp [indicator, not_lt.mpr this]
    · rfl

lemma log_e_add_exp_le {y : ℝ} (hy : 0 ≤ y) : Real.log (rexp 1 + rexp y) ≤ 2 + y := by
  have h1 : rexp 1 + rexp y ≤ rexp (2 + y) := by
    rw [Real.exp_add]
    have e1 : rexp 1 ≤ rexp 1 * rexp y := le_mul_of_one_le_right (exp_pos 1).le (Real.one_le_exp hy)
    have e2 : rexp y ≤ rexp 1 * rexp y := le_mul_of_one_le_left (exp_pos y).le
      (Real.one_le_exp zero_le_one)
    have e3 : rexp 2 = rexp 1 * rexp 1 := by rw [← Real.exp_add]; norm_num
    have e4 : 2 ≤ rexp 1 := by linarith [Real.add_one_le_exp 1]
    rw [e3]; nlinarith [exp_pos 1, exp_pos y]
  calc Real.log (rexp 1 + rexp y) ≤ Real.log (rexp (2 + y)) := Real.log_le_log (by positivity) h1
    _ = 2 + y := Real.log_exp _

lemma two_add_le {w : ℝ} (hw : 0 ≤ w) (β : ℝ) (hβ : 0 ≤ β) :
    (2 + w) ^ β ≤ 3 ^ β * (1 + w ^ β) := by
  have h3 : 0 ≤ (3 : ℝ) ^ β := by positivity
  rcases le_or_lt w 1 with h | h
  · calc (2 + w) ^ β ≤ 3 ^ β := Real.rpow_le_rpow (by linarith) (by linarith) hβ
      _ ≤ 3 ^ β * (1 + w ^ β) := by have : 0 ≤ w ^ β := by positivity
                                    nlinarith
  · calc (2 + w) ^ β ≤ (3 * w) ^ β := Real.rpow_le_rpow (by linarith) (by linarith) hβ
      _ = 3 ^ β * w ^ β := Real.mul_rpow (by norm_num) hw
      _ ≤ 3 ^ β * (1 + w ^ β) := by nlinarith

/-- **Convergence from the count**: if `A(x) ~ c x^α (log x)^β` (`α > 0`, `β ≥ 0`), then `Z(s)`
converges for every `s > α`.  (Tonelli in `ℝ≥0∞`: `Σ n^{−s} = ∫ s e^{−sv} A₋(e^v) dv`, and the
integrand is at most `s C 3^β (1 + v^β) e^{−(s−α)v}`.) -/
theorem dirichlet_summable {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c)) {s : ℝ} (hs : α < s) :
    Summable fun n : ℕ => if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0 := by
  obtain ⟨C, hC, hb⟩ := cnt_bound X hα hβ hA
  have hs0 : 0 < s := by linarith
  set t : ℕ → ℝ := fun n => if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0
  have ht0 : ∀ n, 0 ≤ t n := fun n => by simp only [t]; split_ifs <;> positivity
  set f : ℕ → ℝ → ℝ := fun n v =>
    if 1 ≤ n ∧ X n then (Ioi (Real.log n)).indicator (fun v => s * rexp (-(s * v))) v else 0
  have hnn : ∀ n v, 0 ≤ f n v := by
    intro n v; simp only [f]; split_ifs
    · exact indicator_nonneg (fun _ _ => by positivity) _
    · exact le_rfl
  have hint : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := by
    intro n; simp only [f]; split_ifs
    · have h1 : IntegrableOn (fun v : ℝ => s * rexp (-(s * v))) (Ioi 0) := by
        simpa [neg_mul] using (exp_neg_integrableOn_Ioi 0 hs0).const_mul s
      exact h1.indicator measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hf : ∀ n, ∫⁻ v in Ioi 0, ENNReal.ofReal (f n v) = ENNReal.ofReal (t n) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall fun v => hnn n v)]
    congr 1
    simp only [f, t]; split_ifs with h
    · exact integral_term_d hs0 h.1
    · simp
  -- the pointwise sum is the count
  have hsum : ∀ v, ∑' n, ENNReal.ofReal (f n v) =
      ENNReal.ofReal (s * rexp (-(s * v)) * cntLt X (rexp v)) := by
    intro v
    rw [tsum_eq_sum (s := Finset.range ⌈rexp v⌉₊)]
    · rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn n v)]
      congr 1
      rw [cntLt, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hlt := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
      simp only [f]
      split_ifs with h
      · have hn' : (0 : ℝ) < n := by exact_mod_cast h.1
        have : Real.log n < v := by rw [Real.log_lt_iff_lt_exp hn']; exact hlt
        simp [indicator, this]
      · simp
    · intro n hn
      rw [Finset.mem_range, not_lt, Nat.ceil_le] at hn
      simp only [f]; split_ifs with h
      · have hn' : (0 : ℝ) < n := by exact_mod_cast h.1
        have : v ≤ Real.log n := by rw [Real.le_log_iff_exp_le hn']; exact hn
        simp [indicator, not_lt.mpr this]
      · simp
  -- the bound
  set g : ℝ → ℝ := fun v => s * C * 3 ^ β * (rexp (-((s - α) * v)) + v ^ β * rexp (-(s - α) * v ^ (1 : ℝ)))
  have hg : IntegrableOn g (Ioi 0) := by
    have i1 := exp_neg_integrableOn_Ioi 0 (show 0 < s - α by linarith)
    have i2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := β) (b := s - α) (by linarith)
      le_rfl (by linarith)
    have := (i1.add i2).const_mul (s * C * 3 ^ β)
    have hfun : g = fun x => s * C * 3 ^ β *
        (((fun x => rexp (-(s - α) * x)) + fun x => x ^ β * rexp (-(s - α) * x ^ (1 : ℝ))) x) := by
      funext v; simp only [g, Pi.add_apply, neg_mul]
    rw [hfun]; exact this
  have hle : ∀ v ∈ Ioi (0 : ℝ), s * rexp (-(s * v)) * cntLt X (rexp v) ≤ g v := by
    intro v hv
    have hv' : 0 < v := hv
    have hcnt : cntLt X (rexp v) ≤ C * (rexp (α * v) * Real.log (rexp 1 + rexp v) ^ β) := by
      have := le_trans (cntLt_le_cnt X (rexp v)) (hb _ (exp_pos v))
      rwa [← Real.exp_mul, mul_comm v α] at this
    have hl0 : 0 ≤ Real.log (rexp 1 + rexp v) :=
      Real.log_nonneg (by linarith [Real.add_one_le_exp 1, exp_pos v])
    have hlog : Real.log (rexp 1 + rexp v) ^ β ≤ 3 ^ β * (1 + v ^ β) :=
      le_trans (Real.rpow_le_rpow hl0 (log_e_add_exp_le hv'.le) hβ) (two_add_le hv'.le β hβ)
    have e1 : rexp (-(s * v)) * rexp (α * v) = rexp (-((s - α) * v)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc s * rexp (-(s * v)) * cntLt X (rexp v)
        ≤ s * rexp (-(s * v)) * (C * (rexp (α * v) * (3 ^ β * (1 + v ^ β)))) := by
          gcongr; exact le_trans hcnt (by gcongr)
      _ = s * C * 3 ^ β * (rexp (-((s - α) * v)) * (1 + v ^ β)) := by rw [← e1]; ring
      _ = g v := by simp only [g, Real.rpow_one]; ring_nf
  have hfin : ∑' n, ENNReal.ofReal (t n) ≠ ⊤ := by
    rw [← tsum_congr hf, ← lintegral_tsum (fun n => (hint n).aemeasurable.ennreal_ofReal)]
    simp_rw [hsum]
    refine (lt_of_le_of_lt (lintegral_mono_ae ?_) hg.lintegral_lt_top).ne
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun v hv => ENNReal.ofReal_le_ofReal (hle v hv))
  have := ENNReal.summable_toReal hfin
  simpa [ENNReal.toReal_ofReal (ht0 _)] using this

/-- **The Abelian theorem for the Dirichlet transform.**  If `A(x) ~ c x^α (log x)^β` with
`α > 0`, `β ≥ 0`, then `ε^{β+1} Z(α + ε) → c α Γ(β + 1)` as `ε → 0⁺` (convergence for `s > α`
follows from the count, `dirichlet_summable`).  This is a normalized limit; it reads as
`Z(α + ε) ~ c α Γ(β + 1) ε^{−(β+1)}` only when `c > 0`. -/
theorem dirichlet_abelian {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : Tendsto (fun x => cnt X x / (x ^ α * Real.log x ^ β)) atTop (𝓝 c)) :
    Tendsto (fun ε => dirichlet X (α + ε) * ε ^ (β + 1)) (𝓝[>] 0)
      (𝓝 (c * α * Real.Gamma (β + 1))) := by
  obtain ⟨C, hC, hb⟩ := cnt_bound X hα hβ hA
  -- the integrand after `v = w/ε`
  set F : ℝ → ℝ → ℝ := fun ε w =>
    (α + ε) * rexp (-w) * (cntLt X (rexp (w / ε)) * rexp (-(α * (w / ε))) * ε ^ β)
  have hG : c * α * Real.Gamma (β + 1) = ∫ w in Ioi 0, α * rexp (-w) * (c * w ^ β) := by
    rw [Real.Gamma_eq_integral (by linarith), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    simp only [add_sub_cancel_right]; ring
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      dirichlet X (α + ε) * ε ^ (β + 1) = ∫ w in Ioi 0, F ε w := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    rw [dirichlet_eq_integral X (by linarith) (dirichlet_summable X hα hβ hA (by linarith))]
    set G : ℝ → ℝ := fun v => (α + ε) * rexp (-((α + ε) * v)) * cntLt X (rexp v)
    have hsub := integral_comp_mul_left_Ioi G 0 (inv_pos.mpr hε')
    simp only [mul_zero, inv_inv, smul_eq_mul] at hsub
    have hI : (∫ v in Ioi 0, G v) = ε⁻¹ * ∫ x in Ioi 0, G (ε⁻¹ * x) := by
      rw [hsub, ← mul_assoc, inv_mul_cancel₀ hε'.ne', one_mul]
    have hpow : ε⁻¹ * ε ^ (β + 1) = ε ^ β := by
      rw [Real.rpow_add hε', Real.rpow_one]; field_simp
    rw [show (∫ v in Ioi 0, (α + ε) * rexp (-((α + ε) * v)) * cntLt X (rexp v)) =
      ∫ v in Ioi 0, G v from rfl, hI, mul_comm (ε⁻¹) _, mul_assoc, hpow, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    simp only [F]
    have e1 : rexp (-((α + ε) * (ε⁻¹ * w))) = rexp (-w) * rexp (-(α * (w / ε))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    simp only [G]
    rw [e1, show ε⁻¹ * w = w / ε by ring]
    ring
  rw [hG]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  set g : ℝ → ℝ := fun w => (α + 1) * rexp (-w) * (C * 3 ^ β * (1 + w ^ β))
  refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hm : Measurable fun w => cntLt X (rexp (w / ε)) :=
      ((cntLt_mono X).comp fun a b hab => Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right hab hε'.le)).measurable
    refine (((measurable_const.mul (measurable_neg.exp)).mul
      ((hm.mul ((measurable_id.div_const ε).const_mul α).neg.exp).mul_const _))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε hε1
    have hε' : 0 < ε := hε
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    have hw' : 0 < w := hw
    have hy : 0 ≤ w / ε := by positivity
    have hcnt : cntLt X (rexp (w / ε)) ≤
        C * (rexp (α * (w / ε)) * Real.log (rexp 1 + rexp (w / ε)) ^ β) := by
      have := le_trans (cntLt_le_cnt X (rexp (w / ε))) (hb _ (exp_pos (w / ε)))
      rwa [← Real.exp_mul, mul_comm (w / ε) α] at this
    have hlog := log_e_add_exp_le hy
    have hl0 : 0 ≤ Real.log (rexp 1 + rexp (w / ε)) :=
      Real.log_nonneg (by linarith [Real.add_one_le_exp 1, exp_pos (w / ε)])
    have hbr : cntLt X (rexp (w / ε)) * rexp (-(α * (w / ε))) * ε ^ β ≤ C * 3 ^ β * (1 + w ^ β) := by
      calc cntLt X (rexp (w / ε)) * rexp (-(α * (w / ε))) * ε ^ β
          ≤ C * (rexp (α * (w / ε)) * Real.log (rexp 1 + rexp (w / ε)) ^ β) *
              rexp (-(α * (w / ε))) * ε ^ β := by gcongr
        _ = C * (Real.log (rexp 1 + rexp (w / ε)) ^ β * ε ^ β) := by
            rw [show rexp (-(α * (w / ε))) = (rexp (α * (w / ε)))⁻¹ from Real.exp_neg _]
            field_simp
            ring
        _ ≤ C * ((2 + w / ε) ^ β * ε ^ β) := by gcongr
        _ = C * (2 * ε + w) ^ β := by
            rw [← Real.mul_rpow (by positivity) hε'.le]; congr 2; field_simp
        _ ≤ C * (2 + w) ^ β := by gcongr; linarith [hε1.2]
        _ ≤ C * (3 ^ β * (1 + w ^ β)) := by gcongr; exact two_add_le hw'.le β hβ
        _ = C * 3 ^ β * (1 + w ^ β) := by ring
    have hF0 : 0 ≤ F ε w := by
      have : 0 ≤ cntLt X (rexp (w / ε)) := by unfold cntLt; positivity
      simp only [F]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    simp only [F, g]
    have : α + ε ≤ α + 1 := by linarith [hε1.2]
    have h0 : 0 ≤ cntLt X (rexp (w / ε)) * rexp (-(α * (w / ε))) * ε ^ β := by
      have : 0 ≤ cntLt X (rexp (w / ε)) := by unfold cntLt; positivity
      positivity
    gcongr
  · have i1 : IntegrableOn (fun w : ℝ => rexp (-w) * w ^ (0 : ℝ)) (Ioi 0) := by
      have := Real.GammaIntegral_convergent (show (0 : ℝ) < 1 by norm_num); simpa using this
    have i2 : IntegrableOn (fun w : ℝ => rexp (-w) * w ^ β) (Ioi 0) := by
      have := Real.GammaIntegral_convergent (show 0 < β + 1 by linarith); simpa using this
    have := (i1.add i2).const_mul ((α + 1) * (C * 3 ^ β))
    have hfun : g = fun x => (α + 1) * (C * 3 ^ β) *
        (((fun w => rexp (-w) * w ^ (0 : ℝ)) + fun w => rexp (-w) * w ^ β) x) := by
      funext w; simp only [g, Pi.add_apply, Real.rpow_zero]; ring
    rw [hfun]; exact this
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    have hw' : 0 < w := hw
    -- `x = e^{w/ε} → ∞`
    have hx : Tendsto (fun ε => rexp (w / ε)) (𝓝[>] 0) atTop :=
      tendsto_exp_atTop.comp (tendsto_div_t hw')
    have h1 := (cntLt_asymp X hα hβ hA).comp hx
    have h2 : Tendsto (fun ε : ℝ => α + ε) (𝓝[>] 0) (𝓝 α) := by
      have : Tendsto (fun ε : ℝ => α + ε) (𝓝 0) (𝓝 (α + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this; exact this.mono_left nhdsWithin_le_nhds
    have h3 := (h2.mul_const (rexp (-w))).mul (h1.mul_const (w ^ β))
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    simp only [Function.comp, F]
    have e1 : rexp (w / ε) ^ α = rexp (α * (w / ε)) := by rw [← Real.exp_mul, mul_comm]
    have e2 : Real.log (rexp (w / ε)) = w / ε := Real.log_exp _
    have e3 : (w / ε) ^ β * ε ^ β = w ^ β := by
      rw [← Real.mul_rpow (by positivity) hε'.le, div_mul_cancel₀ _ hε'.ne']
    have e4 : rexp (-(α * (w / ε))) = (rexp (α * (w / ε)))⁻¹ := Real.exp_neg _
    rw [e1, e2, e4, ← e3]
    field_simp
    ring

/-! ### Finite support -/

/-- **Finite support**: if every hit is below `N`, the heat transform tends to the exact number of
hits, and the Dirichlet series is the finite sum (a Dirichlet polynomial, entire in `s`). -/
theorem heat_finite {N : ℕ} (hN : ∀ n, N ≤ n → ¬ X n) :
    Tendsto (heat X) (𝓝[>] 0) (𝓝 ((Finset.range N).filter (fun n => 1 ≤ n ∧ X n)).card) ∧
    ∀ s, dirichlet X s = ∑ n ∈ Finset.range N, if 1 ≤ n ∧ X n then (n : ℝ) ^ (-s) else 0 := by
  have hz : ∀ (f : ℕ → ℝ) n, n ∉ Finset.range N → (if 1 ≤ n ∧ X n then f n else 0) = 0 := by
    intro f n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [if_neg (fun h => hN n hn h.2)]
  have hheat : ∀ t, heat X t = ∑ n ∈ Finset.range N, if 1 ≤ n ∧ X n then rexp (-(t * n)) else 0 :=
    fun t => tsum_eq_sum (fun n hn => hz (fun n => rexp (-(t * n))) n hn)
  refine ⟨?_, fun s => tsum_eq_sum (fun n hn => hz (fun n => (n : ℝ) ^ (-s)) n hn)⟩
  have hlim : Tendsto (fun t : ℝ => ∑ n ∈ Finset.range N,
      if 1 ≤ n ∧ X n then rexp (-(t * n)) else 0) (𝓝 0)
      (𝓝 (∑ n ∈ Finset.range N, if 1 ≤ n ∧ X n then rexp (-((0 : ℝ) * n)) else 0)) := by
    refine tendsto_finset_sum _ fun n _ => ?_
    split_ifs
    · exact ((continuous_id.mul continuous_const).neg.rexp.tendsto 0)
    · exact tendsto_const_nhds
  simp only [zero_mul, neg_zero, Real.exp_zero] at hlim
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact (hlim.mono_left nhdsWithin_le_nhds).congr (fun t => (hheat t).symm)

end PerfectPower.AbelianTransforms
