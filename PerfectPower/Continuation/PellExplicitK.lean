import PerfectPower.Continuation.ExplicitK

/-!
# Explicit error constants: the Pell type

`PellExact.pell_exact_count` bounds `|A(N) - κ log N|` by `|B| + 1 + Σ_ρ K_ρ + κ log(2A + |B|)`,
where each `K_ρ` comes from `count_near_geometric`.  That lemma uses a lower constant `c₁`
obtained as a minimum over finitely many early terms, which is not explicit.  This file replaces
it:

* `count_near_geometric_of_lower`: the same count, with `c₁` an input and
  `K = |log c₁| / log E + 1 + |log (a + b)| / log E`.
* `orbit_lower`: along the orbit of a quadrant solution, `X_j ≥ η ε^j / (2 + √|Δ|)`, because
  `Y_j √D ≤ X_j + √|Δ|` and `X_j ≥ 1`.
* `class_count_explicit`: one residue class costs at most
  `Kc W = 3 + (2 log (W + |Δ|) + log (2 + √|Δ|) + log 2) / log ε`, for any `W ≥ max(1, η)`.
* `orbit_count_explicit`: one orbit with period `P` costs at most `P · Kc W`.
-/

open Finset
open scoped Classical

namespace PerfectPower.PellExact

open PerfectPower

/-- `count_near_geometric` with the lower constant as an input. -/
theorem count_near_geometric_of_lower {f : ℕ → ℝ} {E a b c₁ : ℝ} (hE : 1 < E) (ha : 0 < a)
    (hb : 0 ≤ b) (hf : ∀ h, |f h - a * E ^ h| ≤ b) (hc₁ : 0 < c₁)
    (hlow : ∀ h, c₁ * E ^ h ≤ f h) :
    ∀ (M : ℝ) (L : ℕ), 1 ≤ M → (∀ h, f h ≤ M → h < L) →
      |(((Finset.range L).filter (fun h => f h ≤ M)).card : ℝ) - Real.log M / Real.log E| ≤
        |Real.log c₁| / Real.log E + 1 + |Real.log (a + b)| / Real.log E := by
  have hlogE : 0 < Real.log E := Real.log_pos hE
  set c₂ := a + b
  have hc₂ : 0 < c₂ := by positivity
  have hup : ∀ h, f h ≤ c₂ * E ^ h := by
    intro h
    have h1 := (abs_le.mp (hf h)).2
    have hEh : 1 ≤ E ^ h := one_le_pow₀ hE.le
    have e : c₂ * E ^ h = a * E ^ h + b * E ^ h := by simp only [c₂]; ring
    have : b ≤ b * E ^ h := le_mul_of_one_le_right hb hEh
    linarith
  intro M L hM hL
  have hM0 : 0 < M := by linarith
  set cnt := (((Finset.range L).filter (fun h => f h ≤ M)).card : ℝ)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hupper : cnt ≤ Real.log M / Real.log E + |Real.log c₁| / Real.log E + 1 := by
    rcases le_or_lt c₁ M with h1 | h1
    · have := geometric_count_le hE hc₁ h1 hlow L
      rw [Real.log_div hM0.ne' hc₁.ne', sub_div] at this
      have : -(Real.log c₁ / Real.log E) ≤ |Real.log c₁| / Real.log E := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_le_abs _) hlogE.le
      linarith
    · have hzero : (Finset.range L).filter (fun h => f h ≤ M) = ∅ := by
        apply Finset.filter_false_of_mem
        intro h _ hh
        have := hlow h
        have : c₁ ≤ c₁ * E ^ h := le_mul_of_one_le_right hc₁.le (one_le_pow₀ hE.le)
        linarith
      have : cnt = 0 := by simp only [cnt, hzero, Finset.card_empty, Nat.cast_zero]
      have := div_nonneg (abs_nonneg (Real.log c₁)) hlogE.le
      have := div_nonneg hlogM hlogE.le
      linarith
  have hlower : Real.log M / Real.log E - |Real.log c₂| / Real.log E ≤ cnt := by
    have hLb : Real.log (M / c₂) / Real.log E < L := by
      set q := Real.log (M / c₂) / Real.log E
      rcases lt_or_le q 0 with hq | hq
      · exact hq.trans_le (Nat.cast_nonneg _)
      · have hfl := Nat.floor_le hq
        have hmem := le_of_index_le_geometric hE hc₂ hM0 hup hfl
        have := hL _ hmem
        have : (⌊q⌋₊ : ℝ) + 1 ≤ L := by exact_mod_cast this
        linarith [Nat.lt_floor_add_one q]
    have := le_geometric_count hE hc₂ hM0 hup L hLb
    rw [Real.log_div hM0.ne' hc₂.ne', sub_div] at this
    have : Real.log c₂ / Real.log E ≤ |Real.log c₂| / Real.log E :=
      div_le_div_of_nonneg_right (le_abs_self _) hlogE.le
    linarith
  rw [abs_le]
  constructor <;> linarith [div_nonneg (abs_nonneg (Real.log c₁)) hlogE.le,
    div_nonneg (abs_nonneg (Real.log c₂)) hlogE.le]

variable {D u v Δ : ℤ}

lemma eta_ge_one {p : ℤ × ℤ} (hp : Sol D Δ p) : 1 ≤ eta D p := by
  have hX : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hY : (0 : ℝ) ≤ p.2 := by exact_mod_cast hp.2.1
  have := Real.sqrt_nonneg (D : ℝ)
  simp only [eta]; nlinarith

lemma etaBar_abs_le {p : ℤ × ℤ} (hD : 0 ≤ D) (hp : Sol D Δ p) : |etaBar D p| ≤ |(Δ : ℝ)| := by
  have h1 := eta_ge_one hp
  have hprod : eta D p * etaBar D p = Δ := by
    simp only [eta, etaBar]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ D by exact_mod_cast hD)
    have hN : ((p.1 : ℝ) ^ 2 - D * p.2 ^ 2) = Δ := by exact_mod_cast hp.2.2
    nlinarith
  have : |eta D p| * |etaBar D p| = |(Δ : ℝ)| := by rw [← abs_mul, hprod]
  rw [abs_of_pos (by linarith)] at this
  nlinarith [abs_nonneg (etaBar D p)]

/-- For a quadrant solution, `η ≤ (2 + √|Δ|) X`. -/
lemma eta_le_mul_fst {p : ℤ × ℤ} (hD : 0 ≤ D) (hp : Sol D Δ p) :
    eta D p ≤ (2 + Real.sqrt |(Δ : ℝ)|) * p.1 := by
  have hX : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ D by exact_mod_cast hD)
  have hsΔ := Real.sq_sqrt (abs_nonneg (Δ : ℝ))
  have hsΔ0 := Real.sqrt_nonneg |(Δ : ℝ)|
  have hN : ((p.1 : ℝ) ^ 2 - D * p.2 ^ 2) = Δ := by exact_mod_cast hp.2.2
  -- `Y √D ≤ X + √|Δ|`, by comparing squares
  have hYD : (p.2 : ℝ) * Real.sqrt D ≤ p.1 + Real.sqrt |(Δ : ℝ)| := by
    by_contra h
    push_neg at h
    have h0 : 0 ≤ (p.1 : ℝ) + Real.sqrt |(Δ : ℝ)| := by linarith
    have hsq := mul_self_lt_mul_self h0 h
    have e : (p.2 : ℝ) * Real.sqrt D * ((p.2 : ℝ) * Real.sqrt D) = D * p.2 ^ 2 := by
      rw [show (p.2 : ℝ) * Real.sqrt D * ((p.2 : ℝ) * Real.sqrt D) =
        p.2 ^ 2 * (Real.sqrt D) ^ 2 by ring, hs]; ring
    rw [e] at hsq
    nlinarith [le_abs_self (Δ : ℝ), neg_abs_le (Δ : ℝ)]
  simp only [eta]
  nlinarith

/-- **Explicit lower bound along an orbit**: `X_j ≥ η ε^j / (2 + √|Δ|)`. -/
lemma orbit_lower (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) (j : ℕ) :
    eta D ρ * eps D u v ^ j / (2 + Real.sqrt |(Δ : ℝ)|) ≤ (unitOrbit D u v ρ j).1 := by
  have hs := orbit_sol hD hu hu1.le hv hρ j
  have h := eta_le_mul_fst hD hs
  rw [eta_orbit hD] at h
  have hpos : 0 < 2 + Real.sqrt |(Δ : ℝ)| := by positivity
  rw [div_le_iff₀ hpos]
  linarith

/-- The per-class constant. -/
noncomputable def Kc (D u v Δ : ℤ) (W : ℝ) : ℝ :=
  3 + (2 * Real.log (W + |(Δ : ℝ)|) + Real.log (2 + Real.sqrt |(Δ : ℝ)|) + Real.log 2) /
    Real.log (eps D u v)

/-- **One residue class, explicit.**  For a quadrant solution with `η ≤ W`, `1 ≤ W`: -/
theorem class_count_explicit (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) {W : ℝ} (hW : eta D ρ ≤ W) {P : ℕ} (hP : 0 < P) {r : ℕ}
    (hr : r < P) :
    ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L) →
      |((((Finset.range L).filter
          (fun h => ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M)).card : ℕ) : ℝ) -
        Real.log M / (P * Real.log (eps D u v))| ≤ Kc D u v Δ W := by
  have hε := one_lt_eps (D := D) hu1 hv
  have hlogε : 0 < Real.log (eps D u v) := Real.log_pos hε
  have hE : 1 < eps D u v ^ P := one_lt_pow₀ hε hP.ne'
  have hη := eta_ge_one hρ
  have hεr : 1 ≤ eps D u v ^ r := one_le_pow₀ hε.le
  set a := eta D ρ / 2 * eps D u v ^ r
  set b := |etaBar D ρ| / 2
  set c₁ := eta D ρ * eps D u v ^ r / (2 + Real.sqrt |(Δ : ℝ)|)
  have hsΔ0 := Real.sqrt_nonneg |(Δ : ℝ)|
  have ha : 0 < a := by positivity
  have hc₁ : 0 < c₁ := by positivity
  have hlow : ∀ h, c₁ * (eps D u v ^ P) ^ h ≤ ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) := by
    intro h
    have := orbit_lower hD hu hu1 hv hρ (r + P * h)
    rw [pow_add, pow_mul] at this
    simp only [c₁]
    rw [div_mul_eq_mul_div, mul_assoc]
    exact this
  have hf : ∀ h, |((unitOrbit D u v ρ (r + P * h)).1 : ℝ) - a * (eps D u v ^ P) ^ h| ≤ b := by
    intro h
    have := orbit_fst_bracket hD hu hu1 hv ρ (r + P * h)
    rwa [pow_add, pow_mul, ← mul_assoc] at this
  intro M L hM hL
  have hmain := count_near_geometric_of_lower hE ha (by positivity) hf hc₁ hlow M L hM hL
  rw [Real.log_pow] at hmain
  refine hmain.trans ?_
  -- bound the two logarithms
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hΔ0 := abs_nonneg (Δ : ℝ)
  have hlogW : Real.log W ≤ Real.log (W + |(Δ : ℝ)|) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogWΔ : 0 ≤ Real.log (W + |(Δ : ℝ)|) := Real.log_nonneg (by linarith)
  have hlog2Δ : 0 ≤ Real.log (2 + Real.sqrt |(Δ : ℝ)|) := Real.log_nonneg (by linarith)
  have hlogη : Real.log (eta D ρ) ≤ Real.log W := Real.log_le_log (by linarith) hW
  have hlogη0 : 0 ≤ Real.log (eta D ρ) := Real.log_nonneg hη
  have hlogεr : Real.log (eps D u v ^ r) = r * Real.log (eps D u v) := Real.log_pow _ _
  -- `|log c₁| ≤ log W + r log ε + log (2 + √|Δ|)`
  have hc₁log : |Real.log c₁| ≤ Real.log W + r * Real.log (eps D u v) +
      Real.log (2 + Real.sqrt |(Δ : ℝ)|) := by
    have e : Real.log c₁ = Real.log (eta D ρ) + r * Real.log (eps D u v) -
        Real.log (2 + Real.sqrt |(Δ : ℝ)|) := by
      simp only [c₁]
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        hlogεr]
    rw [e, abs_le]
    have : 0 ≤ (r : ℝ) * Real.log (eps D u v) := by positivity
    constructor <;> linarith
  -- `|log (a + b)| ≤ log 2 + log (W + |Δ|) + r log ε`
  have hab : |Real.log (a + b)| ≤ Real.log 2 + Real.log (W + |(Δ : ℝ)|) +
      r * Real.log (eps D u v) := by
    have hb0 : 0 ≤ b := by positivity
    have hbΔ : |etaBar D ρ| ≤ |(Δ : ℝ)| := etaBar_abs_le hD hρ
    have hlow2 : 1 / 2 ≤ a + b := by
      have : 1 ≤ eta D ρ * eps D u v ^ r := by nlinarith
      simp only [a]; nlinarith
    have hup2 : a + b ≤ eps D u v ^ r * (W + |(Δ : ℝ)|) := by
      simp only [a, b]; nlinarith
    rw [abs_le]
    constructor
    · have := Real.log_le_log (by norm_num) hlow2
      rw [one_div, Real.log_inv] at this
      have : 0 ≤ (r : ℝ) * Real.log (eps D u v) := by positivity
      linarith
    · have := Real.log_le_log (by positivity) hup2
      rw [Real.log_mul (by positivity) (by linarith), hlogεr] at this
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
  -- divide by `P log ε ≥ log ε`
  have hPlog : 0 < P * Real.log (eps D u v) := by positivity
  have key : ∀ x y : ℝ, 0 ≤ x → |y| ≤ x + r * Real.log (eps D u v) →
      |y| / (P * Real.log (eps D u v)) ≤ x / Real.log (eps D u v) + 1 := by
    intro x y hx hy
    rw [div_le_iff₀ hPlog]
    have h1 : x ≤ x * P := le_mul_of_one_le_right hx hPr
    have h2 : (r : ℝ) ≤ P := by exact_mod_cast hr.le
    have h3 : (r : ℝ) * Real.log (eps D u v) ≤ P * Real.log (eps D u v) :=
      mul_le_mul_of_nonneg_right h2 hlogε.le
    have e : (x / Real.log (eps D u v) + 1) * (P * Real.log (eps D u v)) =
        x * P + P * Real.log (eps D u v) := by
      field_simp
      ring
    rw [e]
    linarith
  have k1 := key _ _ (by linarith) (by linarith [hc₁log] : |Real.log c₁| ≤
    (Real.log W + Real.log (2 + Real.sqrt |(Δ : ℝ)|)) + r * Real.log (eps D u v))
  have k2 := key _ _ (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
    (by linarith [hab] : |Real.log (a + b)| ≤
      (Real.log 2 + Real.log (W + |(Δ : ℝ)|)) + r * Real.log (eps D u v))
  unfold Kc
  have : (Real.log W + Real.log (2 + Real.sqrt |(Δ : ℝ)|)) / Real.log (eps D u v) +
      (Real.log 2 + Real.log (W + |(Δ : ℝ)|)) / Real.log (eps D u v) ≤
      (2 * Real.log (W + |(Δ : ℝ)|) + Real.log (2 + Real.sqrt |(Δ : ℝ)|) + Real.log 2) /
        Real.log (eps D u v) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hlogε.le
  linarith


/-- **One orbit, explicit**: a period `P` and `η ≤ W` give the constant `P · Kc W`. -/
theorem orbit_count_explicit (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) {W : ℝ} (hW : eta D ρ ≤ W) (m B : ℤ) {P : ℕ} (hP : 0 < P)
    (hper : ∀ j, m ∣ (unitOrbit D u v ρ (j + P)).1 - (unitOrbit D u v ρ j).1) :
    ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | m ∣ (unitOrbit D u v ρ j).1 - B ∧
            ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} : ℕ) : ℝ) -
        (#((range P).filter fun r => m ∣ (unitOrbit D u v ρ r).1 - B) : ℕ) *
          (Real.log M / (P * Real.log (eps D u v)))| ≤ P * Kc D u v Δ W := by
  set G := (range P).filter fun r => m ∣ (unitOrbit D u v ρ r).1 - B
  intro M L hM hL
  have hgood : ∀ j, m ∣ (unitOrbit D u v ρ (j + P)).1 - B ↔ m ∣ (unitOrbit D u v ρ j).1 - B := by
    intro j
    have := hper j
    constructor
    · intro h; have := dvd_sub h this; simpa using this
    · intro h; have := dvd_add h this; simpa using this
  rw [card_split_residue P L hP _ hgood (fun j => ((unitOrbit D u v ρ j).1 : ℝ) ≤ M) hL]
  push_cast
  have hG : ((#G : ℕ) : ℝ) * (Real.log M / (P * Real.log (eps D u v))) =
      ∑ r ∈ G, Real.log M / (P * Real.log (eps D u v)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hG, ← Finset.sum_sub_distrib]
  have hsum : ∑ r ∈ G, Kc D u v Δ W ≤ P * Kc D u v Δ W := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hGP : (#G : ℝ) ≤ P := by
      have : #G ≤ #(range P) := card_filter_le _ _
      rw [card_range] at this; exact_mod_cast this
    have hK0 : 0 ≤ Kc D u v Δ W := by
      unfold Kc
      have hε := one_lt_eps (D := D) hu1 hv
      have hW1 : 1 ≤ W := (eta_ge_one hρ).trans hW
      have := Real.log_nonneg (show (1 : ℝ) ≤ W + |(Δ : ℝ)| by linarith [abs_nonneg (Δ : ℝ)])
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Real.sqrt |(Δ : ℝ)| by
        linarith [Real.sqrt_nonneg |(Δ : ℝ)|])
      have := Real.log_pos hε
      have : 0 ≤ (2 * Real.log (W + |(Δ : ℝ)|) + Real.log (2 + Real.sqrt |(Δ : ℝ)|) +
        Real.log 2) / Real.log (eps D u v) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right hGP hK0
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)).trans hsum
  have hrP : r < P := by simpa [G] using (mem_filter.mp hr).1
  have hLr : ∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L := by
    intro h hh
    have := hL _ hh
    have : h ≤ r + P * h := by nlinarith
    omega
  have := class_count_explicit hD hu hu1 hv hρ hW hP hrP M L hM hLr
  simpa using this

set_option maxHeartbeats 2000000 in
/-- **The core Pell count, with the periods and per-root constants as parameters.** -/
theorem pell_count_core {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (P : ℤ × ℤ → ℕ) (hP0 : ∀ ρ, 0 < P ρ)
    (Kf : ℤ × ℤ → ℝ)
    (hKf : ∀ ρ, IsRoot (4 * A) u v (B ^ 2 - 4 * A * C) ρ → ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, ((unitOrbit (4 * A) u v ρ j).1 : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | 2 * A ∣ (unitOrbit (4 * A) u v ρ j).1 - B ∧
            ((unitOrbit (4 * A) u v ρ j).1 : ℝ) ≤ M} : ℕ) : ℝ) -
        ((#((range (P ρ)).filter fun r => 2 * A ∣ (unitOrbit (4 * A) u v ρ r).1 - B) : ℕ) : ℝ) *
          (Real.log M / (P ρ * Real.log (eps (4 * A) u v)))| ≤ Kf ρ) :
    let R := (roots_finite (Δ := B ^ 2 - 4 * A * C) (by positivity : (0 : ℤ) < 4 * A) hu1 hv
      hu).toFinset
    let g : ℤ × ℤ → ℕ := fun ρ =>
      #((range (P ρ)).filter fun r => 2 * A ∣ (unitOrbit (4 * A) u v ρ r).1 - B)
    ∀ N : ℕ, B.natAbs + 1 ≤ N →
      |((#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℕ) : ℝ) -
          (∑ ρ ∈ R, (g ρ : ℝ) / P ρ) / Real.log (eps (4 * A) u v) * Real.log N| ≤
        |B| + 1 + ∑ ρ ∈ R, Kf ρ +
          (∑ ρ ∈ R, (g ρ : ℝ) / P ρ) / Real.log (eps (4 * A) u v) * Real.log (2 * A + |B|) := by
  intro R g
  set D := 4 * A
  set Δ := B ^ 2 - 4 * A * C
  have hD : 0 < D := by positivity
  have hu' : u ^ 2 - D * v ^ 2 = 1 := hu
  have hfin := roots_finite (Δ := Δ) hD hu1 hv hu'
  have hroot : ∀ ρ ∈ R, Sol D Δ ρ := fun ρ hρ => (hfin.mem_toFinset.mp hρ).1
  have hε := one_lt_eps (D := D) hu1 hv.le
  have hlogε : 0 < Real.log (eps D u v) := Real.log_pos hε
  set κ := (∑ ρ ∈ R, (g ρ : ℝ) / P ρ) / Real.log (eps D u v)
  have hκ : 0 ≤ κ := div_nonneg (sum_nonneg fun ρ _ => by positivity) hlogε.le
  intro N hN
  -- the parameter range
  set M : ℝ := 2 * A * N + B
  set L : ℕ := (2 * A * N + |B|).toNat + 1
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hBN : (|B| : ℝ) + 1 ≤ N := by
    have : ((B.natAbs : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hN
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hBr : -(|B| : ℝ) ≤ B := by exact_mod_cast neg_abs_le B
  have hBr' : (B : ℝ) ≤ |B| := by exact_mod_cast le_abs_self B
  have hMN : (N : ℝ) ≤ M := by simp only [M]; nlinarith
  have hM1 : (1 : ℝ) ≤ M := hNpos.trans hMN
  have hMup : M ≤ (2 * A + |B|) * N := by
    have : ((|B| : ℤ) : ℝ) ≤ ((|B| : ℤ) : ℝ) * N :=
      le_mul_of_one_le_right (by exact_mod_cast abs_nonneg B) hNpos
    simp only [M]; push_cast at this ⊢; nlinarith [le_abs_self (B : ℝ)]
  have hjL : ∀ ρ, Sol D Δ ρ → ∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L := by
    intro ρ hρ j hj
    have h1 := index_lt_fst hD.le hu1 hv.le hρ j
    have h2 : (unitOrbit D u v ρ j).1 ≤ 2 * A * N + |B| := by
      have : ((unitOrbit D u v ρ j).1 : ℝ) ≤ 2 * A * N + |B| := by simp only [M] at hj; linarith
      exact_mod_cast this
    have : (j : ℤ) < ((2 * A * N + |B|).toNat : ℤ) + 1 := by
      rw [Int.toNat_of_nonneg (by positivity)]; linarith
    omega
  -- the index set T and its count
  set T := (R ×ˢ range L).filter fun x => 2 * A ∣ (unitOrbit D u v x.1 x.2).1 - B ∧
      ((unitOrbit D u v x.1 x.2).1 : ℝ) ≤ M
  have hTcard : #T = ∑ ρ ∈ R, #{j ∈ range L | 2 * A ∣ (unitOrbit D u v ρ j).1 - B ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} :=
    card_filter_prod R L (fun ρ j => 2 * A ∣ (unitOrbit D u v ρ j).1 - B ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ M)
  set hits := (Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)
  set ψ : (ℤ × ℤ) × ℕ → ℕ := fun x => (((unitOrbit D u v x.1 x.2).1 - B) / (2 * A)).toNat
  -- (A1) hits ≤ #T + |B|
  have hA1 : (#hits : ℤ) ≤ #T + B.natAbs := by
    have hsmall : (hits.filter fun n : ℕ => 2 * A * n + B ≤ 0) ⊆ Icc 1 B.natAbs := by
      intro n hn
      simp only [hits, mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1.1.1, ?_⟩
      have : (n : ℤ) ≤ |B| := by nlinarith [neg_abs_le B, (by exact_mod_cast hn.1.1.1 : (1 : ℤ) ≤ n)]
      have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
      omega
    have hbig : (hits.filter fun n : ℕ => ¬ 2 * A * n + B ≤ 0) ⊆ T.image ψ := by
      intro n hn
      simp only [hits, mem_filter, mem_Icc, not_le] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, hhit⟩, hX⟩ := hn
      obtain ⟨Y, hY⟩ := (quadratic_isHit_iff_norm hA.ne' B C n).mp hhit
      have hs : Sol D Δ (2 * A * n + B, |Y|) := ⟨hX, abs_nonneg Y, by simp only [sq_abs]; exact hY⟩
      obtain ⟨ρ, j, hρ, hj⟩ := exists_root hD hu1 hv hu' _ _ rfl hs
      have hρR : ρ ∈ R := hfin.mem_toFinset.mpr hρ
      have hXM : ((unitOrbit D u v ρ j).1 : ℝ) ≤ M := by
        rw [hj]; simp only [M]; push_cast
        have : (n : ℝ) ≤ N := by exact_mod_cast hnN
        nlinarith
      refine mem_image.mpr ⟨(ρ, j), mem_filter.mpr ⟨mem_product.mpr ⟨hρR,
        mem_range.mpr (hjL ρ hρ.1 j hXM)⟩, ?_, hXM⟩, ?_⟩
      · rw [hj]; exact ⟨n, by ring⟩
      · simp only [ψ, hj]
        rw [show 2 * A * (n : ℤ) + B - B = 2 * A * n by ring,
          Int.mul_ediv_cancel_left _ (by positivity)]
        simp
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := hits)
      (fun n : ℕ => 2 * A * n + B ≤ 0)
    have c1 := card_le_card hsmall
    have c2 := (card_le_card hbig).trans card_image_le
    simp only [Nat.card_Icc, add_tsub_cancel_right] at c1
    omega
  -- (A2) #T ≤ hits + |B|
  have hA2 : (#T : ℤ) ≤ #hits + B.natAbs := by
    have hTsol : ∀ x ∈ T, Sol D Δ (unitOrbit D u v x.1 x.2) := by
      intro x hx
      have := (mem_product.mp (mem_filter.mp hx).1).1
      exact orbit_sol hD.le hu' hu1.le hv.le (hroot _ this) x.2
    have hinj : ∀ x ∈ T, ∀ y ∈ T, (unitOrbit D u v x.1 x.2).1 = (unitOrbit D u v y.1 y.2).1 → x = y := by
      intro x hx y hy hxy
      have e := sol_eq_of_fst hD (hTsol x hx) (hTsol y hy) hxy
      have hx' := hfin.mem_toFinset.mp (mem_product.mp (mem_filter.mp hx).1).1
      have hy' := hfin.mem_toFinset.mp (mem_product.mp (mem_filter.mp hy).1).1
      obtain ⟨e1, e2⟩ := root_unique hD.le hu1 hv.le hu' x.2 y.2 hx' hy' e
      exact Prod.ext e1 e2
    have h1 : (T.filter fun x => B < (unitOrbit D u v x.1 x.2).1).card ≤ #hits := by
      refine card_le_card_of_injOn ψ ?_ ?_
      · intro x hx
        rw [mem_filter] at hx
        obtain ⟨hxT, hxB⟩ := hx
        obtain ⟨-, ⟨k, hk⟩, hxM⟩ := mem_filter.mp hxT
        have hk1 : 1 ≤ k := by nlinarith
        simp only [hits, mem_filter, mem_Icc, ψ]
        rw [hk, Int.mul_ediv_cancel_left _ (by positivity)]
        have hkN : k ≤ N := by
          have : ((2 * A * k + B : ℤ) : ℝ) ≤ M := by rw [← hk]; push_cast; linarith
          simp only [M] at this; push_cast at this
          have : (k : ℝ) ≤ N := by nlinarith
          exact_mod_cast this
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Int.toNat_of_nonneg (by omega)]
        refine (quadratic_isHit_iff_norm hA.ne' B C k).mpr ⟨(unitOrbit D u v x.1 x.2).2, ?_⟩
        rw [show 2 * A * k + B = (unitOrbit D u v x.1 x.2).1 by linarith]
        exact (hTsol x hxT).2.2
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter] at hx hy
        obtain ⟨hxT, hxB⟩ := hx
        obtain ⟨hyT, hyB⟩ := hy
        obtain ⟨-, ⟨k, hk⟩, -⟩ := mem_filter.mp hxT
        obtain ⟨-, ⟨l, hl⟩, -⟩ := mem_filter.mp hyT
        simp only [ψ] at hxy
        rw [hk, hl, Int.mul_ediv_cancel_left _ (by positivity),
          Int.mul_ediv_cancel_left _ (by positivity)] at hxy
        have hk0 : 0 ≤ k := by nlinarith
        have hl0 : 0 ≤ l := by nlinarith
        have : k = l := by omega
        exact hinj x hxT y hyT (by rw [this] at hk; linarith)
    have h2 : (T.filter fun x => ¬ B < (unitOrbit D u v x.1 x.2).1).card ≤ B.natAbs := by
      calc _ ≤ (Icc 1 B.natAbs).card := by
            refine card_le_card_of_injOn (fun x => ((unitOrbit D u v x.1 x.2).1).toNat) ?_ ?_
            · intro x hx
              rw [mem_filter, not_lt] at hx
              obtain ⟨hxT, hxB⟩ := hx
              have hpos := (hTsol x hxT).1
              dsimp only
              rw [mem_Icc]
              have h1 := le_abs_self B
              have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
              constructor <;> omega
            · intro x hx y hy hxy
              rw [mem_coe, mem_filter] at hx hy
              have := (hTsol x hx.1).1
              have := (hTsol y hy.1).1
              exact hinj x hx.1 y hy.1 (by simp only at hxy; omega)
        _ = B.natAbs := by simp
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := T)
      (fun x => B < (unitOrbit D u v x.1 x.2).1)
    omega
  -- (B) the per-root estimates
  have hB' : |(#T : ℝ) - κ * Real.log M| ≤ ∑ ρ ∈ R, Kf ρ := by
    rw [hTcard]; push_cast
    have e : κ * Real.log M = ∑ ρ ∈ R, (g ρ : ℝ) * (Real.log M / (P ρ * Real.log (eps D u v))) := by
      simp only [κ]; rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
      refine sum_congr rfl fun ρ hρ => ?_
      have : (0 : ℝ) < P ρ := by exact_mod_cast hP0 ρ
      field_simp
    rw [e, ← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ρ hρ =>
      hKf ρ (hfin.mem_toFinset.mp hρ) M L hM1 (hjL ρ (hroot ρ hρ)))
  -- (C) log M versus log N
  have hlog1 : Real.log N ≤ Real.log M := Real.log_le_log (by linarith) hMN
  have hlog2 : Real.log M ≤ Real.log (2 * A + |B|) + Real.log N := by
    rw [← Real.log_mul (by positivity) (by linarith)]
    exact Real.log_le_log (by linarith) hMup
  have hB : ((B.natAbs : ℕ) : ℝ) = |(B : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hAB1 : ((#hits : ℕ) : ℝ) ≤ (#T : ℕ) + (B.natAbs : ℕ) := by exact_mod_cast hA1
  have hAB2 : ((#T : ℕ) : ℝ) ≤ (#hits : ℕ) + (B.natAbs : ℕ) := by exact_mod_cast hA2
  rw [hB] at hAB1 hAB2
  have hcast : ((|B| : ℤ) : ℝ) = |(B : ℝ)| := Int.cast_abs
  rw [abs_le] at hB' ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlog1 hκ, mul_le_mul_of_nonneg_left hlog2 hκ]


lemma Kc_nonneg (hu1 : 1 < u) (hv : 0 ≤ v) {W : ℝ} (hW : 1 ≤ W) : 0 ≤ Kc D u v Δ W := by
  unfold Kc
  have hε := one_lt_eps (D := D) hu1 hv
  have := Real.log_nonneg (show (1 : ℝ) ≤ W + |(Δ : ℝ)| by linarith [abs_nonneg (Δ : ℝ)])
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Real.sqrt |(Δ : ℝ)| by
    linarith [Real.sqrt_nonneg |(Δ : ℝ)|])
  have := Real.log_pos hε
  have : 0 ≤ (2 * Real.log (W + |(Δ : ℝ)|) + Real.log (2 + Real.sqrt |(Δ : ℝ)|) +
    Real.log 2) / Real.log (eps D u v) := by positivity
  linarith

/-- **The explicit constant for one branch** `A n^2 + B n + C ∈ □`, `A > 0`, unit `(u, v)`. -/
noncomputable def Kpell (A B C u v : ℤ) : ℝ :=
  |(B : ℝ)| + 1 +
    (2 * (|((B ^ 2 - 4 * A * C : ℤ) : ℝ)| * (1 + (u : ℝ) ^ 2)) + 3) ^ 2 * (2 * (A : ℝ)) ^ 2 *
      Kc (4 * A) u v (B ^ 2 - 4 * A * C)
        ((2 * (|((B ^ 2 - 4 * A * C : ℤ) : ℝ)| * (1 + (u : ℝ) ^ 2)) + 2) *
          (1 + Real.sqrt ((4 * A : ℤ) : ℝ))) +
    (2 * (|((B ^ 2 - 4 * A * C : ℤ) : ℝ)| * (1 + (u : ℝ) ^ 2)) + 3) ^ 2 /
      Real.log (eps (4 * A) u v) * Real.log (2 * A + |(B : ℝ)|)

/-- **One Pell branch with an explicit error constant.**  For `A > 0` and any unit `(u, v)` of
`X^2 - 4A Y^2 = 1`: `|A(N) - κ log N| ≤ Kpell A B C u v` for every `N > |B|`. -/
theorem pell_branch_explicit {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ N : ℕ, B.natAbs + 1 ≤ N →
      |((#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℕ) : ℝ) -
        κ * Real.log N| ≤ Kpell A B C u v := by
  set Δ := B ^ 2 - 4 * A * C
  set Zi : ℤ := |Δ| * (1 + u ^ 2)
  set Z : ℝ := |(Δ : ℝ)| * (1 + (u : ℝ) ^ 2)
  have hZ : (Zi : ℝ) = Z := by simp only [Zi, Z]; push_cast; rfl
  set W : ℝ := (2 * Z + 2) * (1 + Real.sqrt ((4 * A : ℤ) : ℝ))
  have hZ0 : 0 ≤ Z := by positivity
  have hW1 : 1 ≤ W := by
    have := Real.sqrt_nonneg ((4 * A : ℤ) : ℝ)
    simp only [W]; nlinarith
  set M := (2 * A).toNat
  have hM : (M : ℤ) = 2 * A := Int.toNat_of_nonneg (by omega)
  haveI : NeZero M := ⟨by omega⟩
  have hper : ∀ ρ : ℤ × ℤ, ∃ P, 0 < P ∧ P ≤ M ^ 2 ∧ ∀ j, 2 * A ∣
      (unitOrbit (4 * A) u v ρ (j + P)).1 - (unitOrbit (4 * A) u v ρ j).1 := by
    intro ρ
    obtain ⟨P, hP, hPM, hPj⟩ := PerfectPower.RationalYun.short_period M hu ρ
    exact ⟨P, hP, hPM, fun j => by rw [← hM]; exact hPj j⟩
  choose P hP0 hPM hPper using hper
  set Kc0 := Kc (4 * A) u v Δ W
  have hKc0 : 0 ≤ Kc0 := Kc_nonneg hu1 hv.le hW1
  -- roots have `η ≤ W`
  have hetaW : ∀ ρ, IsRoot (4 * A) u v Δ ρ → eta (4 * A) ρ ≤ W := by
    intro ρ hρ
    have hsmall := PerfectPower.RationalYun.root_small (by omega) hu1 hv hu hρ
    have hsmallR : ((ρ.1 + ρ.2 : ℤ) : ℝ) ≤ ((2 * (|Δ| * (1 + u ^ 2)) + 2 : ℤ) : ℝ) := by
      exact_mod_cast hsmall
    push_cast at hsmallR
    have hX : (0 : ℝ) ≤ ρ.1 := by exact_mod_cast hρ.1.1.le
    have hY : (0 : ℝ) ≤ ρ.2 := by exact_mod_cast hρ.1.2.1
    have hs := Real.sqrt_nonneg ((4 * A : ℤ) : ℝ)
    simp only [eta, W, Z]
    push_cast at hs ⊢
    nlinarith [mul_le_mul_of_nonneg_right hsmallR (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt (4 * A))]
  have hcore := pell_count_core hA hu1 hv hu P hP0 (fun ρ => P ρ * Kc0) (fun ρ hρ =>
    orbit_count_explicit (by omega) hu hu1 hv.le hρ.1 (hetaW ρ hρ) (2 * A) B (hP0 ρ) (hPper ρ))
  simp only at hcore
  set R := (roots_finite (Δ := Δ) (by positivity : (0 : ℤ) < 4 * A) hu1 hv hu).toFinset
  set κ := (∑ ρ ∈ R, (((range (P ρ)).filter fun r => 2 * A ∣ (unitOrbit (4 * A) u v ρ r).1 - B).card
    : ℝ) / P ρ) / Real.log (eps (4 * A) u v)
  have hε := one_lt_eps (D := 4 * A) hu1 hv.le
  have hlogε : 0 < Real.log (eps (4 * A) u v) := Real.log_pos hε
  have hκ0 : 0 ≤ κ := div_nonneg (sum_nonneg fun ρ _ => by positivity) hlogε.le
  refine ⟨κ, hκ0, fun N hN => (hcore N hN).trans ?_⟩
  -- the roots lie in a box of at most `(2Z + 3)^2` points
  have hRcard : (#R : ℝ) ≤ (2 * Z + 3) ^ 2 := by
    have hsub : R ⊆ Icc (1 : ℤ) (2 * Zi + 2) ×ˢ Icc (0 : ℤ) (2 * Zi + 2) := by
      intro ρ hρ
      have hρ' := (Set.Finite.mem_toFinset _).mp hρ
      have hsmall := PerfectPower.RationalYun.root_small (by omega) hu1 hv hu hρ'
      have h1 := hρ'.1.1
      have h2 := hρ'.1.2.1
      simp only [mem_product, mem_Icc]
      constructor <;> constructor <;> omega
    have hc := card_le_card hsub
    rw [card_product, Int.card_Icc, Int.card_Icc] at hc
    have hZi0 : 0 ≤ Zi := by positivity
    have e1 : ((2 * Zi + 2 + 1 - 1).toNat : ℝ) = 2 * Z + 2 := by
      rw [show 2 * Zi + 2 + 1 - 1 = 2 * Zi + 2 by ring, ← hZ]
      have : ((2 * Zi + 2).toNat : ℤ) = 2 * Zi + 2 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have e2 : ((2 * Zi + 2 + 1 - 0).toNat : ℝ) = 2 * Z + 3 := by
      rw [show 2 * Zi + 2 + 1 - 0 = 2 * Zi + 3 by ring, ← hZ]
      have : ((2 * Zi + 3).toNat : ℤ) = 2 * Zi + 3 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have hc' : (#R : ℝ) ≤ ((2 * Zi + 2 + 1 - 1).toNat : ℝ) * ((2 * Zi + 2 + 1 - 0).toNat : ℝ) := by
      exact_mod_cast hc
    rw [e1, e2] at hc'
    nlinarith
  -- the per-root constants
  have hsumK : ∑ ρ ∈ R, (P ρ : ℝ) * Kc0 ≤ (2 * Z + 3) ^ 2 * (2 * (A : ℝ)) ^ 2 * Kc0 := by
    have hPle : ∀ ρ ∈ R, (P ρ : ℝ) * Kc0 ≤ (2 * (A : ℝ)) ^ 2 * Kc0 := by
      intro ρ _
      apply mul_le_mul_of_nonneg_right _ hKc0
      have : (P ρ : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hPM ρ
      have hMR : (M : ℝ) = 2 * A := by exact_mod_cast hM
      rwa [hMR] at this
    calc ∑ ρ ∈ R, (P ρ : ℝ) * Kc0 ≤ ∑ ρ ∈ R, (2 * (A : ℝ)) ^ 2 * Kc0 := sum_le_sum hPle
      _ = #R * ((2 * (A : ℝ)) ^ 2 * Kc0) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * Z + 3) ^ 2 * ((2 * (A : ℝ)) ^ 2 * Kc0) :=
          mul_le_mul_of_nonneg_right hRcard (by positivity)
      _ = _ := by ring
  -- `κ ≤ #R / log ε`
  have hκle : κ ≤ (2 * Z + 3) ^ 2 / Real.log (eps (4 * A) u v) := by
    apply div_le_div_of_nonneg_right _ hlogε.le
    calc ∑ ρ ∈ R, ((((range (P ρ)).filter fun r => 2 * A ∣
            (unitOrbit (4 * A) u v ρ r).1 - B).card : ℝ) / P ρ)
        ≤ ∑ ρ ∈ R, (1 : ℝ) := by
          apply sum_le_sum
          intro ρ _
          have hP : (0 : ℝ) < P ρ := by exact_mod_cast hP0 ρ
          rw [div_le_one hP]
          have : ((range (P ρ)).filter fun r => 2 * A ∣
              (unitOrbit (4 * A) u v ρ r).1 - B).card ≤ P ρ := by
            have := card_filter_le (range (P ρ)) (fun r => 2 * A ∣
              (unitOrbit (4 * A) u v ρ r).1 - B)
            rwa [card_range] at this
          exact_mod_cast this
      _ = #R := by simp
      _ ≤ _ := hRcard
  have hlogAB : 0 ≤ Real.log (2 * A + |(B : ℝ)|) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA
    linarith [abs_nonneg (B : ℝ)]
  have hκlog : κ * Real.log (2 * A + |(B : ℝ)|) ≤
      (2 * Z + 3) ^ 2 / Real.log (eps (4 * A) u v) * Real.log (2 * A + |(B : ℝ)|) :=
    mul_le_mul_of_nonneg_right hκle hlogAB
  have hK : Kpell A B C u v = |(B : ℝ)| + 1 + (2 * Z + 3) ^ 2 * (2 * (A : ℝ)) ^ 2 * Kc0 +
      (2 * Z + 3) ^ 2 / Real.log (eps (4 * A) u v) * Real.log (2 * A + |(B : ℝ)|) := rfl
  rw [hK]
  have hcB : ((|B| : ℤ) : ℝ) = |(B : ℝ)| := Int.cast_abs
  rw [hcB]
  linarith

end PerfectPower.PellExact

namespace PerfectPower.RationalYun

open PerfectPower PellExact Polynomial

/-- A positive Pell unit of `X^2 - 4A Y^2 = 1` when `A > 0` is not a square (Mathlib's
`Pell.exists_of_not_isSquare`). -/
lemma exists_pellUnit {A : ℤ} (hA : 0 < A) (hsq : ¬ IsSquare A) :
    ∃ p : ℤ × ℤ, 1 < p.1 ∧ 0 < p.2 ∧ p.1 ^ 2 - 4 * A * p.2 ^ 2 = 1 := by
  have h4 : ¬ IsSquare (4 * A) := fun h => hsq (isSquare_of_isSquare_four_mul h)
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (by omega : 0 < 4 * A) h4
  have hv : 0 < |y| := abs_pos.mpr hy
  have hu : |x| ^ 2 - 4 * A * |y| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hxy
  have hu1 : 1 < |x| := by
    have hy2 : 1 ≤ |y| ^ 2 := by nlinarith
    nlinarith [abs_nonneg x]
  exact ⟨(|x|, |y|), hu1, hv, hu⟩

/-- A fixed Pell unit for `A > 0` not a square (and `(1, 0)` otherwise). -/
noncomputable def pellUnit (A : ℤ) : ℤ × ℤ :=
  if h : 0 < A ∧ ¬ IsSquare A then Classical.choose (exists_pellUnit h.1 h.2) else (1, 0)

lemma pellUnit_spec {A : ℤ} (hA : 0 < A) (hsq : ¬ IsSquare A) :
    1 < (pellUnit A).1 ∧ 0 < (pellUnit A).2 ∧
      (pellUnit A).1 ^ 2 - 4 * A * (pellUnit A).2 ^ 2 = 1 := by
  unfold pellUnit
  rw [dif_pos ⟨hA, hsq⟩]
  exact Classical.choose_spec (exists_pellUnit hA hsq)

/-- **The explicit constant of one branch** `A n^2 + B n + C ∈ □`: `|B| + |C|` for `A < 0`,
`|Δ| + |B|` for `A` a square, and `Kpell` at the unit `pellUnit A` otherwise. -/
noncomputable def Kbranch (A B C : ℤ) : ℝ :=
  if A < 0 then ((B.natAbs + C.natAbs : ℕ) : ℝ)
  else if IsSquare A then (((B ^ 2 - 4 * A * C).natAbs + B.natAbs : ℕ) : ℝ)
  else Kpell A B C (pellUnit A).1 (pellUnit A).2

/-- **One branch with an explicit constant.**  For `A ≠ 0` and `B^2 - 4AC ≠ 0`,
`|A(N) - κ log N| ≤ Kbranch A B C` for every `N > |B|`. -/
theorem branch_count_explicit (A B C : ℤ) (hA : A ≠ 0) (hdisc : B ^ 2 - 4 * A * C ≠ 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ N : ℕ, B.natAbs + 1 ≤ N →
      |(#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℝ) -
        κ * Real.log N| ≤ Kbranch A B C := by
  have bounded : ∀ M : ℕ, (∀ n : ℕ, 1 ≤ n → IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) → n ≤ M) →
      ∀ N : ℕ, |(#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℝ) -
        0 * Real.log N| ≤ M := by
    intro M hM N
    have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) ⊆
        Icc 1 M := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      exact ⟨hn.1.1, hM n hn.1.1 hn.2⟩
    have hcard := card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
    simp only [zero_mul, sub_zero, Nat.abs_cast]
    exact_mod_cast hcard
  unfold Kbranch
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · rw [if_pos hneg]
    exact ⟨0, le_refl _, fun N _ => bounded _ (hit_le_of_neg hneg) N⟩
  · rw [if_neg (by omega)]
    by_cases hsqA : IsSquare A
    · rw [if_pos hsqA]
      exact ⟨0, le_refl _, fun N _ => bounded _ (hit_le_of_square hpos hsqA hdisc) N⟩
    · rw [if_neg hsqA]
      obtain ⟨hu1, hv, hu⟩ := pellUnit_spec hpos hsqA
      exact pell_branch_explicit hpos hu1 hv hu

/-- **Theorem C with an explicit constant.**  For `F ∈ ℤ[X]` of Pell type with half-exponent
`e`, there are at most two integer branch quadratics `(A, B, C)` (one for each root `γ` of
`γ^e = lc(F)`, with `A = γ s^2`, `B = γ s^2 b` for the pell part `X^2 + bX + c`), and
`|A(N) - κ log N| ≤ Σ Kbranch(A, B, C) + deg F + 2` as soon as `N > |B|` for each branch. -/
theorem Decomposition.pell_count_explicit {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {e : ℕ} (he : e ≠ 0)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % (2 * e) = 0 ∨ (j + 1) % (2 * e) = e ∨ Y.part (j + 1) = 1)
    (hdegree : (∑ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e),
      (Y.part (j + 1)).natDegree) = 2) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∃ L : List (ℤ × ℤ × ℤ), L.length ≤ 2 ∧
      (∀ t ∈ L, ∃ γ s : ℚ, γ ^ e = F.leadingCoeff ∧ s ≠ 0 ∧ (t.1 : ℚ) = γ * s ^ 2 ∧
        (t.2.1 : ℚ) = γ * s ^ 2 * (Y.pellPart e).coeff 1) ∧
      ∀ N : ℕ, (∀ t ∈ L, t.2.1.natAbs + 1 ≤ N) →
        |(#((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) : ℝ) -
          κ * Real.log N| ≤ (L.map fun t => Kbranch t.1 t.2.1 t.2.2).sum + F.natDegree + 2 := by
  obtain ⟨hmon, hdeg, hiff⟩ := Y.integer_pell_reduction he hres hdegree
  have hFq : F.map (Int.castRingHom ℚ) ≠ 0 := Y.ne_zero
  have hF : F ≠ 0 := by rintro rfl; exact hFq (Polynomial.map_zero _)
  set Q := Y.pellPart e
  have hdisc := disc_ne_zero (pellPart_squarefree Y e) hmon hdeg
  have hlc : (F.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hF
  set P : ℚ → ℕ → Prop := fun γ n => RatPower (γ * Q.eval (n : ℚ)) 2 with hPdef
  -- each nonzero `γ` gives a branch with an explicit constant
  have hbranch : ∀ γ : ℚ, γ ≠ 0 → ∃ A B C : ℤ, ∃ κ : ℝ, 0 ≤ κ ∧
      (∃ s : ℚ, s ≠ 0 ∧ (A : ℚ) = γ * s ^ 2 ∧ (B : ℚ) = γ * s ^ 2 * Q.coeff 1) ∧
      ∀ N : ℕ, B.natAbs + 1 ≤ N →
        |(#((Icc 1 N).filter (P γ)) : ℝ) - κ * Real.log N| ≤ Kbranch A B C := by
    intro γ hγ
    obtain ⟨A, B, C, hA, hD, hs, hPA⟩ := clear_denoms γ (Q.coeff 1) (Q.coeff 0) hγ hdisc
    obtain ⟨κ, hκ, hK⟩ := branch_count_explicit A B C hA hD
    refine ⟨A, B, C, κ, hκ, hs, fun N hN => ?_⟩
    have e1 : (Icc 1 N).filter (P γ) =
        (Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) := by
      apply filter_congr
      intro n _
      simp only [hPdef]
      rw [monic_quadratic_eval hmon hdeg, ← hPA n]
      push_cast
      rfl
    rw [e1]; exact hK N hN
  have hzeros := card_zeros_le F hF
  by_cases hγ : ∃ γ : ℚ, γ ^ e = F.leadingCoeff
  swap
  · refine ⟨0, le_refl _, [], by simp, by simp, fun N _ => ?_⟩
    have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) ⊆
        (Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 := by
      intro n hn
      simp only [mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      rcases (hiff n).mp hn.2 with h | ⟨γ, hγ', -⟩
      · exact h
      · exact absurd ⟨γ, hγ'⟩ hγ
    have := (card_le_card hsub).trans (hzeros N)
    have : ((#((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) : ℕ) : ℝ) ≤
        F.natDegree := by exact_mod_cast this
    simp only [zero_mul, sub_zero, Nat.abs_cast, List.map_nil, List.sum_nil, zero_add]
    linarith
  obtain ⟨γ₀, hγ₀⟩ := hγ
  have hγ₀ne : γ₀ ≠ 0 := by
    rintro rfl; rw [zero_pow he] at hγ₀; exact hlc hγ₀.symm
  have hroots : ∀ γ : ℚ, γ ^ e = F.leadingCoeff → γ = γ₀ ∨ γ = -γ₀ := by
    intro γ hγ
    rw [← hγ₀] at hγ
    rcases (pow_eq_pow_iff_of_ne_zero he).mp hγ with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨A1, B1, C1, κ1, hκ1, hs1, hK1⟩ := hbranch γ₀ hγ₀ne
  by_cases h2 : (-γ₀) ^ e = F.leadingCoeff
  · -- two branches, overlapping only at roots of `Q`
    obtain ⟨A2, B2, C2, κ2, hκ2, hs2, hK2⟩ := hbranch (-γ₀) (neg_ne_zero.mpr hγ₀ne)
    refine ⟨κ1 + κ2, by linarith, [(A1, B1, C1), (A2, B2, C2)], by simp, ?_, fun N hN => ?_⟩
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨γ₀, hs1.choose, hγ₀, hs1.choose_spec⟩
      · exact ⟨-γ₀, hs2.choose, h2, hs2.choose_spec⟩
    have hN1 := hN (A1, B1, C1) (by simp)
    have hN2 := hN (A2, B2, C2) (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have e1 : ((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) =
        (Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ (P γ₀ n ∨ P (-γ₀) n) := by
      apply filter_congr
      intro n _
      rw [hiff n]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨γ, hγ, hP⟩
        rcases hroots γ hγ with rfl | rfl
        · exact Or.inl hP
        · exact Or.inr hP
      · rintro (hP | hP)
        · exact ⟨γ₀, hγ₀, hP⟩
        · exact ⟨-γ₀, h2, hP⟩
    rw [e1]
    obtain ⟨c1, c2⟩ := count_or (fun n : ℕ => F.eval (n : ℤ) = 0) (fun n => P γ₀ n ∨ P (-γ₀) n)
      N F.natDegree (hzeros N)
    have hunion : #((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) +
        #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) =
        #((Icc 1 N).filter (P γ₀)) + #((Icc 1 N).filter (P (-γ₀))) := by
      rw [filter_or, filter_and]
      exact card_union_add_card_inter _ _
    have hover : #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) ≤ 2 := by
      calc #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n)
          ≤ #((Icc 1 N).filter fun n : ℕ => Q.eval (n : ℚ) = 0) := by
            apply card_le_card
            intro n hn
            simp only [mem_filter] at hn ⊢
            refine ⟨hn.1, ?_⟩
            have h0 := (opposite_squares_iff_zero (γ₀ * Q.eval (n : ℚ))).mp
              ⟨hn.2.1, by simpa [hPdef, neg_mul] using hn.2.2⟩
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h hγ₀ne
            · exact h
        _ ≤ Q.natDegree := card_zeros_le_rat Q hmon.ne_zero N
        _ = 2 := hdeg
    have b1 := hK1 N hN1
    have b2 := hK2 N hN2
    have c1' : ((#((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) : ℕ) : ℝ) ≤
        #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ (P γ₀ n ∨ P (-γ₀) n)) := by
      exact_mod_cast c1
    have c2' : ((#((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ (P γ₀ n ∨ P (-γ₀) n)) :
        ℕ) : ℝ) ≤ #((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) + F.natDegree := by
      exact_mod_cast c2
    have hunion' : ((#((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) : ℕ) : ℝ) +
        #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) =
        #((Icc 1 N).filter (P γ₀)) + #((Icc 1 N).filter (P (-γ₀))) := by exact_mod_cast hunion
    have hover' : ((#((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast hover
    rw [abs_le] at b1 b2 ⊢
    constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
  · -- one branch
    refine ⟨κ1, hκ1, [(A1, B1, C1)], by simp, ?_, fun N hN => ?_⟩
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht
      exact ⟨γ₀, hs1.choose, hγ₀, hs1.choose_spec⟩
    have hN1 := hN (A1, B1, C1) (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have e1 : ((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) =
        (Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ P γ₀ n := by
      apply filter_congr
      intro n _
      rw [hiff n]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨γ, hγ, hP⟩
        rcases hroots γ hγ with rfl | rfl
        · exact hP
        · exact absurd hγ h2
      · intro hP; exact ⟨γ₀, hγ₀, hP⟩
    rw [e1]
    obtain ⟨c1, c2⟩ := count_or (fun n : ℕ => F.eval (n : ℤ) = 0) (P γ₀) N F.natDegree (hzeros N)
    have b1 := hK1 N hN1
    have c1' : ((#((Icc 1 N).filter (P γ₀)) : ℕ) : ℝ) ≤
        #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ P γ₀ n) := by exact_mod_cast c1
    have c2' : ((#((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ P γ₀ n) : ℕ) : ℝ) ≤
        #((Icc 1 N).filter (P γ₀)) + F.natDegree := by exact_mod_cast c2
    rw [abs_le] at b1 ⊢
    constructor <;> linarith [b1.1, b1.2]

end PerfectPower.RationalYun
