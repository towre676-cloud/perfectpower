import PerfectPower.RatInterval
import PerfectPower.DirectReduction

/-!
# From a logarithmic lower bound to the analytic premise

`UnitPremises.Analytic` bundled the whole Baker-type argument.  This file proves it from one
precisely stated lower bound (`MatveevLB`, an instance of Matveev's theorem), with every other
step elementary and in Lean.

The real-number lemmas (this section) are generic:

* `siegel`: with `γₗ = b (t − φₗ)` and `t` closest to `φᵢ`, `|γⱼ| ≥ |b| dⱼ/2`, and
  `Λ = (φᵢ − φⱼ)γₖ / ((φᵢ − φₖ)γⱼ) − 1 = −(φⱼ − φₖ)γᵢ / ((φᵢ − φₖ)γⱼ)` satisfies
  `|Λ| |b|³ ≤ 8|N| dⱼₖ / (dⱼ² dₖ²)` and `Λ ≠ 0` (`N = γᵢγⱼγₖ ≠ 0`, distinct conjugates).
* `log_one_add_le`: `|Λ| ≤ 1/2 ⇒ 0 < 1 + Λ ∧ |log(1 + Λ)| ≤ 2|Λ|`.
* `exps_le`: the exponents solve a `2 × 2` system in `log|b|`, so `H ≤ a log|b| + n R`.
* `matveev_cutoff`: the lower bound `log|Λ| > −C(1 + log H)` and the upper bound
  `|Λ| ≤ K₁ e^{−3 log|b|}` force `H < M₀` once `(3/a)M₀ − log K₁ − 3b'/a − C(1 + log M₀) > 0`
  and `M₀ ≥ aC/3`.
-/

namespace PerfectPower.AnalyticBridge

open Real

/-! ### Real-number lemmas -/

lemma siegel_aux {A B C D E : ℝ} (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    A / D * (4 * E / (B ^ 2 * (C * D))) * (2 / (B * C)) * B ^ 3 = 8 * E * A / (C ^ 2 * D ^ 2) := by
  field_simp
  ring

/-- **Siegel's identity and the closest-conjugate geometry.** -/
lemma siegel {b t pi pj pk gi gj gk N : ℝ} (hb : b ≠ 0) (hgi : gi = b * (t - pi))
    (hgj : gj = b * (t - pj)) (hgk : gk = b * (t - pk)) (hij : |t - pi| ≤ |t - pj|)
    (hik : |t - pi| ≤ |t - pk|) (hN : gi * gj * gk = N) (hN0 : N ≠ 0) (dij : pi ≠ pj)
    (dik : pi ≠ pk) (djk : pj ≠ pk) :
    |b| * |pj - pi| / 2 ≤ |gj| ∧ |b| * |pk - pi| / 2 ≤ |gk| ∧
    |t - pi| * (|b| ^ 3 * (|pj - pi| * |pk - pi|)) ≤ 4 * |N| ∧
    (pi - pj) * gk / ((pi - pk) * gj) - 1 = -((pj - pk) * gi / ((pi - pk) * gj)) ∧
    (pi - pj) * gk / ((pi - pk) * gj) - 1 ≠ 0 ∧
    |(pi - pj) * gk / ((pi - pk) * gj) - 1| * |b| ^ 3 ≤
      8 * |N| * |pj - pk| / (|pj - pi| ^ 2 * |pk - pi| ^ 2) := by
  have hb0 : 0 < |b| := abs_pos.mpr hb
  have dj0 : 0 < |pj - pi| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm dij))
  have dk0 : 0 < |pk - pi| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm dik))
  have djk0 : 0 < |pj - pk| := abs_pos.mpr (sub_ne_zero.mpr djk)
  have hN' : 0 < |N| := abs_pos.mpr hN0
  -- |pj − pi| ≤ |pj − t| + |t − pi| ≤ 2 |t − pj|
  have ej : |pj - pi| ≤ 2 * |t - pj| := by
    have := abs_sub_le pj t pi
    rw [abs_sub_comm pj t] at this; linarith
  have ek : |pk - pi| ≤ 2 * |t - pk| := by
    have := abs_sub_le pk t pi
    rw [abs_sub_comm pk t] at this; linarith
  have aj : |gj| = |b| * |t - pj| := by rw [hgj, abs_mul]
  have ak : |gk| = |b| * |t - pk| := by rw [hgk, abs_mul]
  have ai : |gi| = |b| * |t - pi| := by rw [hgi, abs_mul]
  have b1 : |b| * |pj - pi| / 2 ≤ |gj| := by rw [aj]; nlinarith
  have b2 : |b| * |pk - pi| / 2 ≤ |gk| := by rw [ak]; nlinarith
  have hprod : |gi| * |gj| * |gk| = |N| := by rw [← abs_mul, ← abs_mul, hN]
  have gj0 : gj ≠ 0 := by
    intro h; rw [h] at hN; simp at hN; exact hN0 hN.symm
  have gi0 : gi ≠ 0 := by
    intro h; rw [h] at hN; simp at hN; exact hN0 hN.symm
  -- |γᵢ| (|b| dⱼ/2)(|b| dₖ/2) ≤ |N|
  have b3 : |gi| * ((|b| * |pj - pi| / 2) * (|b| * |pk - pi| / 2)) ≤ |N| := by
    rw [← hprod, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact mul_le_mul b1 b2 (by positivity) (abs_nonneg _)
  have b3' : |t - pi| * (|b| ^ 3 * (|pj - pi| * |pk - pi|)) ≤ 4 * |N| := by
    rw [ai] at b3; nlinarith
  have hid : (pi - pj) * gk / ((pi - pk) * gj) - 1 = -((pj - pk) * gi / ((pi - pk) * gj)) := by
    have hd : (pi - pk) * gj ≠ 0 := mul_ne_zero (sub_ne_zero.mpr dik) gj0
    field_simp
    rw [hgi, hgj, hgk]; ring
  refine ⟨b1, b2, b3', hid, ?_, ?_⟩
  · rw [hid, neg_ne_zero]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr djk) gi0)
      (mul_ne_zero (sub_ne_zero.mpr dik) gj0)
  · rw [hid, abs_neg, abs_div, abs_mul, abs_mul]
    have hpk : |pi - pk| = |pk - pi| := abs_sub_comm _ _
    rw [hpk]
    have hgj0 : 0 < |gj| := abs_pos.mpr gj0
    have e1 : |gi| ≤ 4 * |N| / (|b| ^ 2 * (|pj - pi| * |pk - pi|)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [b3]
    have e2 : 1 / |gj| ≤ 2 / (|b| * |pj - pi|) := by
      rw [div_le_div_iff₀ hgj0 (by positivity)]
      linarith
    calc |pj - pk| * |gi| / (|pk - pi| * |gj|) * |b| ^ 3
        = |pj - pk| / |pk - pi| * |gi| * (1 / |gj|) * |b| ^ 3 := by field_simp
      _ ≤ |pj - pk| / |pk - pi| * (4 * |N| / (|b| ^ 2 * (|pj - pi| * |pk - pi|))) *
            (2 / (|b| * |pj - pi|)) * |b| ^ 3 := by gcongr
      _ = 8 * |N| * |pj - pk| / (|pj - pi| ^ 2 * |pk - pi| ^ 2) := siegel_aux hb0 dj0 dk0

/-- **`|log(1 + Λ)| ≤ 2|Λ|`** for `|Λ| ≤ 1/2`. -/
lemma log_one_add_le {L : ℝ} (h : |L| ≤ 1 / 2) : 0 < 1 + L ∧ |Real.log (1 + L)| ≤ 2 * |L| := by
  have h1 := abs_le.mp h
  have hp : 0 < 1 + L := by linarith
  refine ⟨hp, abs_le.mpr ⟨?_, ?_⟩⟩
  · -- log(1 + L) ≥ 1 − 1/(1 + L) = L/(1 + L) ≥ −2|L|
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at this
    have hinv : (1 + L)⁻¹ - 1 = -L / (1 + L) := by field_simp
    rw [hinv] at this
    have : -L / (1 + L) ≤ 2 * |L| := by
      rw [div_le_iff₀ hp]
      rcases le_total 0 L with hl | hl
      · rw [abs_of_nonneg hl]; nlinarith
      · rw [abs_of_nonpos hl]; nlinarith
    linarith
  · have := Real.log_le_sub_one_of_pos hp
    have : L ≤ 2 * |L| := by
      rcases le_total 0 L with hl | hl
      · rw [abs_of_nonneg hl]; linarith
      · rw [abs_of_nonpos hl]; linarith
    linarith

/-- **The exponents are bounded by `log|b|`.** -/
lemma exps_le {x y u1j u2j u1k u2k L wj wk R a n : ℝ}
    (hj : x * u1j + y * u2j = L + wj) (hk : x * u1k + y * u2k = L + wk)
    (hdet : u1j * u2k - u2j * u1k ≠ 0) (hL : 0 ≤ L) (hwj : |wj| ≤ R) (hwk : |wk| ≤ R)
    (ha1 : |u2k - u2j| / |u1j * u2k - u2j * u1k| ≤ a) (ha2 : |u1j - u1k| / |u1j * u2k - u2j * u1k| ≤ a)
    (hn1 : (|u2k| + |u2j|) / |u1j * u2k - u2j * u1k| ≤ n)
    (hn2 : (|u1j| + |u1k|) / |u1j * u2k - u2j * u1k| ≤ n) :
    |x| ≤ a * L + n * R ∧ |y| ≤ a * L + n * R := by
  set d := u1j * u2k - u2j * u1k
  have hd0 : 0 < |d| := abs_pos.mpr hdet
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hwj
  have ex : x = (L * (u2k - u2j) + (wj * u2k - wk * u2j)) / d := by
    field_simp; linear_combination u2k * hj - u2j * hk
  have ey : y = (L * (u1j - u1k) + (u1j * wk - u1k * wj)) / d := by
    field_simp; linear_combination u1j * hk - u1k * hj
  constructor
  · rw [ex, abs_div]
    rw [div_le_iff₀ hd0]
    have e1 : |L * (u2k - u2j) + (wj * u2k - wk * u2j)| ≤ L * |u2k - u2j| + R * (|u2k| + |u2j|) := by
      calc _ ≤ |L * (u2k - u2j)| + |wj * u2k - wk * u2j| := abs_add_le _ _
        _ ≤ |L * (u2k - u2j)| + (|wj * u2k| + |wk * u2j|) := by gcongr; exact abs_sub _ _
        _ = L * |u2k - u2j| + (|wj| * |u2k| + |wk| * |u2j|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hL]
        _ ≤ _ := by nlinarith [abs_nonneg u2k, abs_nonneg u2j]
    have f1 : |u2k - u2j| ≤ a * |d| := by rwa [div_le_iff₀ hd0] at ha1
    have f2 : |u2k| + |u2j| ≤ n * |d| := by rwa [div_le_iff₀ hd0] at hn1
    nlinarith
  · rw [ey, abs_div]
    rw [div_le_iff₀ hd0]
    have e1 : |L * (u1j - u1k) + (u1j * wk - u1k * wj)| ≤ L * |u1j - u1k| + R * (|u1j| + |u1k|) := by
      calc _ ≤ |L * (u1j - u1k)| + |u1j * wk - u1k * wj| := abs_add_le _ _
        _ ≤ |L * (u1j - u1k)| + (|u1j * wk| + |u1k * wj|) := by gcongr; exact abs_sub _ _
        _ = L * |u1j - u1k| + (|u1j| * |wk| + |u1k| * |wj|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hL]
        _ ≤ _ := by nlinarith [abs_nonneg u1j, abs_nonneg u1k]
    have f1 : |u1j - u1k| ≤ a * |d| := by rwa [div_le_iff₀ hd0] at ha2
    have f2 : |u1j| + |u1k| ≤ n * |d| := by rwa [div_le_iff₀ hd0] at hn2
    nlinarith

/-- **The Matveev cutoff.** -/
lemma matveev_cutoff {H L K1 a bb C M0 Λ : ℝ} (ha : 0 < a) (hK : 0 < K1) (hC : 0 ≤ C) (hM1 : 1 ≤ M0)
    (hMa : a * C / 3 ≤ M0) (hlin : H ≤ a * L + bb) (hΛ0 : Λ ≠ 0)
    (hΛ : |Λ| ≤ K1 * Real.exp (-(3 * L)))
    (hMat : 1 ≤ H → -(C * (1 + Real.log H)) < Real.log |Λ|)
    (hchk : 0 < 3 / a * M0 - Real.log K1 - 3 * bb / a - C * (1 + Real.log M0)) : H < M0 := by
  by_contra hcon
  push_neg at hcon
  have hH1 : 1 ≤ H := le_trans hM1 hcon
  have hHpos : 0 < H := by linarith
  have hM0pos : 0 < M0 := by linarith
  have hm := hMat hH1
  -- log|Λ| ≤ log K₁ − 3L
  have hl : Real.log |Λ| ≤ Real.log K1 - 3 * L := by
    have := Real.log_le_log (abs_pos.mpr hΛ0) hΛ
    rwa [Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  -- L ≥ (H − bb)/a
  have hL : (H - bb) / a ≤ L := by rw [div_le_iff₀ ha]; linarith
  have h3 : 3 * ((H - bb) / a) = 3 / a * H - 3 * bb / a := by field_simp; ring
  -- log H − log M₀ ≤ (H − M₀)/M₀
  have hlog : Real.log H - Real.log M0 ≤ (H - M0) / M0 := by
    rw [← Real.log_div hHpos.ne' hM0pos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hHpos hM0pos)
    have e : H / M0 - 1 = (H - M0) / M0 := by field_simp
    linarith
  have hCM : C / M0 ≤ 3 / a := by
    rw [div_le_div_iff₀ hM0pos ha]; linarith
  have hmono : C * (Real.log H - Real.log M0) ≤ 3 / a * (H - M0) := by
    have h1 : C * (Real.log H - Real.log M0) ≤ C * ((H - M0) / M0) :=
      mul_le_mul_of_nonneg_left hlog hC
    have h2 : C * ((H - M0) / M0) = C / M0 * (H - M0) := by ring
    have h4 : C / M0 * (H - M0) ≤ 3 / a * (H - M0) := mul_le_mul_of_nonneg_right hCM (by linarith)
    linarith
  nlinarith

/-! ### One case, in interval arithmetic -/

open RatInterval

/-- The embedding enclosures one case uses: `φᵢ, φⱼ, φₖ`, `γ₀` at `j, k`, `ε₁, ε₂` at `j, k`. -/
structure Base where
  /-- `φ` at the closest embedding `i`. -/
  phi : I
  /-- `φ` at `j`. -/
  phj : I
  /-- `φ` at `k`. -/
  phk : I
  /-- `γ₀` at `j`. -/
  gj : I
  /-- `γ₀` at `k`. -/
  gk : I
  /-- `ε₁` at `j`. -/
  e1j : I
  /-- `ε₁` at `k`. -/
  e1k : I
  /-- `ε₂` at `j`. -/
  e2j : I
  /-- `ε₂` at `k`. -/
  e2k : I

/-- Everything the case computes. -/
structure Out where
  /-- `dⱼ = |φⱼ − φᵢ|`. -/
  dj : I
  /-- `dₖ = |φₖ − φᵢ|`. -/
  dk : I
  /-- `K₁ = 8|N| dⱼₖ/(dⱼ² dₖ²)`. -/
  K1 : I
  /-- `α₁ = |ε₁ₖ/ε₁ⱼ|`. -/
  a1 : I
  /-- `α₂`. -/
  a2 : I
  /-- `α₃`. -/
  a3 : I
  /-- `ℓ₁ = log α₁`. -/
  l1 : I
  /-- `ℓ₂`. -/
  l2 : I
  /-- `ℓ₃`. -/
  l3 : I
  /-- `log|ε₁ⱼ|`. -/
  u1j : I
  /-- `log|ε₂ⱼ|`. -/
  u2j : I
  /-- `log|ε₁ₖ|`. -/
  u1k : I
  /-- `log|ε₂ₖ|`. -/
  u2k : I
  /-- The determinant. -/
  det : I
  /-- The slope bound `a`. -/
  aQ : ℚ
  /-- The norm bound `n`. -/
  nQ : ℚ
  /-- `τ ≥ |t − φᵢ|`. -/
  tau : ℚ
  /-- Enclosure of `log|t − φⱼ| − log|γ₀ⱼ|`. -/
  wj : I
  /-- Enclosure of `log|t − φₖ| − log|γ₀ₖ|`. -/
  wk : I
  /-- `R ≥ |wⱼ|, |wₖ|`. -/
  R : ℚ
  /-- `b' = n R`. -/
  bb : ℚ
  /-- `κ = ℓ₁/ℓ₂`. -/
  kap : I
  /-- `μ = ℓ₃/ℓ₂`. -/
  mu : I
  /-- `A ≤ Au`. -/
  Au : ℚ

/-- **The interval computation of one case.** -/
def caseCompute (p J em : ℕ) (Nq : ℚ) (V : ℕ) (B : Base) : Out :=
  let lg := logI p J
  let dj := absI (sub B.phj B.phi)
  let dk := absI (sub B.phk B.phi)
  let djk := absI (sub B.phj B.phk)
  let K1 := rnd p (div (mul (ofQ (8 * Nq)) djk) (mul (mul dj dj) (mul dk dk)))
  let a1 := absI (div B.e1k B.e1j)
  let a2 := absI (div B.e2k B.e2j)
  let a3 := absI (div (mul (sub B.phi B.phj) B.gk) (mul (sub B.phi B.phk) B.gj))
  let l1 := rnd p (lg a1)
  let l2 := rnd p (lg a2)
  let l3 := rnd p (lg a3)
  let u1j := rnd p (lg (absI B.e1j))
  let u2j := rnd p (lg (absI B.e2j))
  let u1k := rnd p (lg (absI B.e1k))
  let u2k := rnd p (lg (absI B.e2k))
  let det := rnd p (sub (mul u1j u2k) (mul u2j u1k))
  let ad := absI det
  let aQ := rup p (max (div (absI (sub u2k u2j)) ad).2 (div (absI (sub u1j u1k)) ad).2)
  let nQ := rup p (max (div (add (absI u2k) (absI u2j)) ad).2 (div (add (absI u1j) (absI u1k)) ad).2)
  let tau := rup p (div (ofQ (4 * Nq / ((V : ℚ) + 1) ^ 3)) (mul dj dk)).2
  let wj : I := ((sub (lg (div dj (ofQ 2))) (lg (absI B.gj))).1,
    (sub (lg (add dj (ofQ tau))) (lg (absI B.gj))).2)
  let wk : I := ((sub (lg (div dk (ofQ 2))) (lg (absI B.gk))).1,
    (sub (lg (add dk (ofQ tau))) (lg (absI B.gk))).2)
  let R := max (max |wj.1| |wj.2|) (max |wk.1| |wk.2|)
  let bb := rup p (nQ * R)
  { dj := dj, dk := dk, K1 := K1, a1 := a1, a2 := a2, a3 := a3, l1 := l1, l2 := l2, l3 := l3,
    u1j := u1j, u2j := u2j, u1k := u1k, u2k := u2k, det := det, aQ := aQ, nQ := nQ, tau := tau,
    wj := wj, wk := wk, R := R, bb := bb, kap := div l1 l2, mu := div l3 l2,
    Au := rup p (div (mul (ofQ 2) (mul K1 (ofQ (expHi p em (3 * bb / aQ))))) (absI l2)).2 }

/-- **The side conditions of one case**, all decidable. -/
def caseOK (p J em : ℕ) (Nq : ℚ) (V : ℕ) (Cm : ℚ) (B : Base) (C : UnitPremises.Case) : Bool :=
  let O := caseCompute p J em Nq V B
  let lg := logI p J
  [nz (sub B.phi B.phj),
   nz (sub B.phi B.phk),
   nz (sub B.phj B.phk),
   nz B.e1j,
   nz B.e1k,
   nz B.e2j,
   nz B.e2k,
   nz B.gj,
   nz B.gk,
   logOK p O.a1,
   logOK p O.a2,
   logOK p O.a3,
   logOK p (absI B.e1j),
   logOK p (absI B.e2j),
   logOK p (absI B.e1k),
   logOK p (absI B.e2k),
   logOK p (div O.dj (ofQ 2)),
   logOK p (absI B.gj),
   logOK p (add O.dj (ofQ O.tau)),
   logOK p (div O.dk (ofQ 2)),
   logOK p (absI B.gk),
   logOK p (add O.dk (ofQ O.tau)),
   logOK p O.K1,
   logOK p (ofQ C.M0),
   nz O.det,
   nz O.l2,
   nz (mul O.dj O.dk),
   nz (mul (mul O.dj O.dj) (mul O.dk O.dk)),
   nz (absI O.det),
   nz (absI O.l2),
   nz (mul (sub B.phi B.phk) B.gj),
   nz B.e1j,
   nz B.e2j,
   decide (0 < O.aQ),
   decide (0 < Nq),
   decide (2 * O.K1.2 ≤ ((V : ℚ) + 1) ^ 3),
   decide (0 ≤ O.bb),
   decide (3 * O.bb / O.aQ / 2 ^ em < 1),
   decide (0 ≤ Cm),
   decide (1 ≤ (C.M0 : ℚ)),
   decide (O.aQ * Cm / 3 ≤ C.M0),
   decide (0 < 3 / O.aQ * C.M0 - (lg O.K1).2 - 3 * O.bb / O.aQ - Cm * (1 + (lg (ofQ C.M0)).2)),
   decide (C.kl ≤ O.kap.1),
   decide (O.kap.2 ≤ C.ku),
   decide (C.ml ≤ O.mu.1),
   decide (O.mu.2 ≤ C.mu),
   decide (C.cl ≤ 3 / O.aQ),
   decide (O.Au ≤ C.Au)].all id

/-- **Matveev's lower bound, as used** (an instance of Bugeaud–Mignotte–Siksek 2006, Thm 9.4,
real case, `n = 3`): for the positive reals `α₁, α₂, α₃` and the constant `C`, every
`Λ = α₁^x α₂^y α₃ − 1 ≠ 0` with `H = max(|x|, |y|) ≥ 1` has `log|Λ| > −C(1 + log H)`. -/
def MatveevLB (α1 α2 α3 C : ℝ) : Prop :=
  ∀ x y : ℤ, α1 ^ x * α2 ^ y * α3 ≠ 1 → 1 ≤ DirectReduction.hmax x y →
    -(C * (1 + Real.log (DirectReduction.hmax x y))) < Real.log |α1 ^ x * α2 ^ y * α3 - 1|

lemma abs_zpow' (x : ℝ) (k : ℤ) : |x ^ k| = |x| ^ k := map_zpow₀ (absHom (α := ℝ)) x k

lemma hmax_cast (x y : ℤ) : ((DirectReduction.hmax x y : ℤ) : ℝ) = max |(x : ℝ)| |(y : ℝ)| := by
  simp [DirectReduction.hmax]

lemma ratio_eq {phi phj phk gj gk gjr gkr e1j e1k e2j e2k s : ℝ} {x y : ℤ}
    (hs : s ≠ 0) (hgj : gj ≠ 0) (he1 : e1j ≠ 0) (he2 : e2j ≠ 0) (hik : phi - phk ≠ 0)
    (hj : gjr = s * (gj * (e1j ^ x * e2j ^ y))) (hk : gkr = s * (gk * (e1k ^ x * e2k ^ y))) :
    1 + ((phi - phj) * gkr / ((phi - phk) * gjr) - 1) =
      (phi - phj) * gk / ((phi - phk) * gj) * ((e1k / e1j) ^ x * (e2k / e2j) ^ y) := by
  have a := zpow_ne_zero x he1
  have b := zpow_ne_zero y he2
  rw [add_sub_cancel, hj, hk, div_zpow, div_zpow]
  field_simp
  ring

lemma log_split {g gr e1 e2 s : ℝ} {x y : ℤ} (hs : s = 1 ∨ s = -1) (hg : g ≠ 0) (he1 : e1 ≠ 0)
    (he2 : e2 ≠ 0) (h : gr = s * (g * (e1 ^ x * e2 ^ y))) :
    Real.log |gr| = Real.log |g| + (x * Real.log |e1| + y * Real.log |e2|) := by
  have hs1 : |s| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have a := zpow_ne_zero x (abs_ne_zero.mpr he1)
  have b := zpow_ne_zero y (abs_ne_zero.mpr he2)
  rw [h, abs_mul, hs1, one_mul, abs_mul, abs_mul, abs_zpow', abs_zpow',
    Real.log_mul (abs_ne_zero.mpr hg) (mul_ne_zero a b), Real.log_mul a b, Real.log_zpow,
    Real.log_zpow]

/-- The defining equations of `caseCompute`, stated for an opaque output so that no proof step
unfolds the computation. -/
structure Spec (p J em : ℕ) (Nq : ℚ) (V : ℕ) (B : Base) (O : Out) : Prop where
  dj : O.dj = absI (sub B.phj B.phi)
  dk : O.dk = absI (sub B.phk B.phi)
  K1 : O.K1 = rnd p (div (mul (ofQ (8 * Nq)) (absI (sub B.phj B.phk)))
    (mul (mul O.dj O.dj) (mul O.dk O.dk)))
  a1 : O.a1 = absI (div B.e1k B.e1j)
  a2 : O.a2 = absI (div B.e2k B.e2j)
  a3 : O.a3 = absI (div (mul (sub B.phi B.phj) B.gk) (mul (sub B.phi B.phk) B.gj))
  l1 : O.l1 = rnd p (logI p J O.a1)
  l2 : O.l2 = rnd p (logI p J O.a2)
  l3 : O.l3 = rnd p (logI p J O.a3)
  u1j : O.u1j = rnd p (logI p J (absI B.e1j))
  u2j : O.u2j = rnd p (logI p J (absI B.e2j))
  u1k : O.u1k = rnd p (logI p J (absI B.e1k))
  u2k : O.u2k = rnd p (logI p J (absI B.e2k))
  det : O.det = rnd p (sub (mul O.u1j O.u2k) (mul O.u2j O.u1k))
  aQ : O.aQ = rup p (max (div (absI (sub O.u2k O.u2j)) (absI O.det)).2
    (div (absI (sub O.u1j O.u1k)) (absI O.det)).2)
  nQ : O.nQ = rup p (max (div (add (absI O.u2k) (absI O.u2j)) (absI O.det)).2
    (div (add (absI O.u1j) (absI O.u1k)) (absI O.det)).2)
  tau : O.tau = rup p (div (ofQ (4 * Nq / ((V : ℚ) + 1) ^ 3)) (mul O.dj O.dk)).2
  wj : O.wj = ((sub (logI p J (div O.dj (ofQ 2))) (logI p J (absI B.gj))).1,
    (sub (logI p J (add O.dj (ofQ O.tau))) (logI p J (absI B.gj))).2)
  wk : O.wk = ((sub (logI p J (div O.dk (ofQ 2))) (logI p J (absI B.gk))).1,
    (sub (logI p J (add O.dk (ofQ O.tau))) (logI p J (absI B.gk))).2)
  R : O.R = max (max |O.wj.1| |O.wj.2|) (max |O.wk.1| |O.wk.2|)
  bb : O.bb = rup p (O.nQ * O.R)
  kap : O.kap = div O.l1 O.l2
  mu : O.mu = div O.l3 O.l2
  Au : O.Au = rup p (div (mul (ofQ 2) (mul O.K1 (ofQ (expHi p em (3 * O.bb / O.aQ))))) (absI O.l2)).2

lemma spec_caseCompute (p J em : ℕ) (Nq : ℚ) (V : ℕ) (B : Base) :
    Spec p J em Nq V B (caseCompute p J em Nq V B) := by
  constructor <;> rfl

/-- The enclosure of `log|t − φ| − log|γ₀|` at a far conjugate: `|φ − φᵢ|/2 ≤ |t − φ|` (Siegel)
and `|t − φ| ≤ |φ − φᵢ| + τ`. -/
lemma w_mem {p J : ℕ} {t phi ph g b : ℝ} {d gI : I} {tq : ℚ} (md : Mem |ph - phi| d)
    (mg : Mem g gI) (hd : 0 < |ph - phi|) (hb0 : 0 < |b|)
    (hge : |b| * |ph - phi| / 2 ≤ |b| * |t - ph|) (tp : 0 < |t - ph|) (htau : |t - phi| ≤ (tq : ℝ))
    (o1 : logOK p (div d (ofQ 2)) = true) (o2 : logOK p (absI gI) = true)
    (o3 : logOK p (add d (ofQ tq)) = true) :
    Mem (Real.log |t - ph| - Real.log |g|)
      ((sub (logI p J (div d (ofQ 2))) (logI p J (absI gI))).1,
       (sub (logI p J (add d (ofQ tq))) (logI p J (absI gI))).2) := by
  have hlo : |ph - phi| / 2 ≤ |t - ph| := by
    rw [mul_div_assoc] at hge; exact le_of_mul_le_mul_left hge hb0
  have hhi : |t - ph| ≤ |ph - phi| + tq := by
    have := abs_sub_le t phi ph
    rw [abs_sub_comm phi ph] at this; linarith
  have n2 : nz (ofQ 2) = true := by norm_num [nz, ofQ]
  have ml1 := mem_log p J (mem_div md (mem_ofQ 2) n2) o1
  have ml2 := mem_log p J (mem_abs mg) o2
  have ml3 := mem_log p J (mem_add md (mem_ofQ tq)) o3
  have e2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [e2] at ml1
  have a1 := Real.log_le_log (half_pos hd) hlo
  have a3 := Real.log_le_log tp hhi
  generalize logI p J (div d (ofQ 2)) = X1 at ml1 ⊢
  generalize logI p J (absI gI) = X2 at ml2 ⊢
  generalize logI p J (add d (ofQ tq)) = X3 at ml3 ⊢
  constructor
  · simp only [sub, add, neg, Rat.cast_add, Rat.cast_neg]
    linarith [ml1.1, ml2.2]
  · simp only [sub, add, neg, Rat.cast_add, Rat.cast_neg]
    linarith [ml3.2, ml2.1]

set_option maxHeartbeats 1000000 in
/-- **One case is sound**: the interval checks, the Matveev instance and the facts of one solution
give the analytic inequality of the case. -/
theorem real_case {p J em : ℕ} {Nq : ℚ} {V : ℕ} {Cm : ℚ} {B : Base} {C : UnitPremises.Case}
    (hok : caseOK p J em Nq V Cm B C = true)
    {phi phj phk gj gk e1j e1k e2j e2k : ℝ}
    (m_phi : Mem phi B.phi) (m_phj : Mem phj B.phj) (m_phk : Mem phk B.phk) (m_gj : Mem gj B.gj)
    (m_gk : Mem gk B.gk) (m_e1j : Mem e1j B.e1j) (m_e1k : Mem e1k B.e1k) (m_e2j : Mem e2j B.e2j)
    (m_e2k : Mem e2k B.e2k)
    (hmat : MatveevLB |e1k / e1j| |e2k / e2j| |(phi - phj) * gk / ((phi - phk) * gj)| Cm)
    {b t gi gjr gkr N s : ℝ} {x y : ℤ}
    (hs : s = 1 ∨ s = -1) (hN : |N| = Nq) (hN0 : N ≠ 0)
    (hgi : gi = b * (t - phi)) (hgjr : gjr = b * (t - phj)) (hgkr : gkr = b * (t - phk))
    (hprod : gi * gjr * gkr = N)
    (hij : |t - phi| ≤ |t - phj|) (hik : |t - phi| ≤ |t - phk|)
    (hb : (V : ℝ) + 1 ≤ |b|)
    (hj : gjr = s * (gj * (e1j ^ x * e2j ^ y))) (hk : gkr = s * (gk * (e1k ^ x * e2k ^ y))) :
    UnitPremises.LinIneq C x y := by
  simp only [caseOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id,
    decide_eq_true_eq] at hok
  have hS := spec_caseCompute p J em Nq V B
  generalize caseCompute p J em Nq V B = O at hok hS
  obtain ⟨n_ij, n_ik, n_jk, n_e1j, n_e1k, n_e2j, n_e2k, n_gj, n_gk, o_a1, o_a2, o_a3, o_e1j, o_e2j,
    o_e1k, o_e2k, o_dj2, o_gj, o_djt, o_dk2, o_gk, o_dkt, o_K1, o_M0, n_det, n_l2, n_djdk, n_dd,
    n_adet, n_al2, n_den, -, -, c_a, c_N, c_K1, c_bb, c_exp, c_C, c_M1, c_Ma, c_chk, c_kl, c_ku,
    c_ml, c_mu, c_cl, c_Au⟩ := hok
  -- basic nonvanishing
  have dij : phi ≠ phj := fun h => nz_ne (mem_sub m_phi m_phj) n_ij (by rw [h, sub_self])
  have dik : phi ≠ phk := fun h => nz_ne (mem_sub m_phi m_phk) n_ik (by rw [h, sub_self])
  have djk : phj ≠ phk := fun h => nz_ne (mem_sub m_phj m_phk) n_jk (by rw [h, sub_self])
  have z_e1j := nz_ne m_e1j n_e1j
  have z_e1k := nz_ne m_e1k n_e1k
  have z_e2j := nz_ne m_e2j n_e2j
  have z_e2k := nz_ne m_e2k n_e2k
  have z_gj := nz_ne m_gj n_gj
  have z_gk := nz_ne m_gk n_gk
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hV0 : (0 : ℝ) ≤ V := by positivity
  have hb0 : 0 < |b| := by linarith
  have hbne : b ≠ 0 := abs_pos.mp hb0
  have hb3 : (0 : ℝ) < |b| ^ 3 := by positivity
  have hdj0 : 0 < |phj - phi| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm dij))
  have hdk0 : 0 < |phk - phi| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm dik))
  -- interval memberships
  have m_dj : Mem |phj - phi| O.dj := by rw [hS.dj]; exact mem_abs (mem_sub m_phj m_phi)
  have m_dk : Mem |phk - phi| O.dk := by rw [hS.dk]; exact mem_abs (mem_sub m_phk m_phi)
  have m_djk : Mem |phj - phk| (absI (sub B.phj B.phk)) := mem_abs (mem_sub m_phj m_phk)
  have hNq : ((8 * Nq : ℚ) : ℝ) = 8 * |N| := by push_cast; rw [hN]
  obtain ⟨K1r, hK1r⟩ : ∃ K : ℝ, K = 8 * |N| * |phj - phk| / (|phj - phi| ^ 2 * |phk - phi| ^ 2) :=
    ⟨_, rfl⟩
  have m_K1 : Mem K1r O.K1 := by
    rw [hS.K1]
    have h := mem_rnd p (mem_div (mem_mul (mem_ofQ (8 * Nq)) m_djk)
      (mem_mul (mem_mul m_dj m_dj) (mem_mul m_dk m_dk)) n_dd)
    rw [hNq] at h
    convert h using 1
    rw [hK1r]; ring
  have hK0 : 0 < K1r := by
    rw [hK1r]
    exact div_pos (mul_pos (mul_pos (by norm_num) (abs_pos.mpr hN0))
      (abs_pos.mpr (sub_ne_zero.mpr djk))) (mul_pos (pow_pos hdj0 2) (pow_pos hdk0 2))
  obtain ⟨α1, hα1⟩ : ∃ a : ℝ, a = |e1k / e1j| := ⟨_, rfl⟩
  obtain ⟨α2, hα2⟩ : ∃ a : ℝ, a = |e2k / e2j| := ⟨_, rfl⟩
  obtain ⟨α3, hα3⟩ : ∃ a : ℝ, a = |(phi - phj) * gk / ((phi - phk) * gj)| := ⟨_, rfl⟩
  rw [← hα1, ← hα2, ← hα3] at hmat
  have m_a1 : Mem α1 O.a1 := by rw [hα1, hS.a1]; exact mem_abs (mem_div m_e1k m_e1j n_e1j)
  have m_a2 : Mem α2 O.a2 := by rw [hα2, hS.a2]; exact mem_abs (mem_div m_e2k m_e2j n_e2j)
  have m_a3 : Mem α3 O.a3 := by
    rw [hα3, hS.a3]
    exact mem_abs (mem_div (mem_mul (mem_sub m_phi m_phj) m_gk) (mem_mul (mem_sub m_phi m_phk) m_gj)
      n_den)
  have pa1 : 0 < α1 := by rw [hα1]; exact abs_pos.mpr (div_ne_zero z_e1k z_e1j)
  have pa2 : 0 < α2 := by rw [hα2]; exact abs_pos.mpr (div_ne_zero z_e2k z_e2j)
  have pa3 : 0 < α3 := by
    rw [hα3]
    exact abs_pos.mpr (div_ne_zero (mul_ne_zero (sub_ne_zero.mpr dij) z_gk)
      (mul_ne_zero (sub_ne_zero.mpr dik) z_gj))
  have m_l1 : Mem (Real.log α1) O.l1 := by rw [hS.l1]; exact mem_rnd p (mem_log p J m_a1 o_a1)
  have m_l2 : Mem (Real.log α2) O.l2 := by rw [hS.l2]; exact mem_rnd p (mem_log p J m_a2 o_a2)
  have m_l3 : Mem (Real.log α3) O.l3 := by rw [hS.l3]; exact mem_rnd p (mem_log p J m_a3 o_a3)
  obtain ⟨u1j, hu1j⟩ : ∃ u : ℝ, u = Real.log |e1j| := ⟨_, rfl⟩
  obtain ⟨u2j, hu2j⟩ : ∃ u : ℝ, u = Real.log |e2j| := ⟨_, rfl⟩
  obtain ⟨u1k, hu1k⟩ : ∃ u : ℝ, u = Real.log |e1k| := ⟨_, rfl⟩
  obtain ⟨u2k, hu2k⟩ : ∃ u : ℝ, u = Real.log |e2k| := ⟨_, rfl⟩
  have m_u1j : Mem u1j O.u1j := by
    rw [hu1j, hS.u1j]; exact mem_rnd p (mem_log p J (mem_abs m_e1j) o_e1j)
  have m_u2j : Mem u2j O.u2j := by
    rw [hu2j, hS.u2j]; exact mem_rnd p (mem_log p J (mem_abs m_e2j) o_e2j)
  have m_u1k : Mem u1k O.u1k := by
    rw [hu1k, hS.u1k]; exact mem_rnd p (mem_log p J (mem_abs m_e1k) o_e1k)
  have m_u2k : Mem u2k O.u2k := by
    rw [hu2k, hS.u2k]; exact mem_rnd p (mem_log p J (mem_abs m_e2k) o_e2k)
  have m_det : Mem (u1j * u2k - u2j * u1k) O.det := by
    rw [hS.det]; exact mem_rnd p (mem_sub (mem_mul m_u1j m_u2k) (mem_mul m_u2j m_u1k))
  have z_det : u1j * u2k - u2j * u1k ≠ 0 := nz_ne m_det n_det
  have z_l2 : Real.log α2 ≠ 0 := nz_ne m_l2 n_l2
  -- Siegel
  have e := ratio_eq (phi := phi) (phj := phj) hs0 z_gj z_e1j z_e2j (sub_ne_zero.mpr dik) hj hk
  obtain ⟨b1, b2, b3, -, hΛ0, hΛb⟩ :=
    siegel hbne hgi hgjr hgkr hij hik hprod hN0 dij dik djk
  generalize (phi - phj) * gkr / ((phi - phk) * gjr) - 1 = Λ at e hΛ0 hΛb
  have hΛhalf : |Λ| ≤ 1 / 2 := by
    have c1 : 2 * (O.K1.2 : ℝ) ≤ ((V : ℝ) + 1) ^ 3 := by exact_mod_cast c_K1
    have hK1hi : K1r ≤ O.K1.2 := m_K1.2
    have hVb : ((V : ℝ) + 1) ^ 3 ≤ |b| ^ 3 := pow_le_pow_left₀ (by positivity) hb 3
    rw [hK1r] at hK1hi
    have : |Λ| * |b| ^ 3 ≤ 1 / 2 * |b| ^ 3 := by linarith
    exact le_of_mul_le_mul_right this hb3
  obtain ⟨h1Λ, hlogΛ⟩ := log_one_add_le hΛhalf
  -- 1 + Λ = α₁^x α₂^y α₃
  have h1Λ' : 1 + Λ = α1 ^ x * α2 ^ y * α3 := by
    rw [← abs_of_pos h1Λ, e, abs_mul, abs_mul, abs_zpow', abs_zpow', hα1, hα2, hα3]
    ring
  have hlog1 : Real.log (1 + Λ) = x * Real.log α1 + y * Real.log α2 + Real.log α3 := by
    rw [h1Λ', Real.log_mul (mul_pos (zpow_pos pa1 x) (zpow_pos pa2 y)).ne' pa3.ne',
      Real.log_mul (zpow_pos pa1 x).ne' (zpow_pos pa2 y).ne', Real.log_zpow, Real.log_zpow]
  -- the exponent system
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log |b| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by linarith)
  have tj0 : 0 < |t - phj| := by
    have : 0 < |gjr| := lt_of_lt_of_le (div_pos (mul_pos hb0 hdj0) two_pos) b1
    rw [hgjr, abs_mul] at this; exact pos_of_mul_pos_right this hb0.le
  have tk0 : 0 < |t - phk| := by
    have : 0 < |gkr| := lt_of_lt_of_le (div_pos (mul_pos hb0 hdk0) two_pos) b2
    rw [hgkr, abs_mul] at this; exact pos_of_mul_pos_right this hb0.le
  have sysj : x * u1j + y * u2j = L + (Real.log |t - phj| - Real.log |gj|) := by
    have e1 := log_split hs z_gj z_e1j z_e2j hj
    have e2 : Real.log |gjr| = L + Real.log |t - phj| := by
      rw [hgjr, abs_mul, Real.log_mul hb0.ne' tj0.ne', hL]
    rw [← hu1j, ← hu2j] at e1
    linarith
  have sysk : x * u1k + y * u2k = L + (Real.log |t - phk| - Real.log |gk|) := by
    have e1 := log_split hs z_gk z_e1k z_e2k hk
    have e2 : Real.log |gkr| = L + Real.log |t - phk| := by
      rw [hgkr, abs_mul, Real.log_mul hb0.ne' tk0.ne', hL]
    rw [← hu1k, ← hu2k] at e1
    linarith
  -- bounds on w
  have htau : |t - phi| ≤ (O.tau : ℝ) := by
    have hVb : ((V : ℝ) + 1) ^ 3 ≤ |b| ^ 3 := pow_le_pow_left₀ (by positivity) hb 3
    have h1 : |t - phi| ≤ 4 * |N| / (|b| ^ 3 * (|phj - phi| * |phk - phi|)) := by
      rw [le_div_iff₀ (mul_pos hb3 (mul_pos hdj0 hdk0))]; exact b3
    have h2 : 4 * |N| / (|b| ^ 3 * (|phj - phi| * |phk - phi|)) ≤
        4 * |N| / ((V + 1) ^ 3) / (|phj - phi| * |phk - phi|) := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos (by positivity) (mul_pos hdj0 hdk0))
      exact mul_le_mul_of_nonneg_right hVb (by positivity)
    have h3 := (mem_div (mem_ofQ (4 * Nq / ((V : ℚ) + 1) ^ 3)) (mem_mul m_dj m_dk) n_djdk).2
    have h4 : (((4 * Nq / ((V : ℚ) + 1) ^ 3 : ℚ) : ℝ)) = 4 * |N| / ((V + 1) ^ 3) := by
      push_cast; rw [hN]
    rw [h4] at h3
    rw [hS.tau]
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_rup_R p _)))
  have hjge : |b| * |phj - phi| / 2 ≤ |b| * |t - phj| := by
    have := b1; rw [hgjr, abs_mul] at this; exact this
  have hkge : |b| * |phk - phi| / 2 ≤ |b| * |t - phk| := by
    have := b2; rw [hgkr, abs_mul] at this; exact this
  have m_wj : Mem (Real.log |t - phj| - Real.log |gj|) O.wj := by
    rw [hS.wj]; exact w_mem m_dj m_gj hdj0 hb0 hjge tj0 htau o_dj2 o_gj o_djt
  have m_wk : Mem (Real.log |t - phk| - Real.log |gk|) O.wk := by
    rw [hS.wk]; exact w_mem m_dk m_gk hdk0 hb0 hkge tk0 htau o_dk2 o_gk o_dkt
  have hRj : |(Real.log |t - phj| - Real.log |gj|)| ≤ (O.R : ℝ) := by
    rw [hS.R]
    simp only [Rat.cast_max, Rat.cast_abs]
    exact le_max_of_le_left (DirectReduction.abs_le_of_between m_wj.1 m_wj.2)
  have hRk : |(Real.log |t - phk| - Real.log |gk|)| ≤ (O.R : ℝ) := by
    rw [hS.R]
    simp only [Rat.cast_max, Rat.cast_abs]
    exact le_max_of_le_right (DirectReduction.abs_le_of_between m_wk.1 m_wk.2)
  -- the slope bounds
  have m_ad : Mem |u1j * u2k - u2j * u1k| (absI O.det) := mem_abs m_det
  have ha1 : |u2k - u2j| / |u1j * u2k - u2j * u1k| ≤ (O.aQ : ℝ) := by
    have := (mem_div (mem_abs (mem_sub m_u2k m_u2j)) m_ad n_adet).2
    rw [hS.aQ]
    exact le_trans this (le_trans (by exact_mod_cast le_max_left _ _) (le_rup_R p _))
  have ha2 : |u1j - u1k| / |u1j * u2k - u2j * u1k| ≤ (O.aQ : ℝ) := by
    have := (mem_div (mem_abs (mem_sub m_u1j m_u1k)) m_ad n_adet).2
    rw [hS.aQ]
    exact le_trans this (le_trans (by exact_mod_cast le_max_right _ _) (le_rup_R p _))
  have hn1 : (|u2k| + |u2j|) / |u1j * u2k - u2j * u1k| ≤ (O.nQ : ℝ) := by
    have := (mem_div (mem_add (mem_abs m_u2k) (mem_abs m_u2j)) m_ad n_adet).2
    rw [hS.nQ]
    exact le_trans this (le_trans (by exact_mod_cast le_max_left _ _) (le_rup_R p _))
  have hn2 : (|u1j| + |u1k|) / |u1j * u2k - u2j * u1k| ≤ (O.nQ : ℝ) := by
    have := (mem_div (mem_add (mem_abs m_u1j) (mem_abs m_u1k)) m_ad n_adet).2
    rw [hS.nQ]
    exact le_trans this (le_trans (by exact_mod_cast le_max_right _ _) (le_rup_R p _))
  obtain ⟨hx, hy⟩ := exps_le sysj sysk z_det hL0 hRj hRk ha1 ha2 hn1 hn2
  have hbb : (O.nQ : ℝ) * O.R ≤ O.bb := by rw [hS.bb]; exact_mod_cast le_rup p _
  have haQ : (0 : ℝ) < O.aQ := by exact_mod_cast c_a
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ((DirectReduction.hmax x y : ℤ) : ℝ) := ⟨_, rfl⟩
  have hHle : H ≤ O.aQ * L + O.bb := by
    rw [hH, hmax_cast]
    exact max_le (by linarith [hx]) (by linarith [hy])
  -- Matveev ⇒ H < M₀
  have hexpL : Real.exp (3 * L) = |b| ^ 3 := by
    rw [show 3 * L = (3 : ℕ) * L by norm_num, Real.exp_nat_mul, hL, Real.exp_log hb0]
  have hΛK : |Λ| ≤ K1r * Real.exp (-(3 * L)) := by
    rw [Real.exp_neg, hexpL, ← div_eq_mul_inv, le_div_iff₀ hb3, hK1r]; exact hΛb
  have hval : α1 ^ x * α2 ^ y * α3 - 1 = Λ := by rw [← h1Λ']; ring
  have hMat : 1 ≤ H → -((Cm : ℝ) * (1 + Real.log H)) < Real.log |Λ| := by
    intro h1
    rw [hH] at h1 ⊢
    have := hmat x y (by rw [← h1Λ']; intro h; apply hΛ0; linarith) (by exact_mod_cast h1)
    rwa [hval] at this
  have hC0 : (0 : ℝ) ≤ Cm := by exact_mod_cast c_C
  have hchkR : 0 < 3 / (O.aQ : ℝ) * (C.M0 : ℝ) - Real.log K1r - 3 * O.bb / O.aQ -
      Cm * (1 + Real.log (C.M0 : ℝ)) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr c_chk
    push_cast at h
    have e1 := (mem_log p J m_K1 o_K1).2
    have e2 := (mem_log p J (mem_ofQ (C.M0 : ℚ)) o_M0).2
    push_cast at e2
    have e3 := mul_le_mul_of_nonneg_left (add_le_add_left e2 1) hC0
    linarith
  have hlt := matveev_cutoff haQ hK0 hC0 (by exact_mod_cast c_M1)
    (by have := (Rat.cast_le (K := ℝ)).mpr c_Ma; push_cast at this; exact this) hHle hΛ0 hΛK hMat
    hchkR
  -- the linear form
  have hform : |x * Real.log α1 + y * Real.log α2 + Real.log α3| ≤
      2 * K1r * Real.exp (3 * O.bb / O.aQ) * Real.exp (-(3 / (O.aQ : ℝ) * H)) := by
    rw [← hlog1]
    have hE : Real.exp (-(3 * L)) ≤
        Real.exp (3 * O.bb / O.aQ) * Real.exp (-(3 / (O.aQ : ℝ) * H)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hq : 3 / (O.aQ : ℝ) * H ≤ 3 * L + 3 * O.bb / O.aQ := by
        have ha0 := haQ.ne'
        have e4 : 3 * L + 3 * (O.bb : ℝ) / O.aQ = 3 / O.aQ * (O.aQ * L + O.bb) := by
          field_simp; ring
        rw [e4]
        exact mul_le_mul_of_nonneg_left hHle (by positivity)
      linarith
    calc |Real.log (1 + Λ)| ≤ 2 * |Λ| := hlogΛ
      _ ≤ 2 * (K1r * Real.exp (-(3 * L))) := by linarith
      _ ≤ 2 * (K1r * (Real.exp (3 * O.bb / O.aQ) * Real.exp (-(3 / (O.aQ : ℝ) * H)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hK0.le) (by norm_num)
      _ = _ := by ring
  rw [hS.kap] at c_kl c_ku
  rw [hS.mu] at c_ml c_mu
  rw [hS.Au] at c_Au
  refine ⟨Real.log α1 / Real.log α2, Real.log α3 / Real.log α2, 3 / (O.aQ : ℝ),
    2 * K1r * Real.exp (3 * O.bb / O.aQ) / |Real.log α2|, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast c_kl) (mem_div m_l1 m_l2 n_l2).1
  · exact le_trans (mem_div m_l1 m_l2 n_l2).2 (by exact_mod_cast c_ku)
  · exact le_trans (by exact_mod_cast c_ml) (mem_div m_l3 m_l2 n_l2).1
  · exact le_trans (mem_div m_l3 m_l2 n_l2).2 (by exact_mod_cast c_mu)
  · have := (Rat.cast_le (K := ℝ)).mpr c_cl; push_cast at this; exact this
  · have hexp := exp_le_expHi p em c_exp
    push_cast at hexp
    have hA := (mem_div (mem_mul (mem_ofQ 2)
      (mem_mul m_K1 (mem_ofQ (expHi p em (3 * O.bb / O.aQ))))) (mem_abs m_l2) n_al2).2
    have hl2 : 0 < |Real.log α2| := abs_pos.mpr z_l2
    calc 2 * K1r * Real.exp (3 * O.bb / O.aQ) / |Real.log α2|
        ≤ ((2 : ℚ) : ℝ) * (K1r * ((expHi p em (3 * O.bb / O.aQ) : ℚ) : ℝ)) / |Real.log α2| := by
          apply div_le_div_of_nonneg_right _ hl2.le
          rw [show ((2 : ℚ) : ℝ) = 2 by norm_num, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left hexp (by linarith)
      _ ≤ _ := hA
      _ ≤ _ := le_rup_R p _
      _ ≤ C.Au := by exact_mod_cast c_Au
  · have : ((DirectReduction.hmax x y : ℤ) : ℝ) < (C.M0 : ℝ) := by rw [← hH]; exact hlt
    have : ((DirectReduction.hmax x y : ℤ) : ℝ) < ((C.M0 : ℤ) : ℝ) := by exact_mod_cast this
    exact (Int.cast_lt.mp this).le
  · have hl2 : 0 < |Real.log α2| := abs_pos.mpr z_l2
    have e5 : Real.log α1 / Real.log α2 * (x : ℝ) + y + Real.log α3 / Real.log α2 =
        (x * Real.log α1 + y * Real.log α2 + Real.log α3) / Real.log α2 := by field_simp; ring
    rw [e5, abs_div, div_le_iff₀ hl2, ← hH]
    calc _ ≤ 2 * K1r * Real.exp (3 * O.bb / O.aQ) * Real.exp (-(3 / (O.aQ : ℝ) * H)) := hform
      _ = _ := by field_simp

/-! ### The class-level theorem

The roots of `X³ − PX − Q` come from rational brackets with a sign change (`rootIn`).  The
embedding of an element at a root lies in `sigI` of its bracket.  At a solution, `t = c₀a/b` has a
closest conjugate `φᵢ` (a minimum over `Fin 3`), and the case `i` of the class applies. -/

open UnitGenProof in
/-- A root of `X³ − PX − Q` in `[lo, hi]` (chosen; `0` if the bracket has no sign change). -/
noncomputable def rootIn (P Q : ℤ) (lo hi : ℚ) : ℝ :=
  if h : lo ≤ hi ∧ cub P Q lo * cub P Q hi < 0 then Classical.choose (root_in P Q lo hi h.1 h.2) else 0

open UnitGenProof in
lemma rootIn_spec {P Q : ℤ} {lo hi : ℚ} (h1 : lo ≤ hi) (h2 : cub P Q lo * cub P Q hi < 0) :
    (lo : ℝ) ≤ rootIn P Q lo hi ∧ rootIn P Q lo hi ≤ hi ∧
      rootIn P Q lo hi ^ 3 = P * rootIn P Q lo hi + Q := by
  unfold rootIn
  rw [dif_pos ⟨h1, h2⟩]
  exact Classical.choose_spec (root_in P Q lo hi h1 h2)

open UnitGenProof in
/-- The embedding of `g` over a bracket: `σ(lo) ± rad`. -/
def sigI (g : UnitBox.Z3) (lo hi : ℚ) : I := (sigQ lo g - rad g lo hi, sigQ lo g + rad g lo hi)

open UnitGenProof in
lemma mem_sigI (g : UnitBox.Z3) {lo hi : ℚ} {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    Mem (sig t g) (sigI g lo hi) := by
  have hR := abs_le_max_of h1 h2
  have hR0 : |(lo : ℝ)| ≤ ((max |lo| |hi| : ℚ) : ℝ) := by push_cast; exact le_max_left _ _
  have hd : sig t g - ((sigQ lo g : ℚ) : ℝ) = (t - lo) * (g.2.1 + g.2.2 * (t + lo)) := by
    simp only [sig, sigQ]; push_cast; ring
  have hb : |sig t g - ((sigQ lo g : ℚ) : ℝ)| ≤ ((rad g lo hi : ℚ) : ℝ) := by
    rw [hd, abs_mul]
    have e1 : |t - lo| ≤ (hi : ℝ) - lo := by rw [abs_of_nonneg (by linarith)]; linarith
    have e2 : |(g.2.1 : ℝ) + g.2.2 * (t + lo)| ≤
        |(g.2.1 : ℝ)| + 2 * |(g.2.2 : ℝ)| * ((max |lo| |hi| : ℚ) : ℝ) := by
      calc _ ≤ |(g.2.1 : ℝ)| + |(g.2.2 : ℝ) * (t + lo)| := abs_add_le _ _
        _ = |(g.2.1 : ℝ)| + |(g.2.2 : ℝ)| * |t + lo| := by rw [abs_mul]
        _ ≤ _ := by
          have : |t + lo| ≤ 2 * ((max |lo| |hi| : ℚ) : ℝ) := by
            calc |t + lo| ≤ |t| + |(lo : ℝ)| := abs_add_le _ _
              _ ≤ _ := by linarith
          nlinarith [abs_nonneg (g.2.2 : ℝ)]
    calc |t - lo| * |(g.2.1 : ℝ) + g.2.2 * (t + lo)|
        ≤ ((hi : ℝ) - lo) * (|(g.2.1 : ℝ)| + 2 * |(g.2.2 : ℝ)| * ((max |lo| |hi| : ℚ) : ℝ)) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by linarith)
      _ = ((rad g lo hi : ℚ) : ℝ) := by simp only [rad]; push_cast; ring
  have := abs_le.mp hb
  constructor
  · simp only [sigI]; push_cast; linarith
  · simp only [sigI]; push_cast; linarith

/-- The two other conjugates of case `i`: `j`. -/
def oj : Fin 3 → Fin 3 := ![1, 0, 0]
/-- The two other conjugates of case `i`: `k`. -/
def ok : Fin 3 → Fin 3 := ![2, 2, 1]

/-- **The analytic certificate of one class**: root brackets, the interval precision `p`, the
series length `J`, the squaring count `em`, and the Matveev constant of each case. -/
structure ACert where
  /-- Lower ends of the root brackets. -/
  lo : Fin 3 → ℚ
  /-- Upper ends of the root brackets. -/
  hi : Fin 3 → ℚ
  /-- Rounding grid `2^-p`. -/
  p : ℕ
  /-- Terms of the `atanh` series. -/
  J : ℕ
  /-- Squarings in the exponential bound. -/
  em : ℕ
  /-- Matveev's constant, per case. -/
  Cm : Fin 3 → ℚ

/-- The brackets have sign changes and are ordered (so the roots are distinct). -/
def bracketsOK (P Q : ℤ) (A : ACert) : Bool :=
  decide (∀ l : Fin 3, A.lo l ≤ A.hi l ∧
    UnitGenProof.cub P Q (A.lo l) * UnitGenProof.cub P Q (A.hi l) < 0) &&
  decide (A.hi 0 < A.lo 1) && decide (A.hi 1 < A.lo 2)

/-- The interval data of case `i`. -/
def baseOf (A : ACert) (phi g0 e1 e2 : UnitBox.Z3) (i : Fin 3) : Base :=
  { phi := rnd A.p (sigI phi (A.lo i) (A.hi i)),
    phj := rnd A.p (sigI phi (A.lo (oj i)) (A.hi (oj i))),
    phk := rnd A.p (sigI phi (A.lo (ok i)) (A.hi (ok i))),
    gj := rnd A.p (sigI g0 (A.lo (oj i)) (A.hi (oj i))),
    gk := rnd A.p (sigI g0 (A.lo (ok i)) (A.hi (ok i))),
    e1j := rnd A.p (sigI e1 (A.lo (oj i)) (A.hi (oj i))),
    e1k := rnd A.p (sigI e1 (A.lo (ok i)) (A.hi (ok i))),
    e2j := rnd A.p (sigI e2 (A.lo (oj i)) (A.hi (oj i))),
    e2k := rnd A.p (sigI e2 (A.lo (ok i)) (A.hi (ok i))) }

/-- The root of bracket `l`. -/
noncomputable def tR (P Q : ℤ) (A : ACert) (l : Fin 3) : ℝ := rootIn P Q (A.lo l) (A.hi l)

/-- The embedding of `g` at the root of bracket `l`. -/
noncomputable def sR (P Q : ℤ) (A : ACert) (g : UnitBox.Z3) (l : Fin 3) : ℝ :=
  UnitGenProof.sig (tR P Q A l) g

/-- **Matveev's lower bound for case `i`** of a class: `MatveevLB` at
`α₁ = |σₖ(ε₁)/σⱼ(ε₁)|`, `α₂ = |σₖ(ε₂)/σⱼ(ε₂)|`, `α₃ = |(φᵢ − φⱼ)σₖ(γ₀) / ((φᵢ − φₖ)σⱼ(γ₀))|`
with the constant `Cm i`. -/
def MatveevCase (P Q : ℤ) (A : ACert) (phi g0 e1 e2 : UnitBox.Z3) (i : Fin 3) : Prop :=
  MatveevLB |sR P Q A e1 (ok i) / sR P Q A e1 (oj i)| |sR P Q A e2 (ok i) / sR P Q A e2 (oj i)|
    |(sR P Q A phi i - sR P Q A phi (oj i)) * sR P Q A g0 (ok i) /
      ((sR P Q A phi i - sR P Q A phi (ok i)) * sR P Q A g0 (oj i))| (A.Cm i)

lemma sig_enc (t : ℝ) (c0 : ℤ) (phi : UnitBox.Z3) (a b : ℤ) :
    UnitGenProof.sig t (UnitBox.enc c0 phi a b) = c0 * a - b * UnitGenProof.sig t phi := by
  simp only [UnitGenProof.sig, UnitBox.enc]; push_cast; ring

/-- **The analytic premise of a class, from Matveev's lower bound.**  Everything except the three
`MatveevCase` instances is proved here or checked by evaluation (`bracketsOK`, `caseOK`). -/
theorem analytic_of_cert (F : ThueLocal.Form) (M P Q : ℤ) (phi g0 e1 e1i e2 e2i : UnitBox.Z3) (V : ℕ) (A : ACert)
    (C0 C1 C2 : UnitPremises.Case)
    (h1 : UnitBox.mul P Q e1 e1i = (1, 0, 0)) (h2 : UnitBox.mul P Q e2 e2i = (1, 0, 0))
    (hnorm : ∀ a b, UnitPremises.nrm P Q (UnitBox.enc F.1 phi a b) = F.1 ^ 2 * ThueLocal.evalF F a b)
    (hbr : bracketsOK P Q A = true) (hF0 : F.1 ≠ 0) (hM0 : M ≠ 0)
    (hc : ∀ i, caseOK A.p A.J A.em ((|F.1 ^ 2 * M| : ℤ) : ℚ) V (A.Cm i) (baseOf A phi g0 e1 e2 i)
      (![C0, C1, C2] i) = true)
    (hmat : ∀ i, MatveevCase P Q A phi g0 e1 e2 i) :
    UnitPremises.Analytic F M P Q phi e1 e1i e2 e2i V [(g0, [C0, C1, C2])] := by
  intro a b hF hb r hr x y hcases
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [bracketsOK, Bool.and_eq_true, decide_eq_true_eq] at hbr
  obtain ⟨⟨hbl, h01⟩, h12⟩ := hbr
  have hroot : ∀ l, (A.lo l : ℝ) ≤ tR P Q A l ∧ tR P Q A l ≤ A.hi l ∧
      tR P Q A l ^ 3 = P * tR P Q A l + Q := fun l => rootIn_spec (hbl l).1 (hbl l).2
  have d01 : tR P Q A 0 < tR P Q A 1 := by
    have : ((A.hi 0 : ℚ) : ℝ) < A.lo 1 := by exact_mod_cast h01
    linarith [(hroot 0).2.1, (hroot 1).1]
  have d12 : tR P Q A 1 < tR P Q A 2 := by
    have : ((A.hi 1 : ℚ) : ℝ) < A.lo 2 := by exact_mod_cast h12
    linarith [(hroot 1).2.1, (hroot 2).1]
  let R : UnitGenProof.Roots P Q :=
    { t1 := tR P Q A 0, t2 := tR P Q A 1, t3 := tR P Q A 2, h1 := (hroot 0).2.2,
      h2 := (hroot 1).2.2, h3 := (hroot 2).2.2, d12 := d01.ne, d13 := (d01.trans d12).ne,
      d23 := d12.ne }
  have hbR : (V : ℝ) + 1 ≤ |(b : ℝ)| := by
    have : (V : ℤ) + 1 ≤ |b| := hb
    have h' : (((V : ℤ) + 1 : ℤ) : ℝ) ≤ ((|b| : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h'; exact h'
  have hb0 : (b : ℝ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hbR; linarith [show (0 : ℝ) ≤ V by positivity]
  set tt : ℝ := (F.1 : ℝ) * a / b with htt
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun l => |tt - sR P Q A phi l|)
    ⟨0, Finset.mem_univ _⟩
  refine ⟨![C0, C1, C2] i, by fin_cases i <;> simp, ?_⟩
  have hg : ∀ l, sR P Q A (UnitBox.enc F.1 phi a b) l = b * (tt - sR P Q A phi l) := by
    intro l
    simp only [sR, sig_enc, htt]
    field_simp
  obtain ⟨s, hs, hγ⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ l, sR P Q A (UnitBox.enc F.1 phi a b) l =
      s * (sR P Q A g0 l * (sR P Q A e1 l ^ x * sR P Q A e2 l ^ y)) := by
    rcases hcases with h | h
    · refine ⟨1, Or.inl rfl, fun l => ?_⟩
      simp only [sR]
      rw [h, UnitGenProof.sig_mul (hroot l).2.2, UnitGenProof.sig_mul (hroot l).2.2,
        UnitGenProof.sig_zp (hroot l).2.2 h1, UnitGenProof.sig_zp (hroot l).2.2 h2]
      ring
    · refine ⟨-1, Or.inr rfl, fun l => ?_⟩
      simp only [sR]
      rw [h, UnitGenProof.sig_neg, UnitGenProof.sig_mul (hroot l).2.2,
        UnitGenProof.sig_mul (hroot l).2.2, UnitGenProof.sig_zp (hroot l).2.2 h1,
        UnitGenProof.sig_zp (hroot l).2.2 h2]
      ring
  have hperm : ∀ f : Fin 3 → ℝ, f i * f (oj i) * f (ok i) = f 0 * f 1 * f 2 := by
    intro f
    fin_cases i
    · rfl
    · show f 1 * f 0 * f 2 = f 0 * f 1 * f 2; ring
    · show f 2 * f 0 * f 1 = f 0 * f 1 * f 2; ring
  have hprod : sR P Q A (UnitBox.enc F.1 phi a b) i * sR P Q A (UnitBox.enc F.1 phi a b) (oj i) *
      sR P Q A (UnitBox.enc F.1 phi a b) (ok i) = ((F.1 ^ 2 * M : ℤ) : ℝ) := by
    rw [hperm (sR P Q A (UnitBox.enc F.1 phi a b))]
    have := R.nrm_eq (UnitBox.enc F.1 phi a b)
    rw [hnorm, hF] at this
    rw [this]; rfl
  have hN : |((F.1 ^ 2 * M : ℤ) : ℝ)| = ((((|F.1 ^ 2 * M| : ℤ) : ℚ)) : ℝ) := by
    push_cast; rfl
  have hN0 : ((F.1 ^ 2 * M : ℤ) : ℝ) ≠ 0 := by exact_mod_cast mul_ne_zero (pow_ne_zero 2 hF0) hM0
  have mem : ∀ (g : UnitBox.Z3) (l : Fin 3), Mem (sR P Q A g l) (rnd A.p (sigI g (A.lo l) (A.hi l))) :=
    fun g l => mem_rnd A.p (mem_sigI g (hroot l).1 (hroot l).2.1)
  exact real_case (hc i) (mem phi i) (mem phi (oj i)) (mem phi (ok i)) (mem g0 (oj i))
    (mem g0 (ok i)) (mem e1 (oj i)) (mem e1 (ok i)) (mem e2 (oj i)) (mem e2 (ok i)) (hmat i)
    hs hN hN0 (hg i) (hg (oj i)) (hg (ok i)) hprod (hi _ (Finset.mem_univ _))
    (hi _ (Finset.mem_univ _)) hbR (hγ (oj i)) (hγ (ok i))

end PerfectPower.AnalyticBridge
