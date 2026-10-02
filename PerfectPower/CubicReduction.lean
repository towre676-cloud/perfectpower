import Batteries.Tactic.Lint.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Reduction of binary cubic forms of negative discriminant

Let `F = a X³ + B X²Y + C XY² + d Y³` have discriminant `D < 0`.  Over `ℝ`, with a real root `ρ`
(`a ≠ 0`), `F = (X − ρY) Q₂` with `Q₂ = aX² + βXY + γY²`, and `D = −δ R²` with `δ = 4aγ − β² > 0`,
`R = Q₂(ρ, 1)` (`disc_factor`).  The quadratic form
`q = (X − ρY)²/R² + 2|Q₂|/(|R| δ)` is positive definite with `det q = 3/|D|`, and
`q(v)³ ≥ 27 F(v)²/|D|²` (`(x₁ + 2x₂)³ − 27x₁x₂² = (x₁ − x₂)²(x₁ + 8x₂)`).  A Gauss-reduced basis
`v₁, v₂` of `ℤ²` for `q` then bounds `F(v₁)`, `F(v₂)`, `F(v₁ ± v₂)`: the coefficients of `F` in that
basis.  No complex numbers are needed.
-/

namespace PerfectPower.CubicReduction

noncomputable section

open Real

/-- A real cubic polynomial with nonzero leading coefficient has a real root. -/
@[nolint unusedHavesSuffices]
theorem cubic_root (a B C d : ℝ) (ha : a ≠ 0) : ∃ ρ : ℝ, a * ρ ^ 3 + B * ρ ^ 2 + C * ρ + d = 0 := by
  -- reduce to a > 0
  wlog hpos : 0 < a generalizing a B C d
  · obtain ⟨ρ, hρ⟩ := this (-a) (-B) (-C) (-d) (neg_ne_zero.mpr ha) (by
      rcases lt_or_gt_of_ne ha with h | h
      · linarith
      · exact absurd h hpos)
    exact ⟨ρ, by linarith⟩
  set M : ℝ := 1 + (|B| + |C| + |d|) / a with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ (|B| + |C| + |d|) / a := by positivity
    rw [hM]; linarith
  have haM : a * M = a + (|B| + |C| + |d|) := by
    rw [hM]; field_simp
  let f : ℝ → ℝ := fun x => a * x ^ 3 + B * x ^ 2 + C * x + d
  have hf : Continuous f := by continuity
  -- |B x² + C x + d| ≤ (|B| + |C| + |d|) M² for |x| ≤ M, M ≥ 1
  have key : ∀ x : ℝ, |x| = M → |B * x ^ 2 + C * x + d| < a * M ^ 3 := by
    intro x hx
    have h1 : |B * x ^ 2 + C * x + d| ≤ (|B| + |C| + |d|) * M ^ 2 := by
      calc |B * x ^ 2 + C * x + d| ≤ |B * x ^ 2| + |C * x| + |d| := abs_add_three _ _ _
        _ = |B| * M ^ 2 + |C| * M + |d| := by rw [abs_mul, abs_mul, abs_pow, hx]
        _ ≤ |B| * M ^ 2 + |C| * M ^ 2 + |d| * M ^ 2 := by
          have h1 : M ≤ M ^ 2 := by nlinarith
          have h2 : 1 ≤ M ^ 2 := by nlinarith
          have := abs_nonneg C
          have := abs_nonneg d
          nlinarith
        _ = (|B| + |C| + |d|) * M ^ 2 := by ring
    have h2 : (|B| + |C| + |d|) * M ^ 2 < a * M ^ 3 := by
      have : a * M ^ 3 = (a + (|B| + |C| + |d|)) * M ^ 2 := by rw [← haM]; ring
      rw [this]
      have : 0 < M ^ 2 := by positivity
      nlinarith
    linarith
  have hfM : 0 < f M := by
    have := key M (abs_of_pos (by linarith))
    simp only [f]
    have := (abs_lt.mp this).1
    nlinarith
  have hfm : f (-M) < 0 := by
    have := key (-M) (by rw [abs_neg]; exact abs_of_pos (by linarith))
    simp only [f]
    have := (abs_lt.mp this).2
    nlinarith
  obtain ⟨ρ, -, hρ⟩ := intermediate_value_Icc (by linarith : -M ≤ M) hf.continuousOn ⟨hfm.le, hfM.le⟩
  exact ⟨ρ, hρ⟩

/-- `a x³ + B x²y + C xy² + d y³` over `ℝ`. -/
def ev4 (a B C d x y : ℝ) : ℝ := a * x ^ 3 + B * x ^ 2 * y + C * x * y ^ 2 + d * y ^ 3

/-- The discriminant of `a X³ + B X²Y + C XY² + d Y³`. -/
def disc4 (a B C d : ℝ) : ℝ :=
  B ^ 2 * C ^ 2 - 4 * a * C ^ 3 - 4 * B ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * B * C * d

theorem factor {a B C d ρ : ℝ} (hρ : a * ρ ^ 3 + B * ρ ^ 2 + C * ρ + d = 0) (x y : ℝ) :
    ev4 a B C d x y = (x - ρ * y) * (a * x ^ 2 + (B + a * ρ) * x * y + (C + (B + a * ρ) * ρ) * y ^ 2) := by
  have hd : d = -(C + (B + a * ρ) * ρ) * ρ := by linear_combination hρ
  simp only [ev4]; rw [hd]; ring

theorem disc_factor {a B C d ρ : ℝ} (hρ : a * ρ ^ 3 + B * ρ ^ 2 + C * ρ + d = 0) :
    disc4 a B C d = -(4 * a * (C + (B + a * ρ) * ρ) - (B + a * ρ) ^ 2) *
      (a * ρ ^ 2 + (B + a * ρ) * ρ + (C + (B + a * ρ) * ρ)) ^ 2 := by
  have hd : d = -(C + (B + a * ρ) * ρ) * ρ := by linear_combination hρ
  simp only [disc4]; rw [hd]; ring

/-- **The AM-GM step**: `(x₁ + 2x₂)³ ≥ 27 x₁ x₂²` for `x₁, x₂ ≥ 0`. -/
@[nolint unusedHavesSuffices]
theorem amgm (x₁ x₂ : ℝ) (h1 : 0 ≤ x₁) (h2 : 0 ≤ x₂) : 27 * x₁ * x₂ ^ 2 ≤ (x₁ + 2 * x₂) ^ 3 := by
  have : (x₁ + 2 * x₂) ^ 3 - 27 * x₁ * x₂ ^ 2 = (x₁ - x₂) ^ 2 * (x₁ + 8 * x₂) := by ring
  nlinarith [sq_nonneg (x₁ - x₂), mul_nonneg (sq_nonneg (x₁ - x₂)) (by linarith : 0 ≤ x₁ + 8 * x₂)]

/-- The covariant quadratic form `q = (X − ρY)²/R² + 2Q₂/(Rδ)`, as coefficients `(A, B, C)`. -/
noncomputable def qA (a ρ β γ : ℝ) : ℝ :=
  1 / (a * ρ ^ 2 + β * ρ + γ) ^ 2 + 2 * a / ((a * ρ ^ 2 + β * ρ + γ) * (4 * a * γ - β ^ 2))
/-- The middle coefficient of `q`. -/
noncomputable def qB (a ρ β γ : ℝ) : ℝ :=
  -2 * ρ / (a * ρ ^ 2 + β * ρ + γ) ^ 2 + 2 * β / ((a * ρ ^ 2 + β * ρ + γ) * (4 * a * γ - β ^ 2))
/-- The last coefficient of `q`. -/
noncomputable def qC (a ρ β γ : ℝ) : ℝ :=
  ρ ^ 2 / (a * ρ ^ 2 + β * ρ + γ) ^ 2 + 2 * γ / ((a * ρ ^ 2 + β * ρ + γ) * (4 * a * γ - β ^ 2))

/-- The value of `q`. -/
def qv (A B C x y : ℝ) : ℝ := A * x ^ 2 + B * x * y + C * y ^ 2

theorem q_eq (a ρ β γ x y : ℝ) (hR : a * ρ ^ 2 + β * ρ + γ ≠ 0) (hδ : 4 * a * γ - β ^ 2 ≠ 0) :
    qv (qA a ρ β γ) (qB a ρ β γ) (qC a ρ β γ) x y =
      (x - ρ * y) ^ 2 / (a * ρ ^ 2 + β * ρ + γ) ^ 2 +
        2 * (a * x ^ 2 + β * x * y + γ * y ^ 2) / ((a * ρ ^ 2 + β * ρ + γ) * (4 * a * γ - β ^ 2)) := by
  simp only [qv, qA, qB, qC]
  field_simp
  ring

/-- **`det q = 3/|D|`**: `4AC − B² = 12/(R²δ)`. -/
theorem q_det (a ρ β γ : ℝ) (hR : a * ρ ^ 2 + β * ρ + γ ≠ 0) (hδ : 4 * a * γ - β ^ 2 ≠ 0) :
    4 * qA a ρ β γ * qC a ρ β γ - qB a ρ β γ ^ 2 =
      12 / ((a * ρ ^ 2 + β * ρ + γ) ^ 2 * (4 * a * γ - β ^ 2)) := by
  simp only [qA, qB, qC]
  field_simp
  ring

/-- **The value bound** `27 F(v)² ≤ D² q(v)³`, with the sign facts it needs. -/
@[nolint unusedHavesSuffices]
theorem value_bound {a B C d ρ : ℝ} (hρ : a * ρ ^ 3 + B * ρ ^ 2 + C * ρ + d = 0)
    (hD : disc4 a B C d < 0) (x y : ℝ) :
    27 * ev4 a B C d x y ^ 2 ≤ disc4 a B C d ^ 2 *
      qv (qA a ρ (B + a * ρ) (C + (B + a * ρ) * ρ)) (qB a ρ (B + a * ρ) (C + (B + a * ρ) * ρ))
        (qC a ρ (B + a * ρ) (C + (B + a * ρ) * ρ)) x y ^ 3 := by
  set β := B + a * ρ with hβ
  set γ := C + β * ρ with hγ
  set R := a * ρ ^ 2 + β * ρ + γ with hRdef
  set δ := 4 * a * γ - β ^ 2 with hδdef
  have hdisc : disc4 a B C d = -δ * R ^ 2 := by rw [disc_factor hρ]
  have hRδ : 0 < δ * R ^ 2 := by linarith
  have hR : R ≠ 0 := by
    intro h0; rw [h0] at hRδ; simp at hRδ
  have hR2 : 0 < R ^ 2 := by positivity
  have hδ : 0 < δ := by
    by_contra hc; push_neg at hc; nlinarith
  have haR : 0 < a * R := by
    have : 4 * a * R = (2 * a * ρ + β) ^ 2 + δ := by simp only [hRdef, hδdef]; ring
    nlinarith [sq_nonneg (2 * a * ρ + β)]
  set Q2 := a * x ^ 2 + β * x * y + γ * y ^ 2 with hQ2
  have haQ : 0 ≤ a * Q2 := by
    have : 4 * a * Q2 = (2 * a * x + β * y) ^ 2 + δ * y ^ 2 := by simp only [hQ2, hδdef]; ring
    nlinarith [sq_nonneg (2 * a * x + β * y), sq_nonneg y]
  have hQR : 0 ≤ Q2 * R := by
    have : 0 ≤ (a * Q2) * (a * R) := mul_nonneg haQ haR.le
    have ha2 : 0 < a ^ 2 := by
      have : a ≠ 0 := by rintro rfl; simp at haR
      positivity
    nlinarith
  set x1 := (x - ρ * y) ^ 2 / R ^ 2 with hx1
  set x2 := Q2 / (R * δ) with hx2
  have h1 : 0 ≤ x1 := by positivity
  have h2 : 0 ≤ x2 := by
    rw [hx2, show Q2 / (R * δ) = (Q2 * R) / (R ^ 2 * δ) by field_simp; ring]
    positivity
  have hq : qv (qA a ρ β γ) (qB a ρ β γ) (qC a ρ β γ) x y = x1 + 2 * x2 := by
    rw [q_eq a ρ β γ x y hR hδ.ne', hx1, hx2]; ring
  have hF : ev4 a B C d x y = (x - ρ * y) * Q2 := by rw [factor hρ]
  rw [hq, hF, hdisc]
  have hAM := amgm x1 x2 h1 h2
  have hprod : x1 * x2 ^ 2 = ((x - ρ * y) * Q2) ^ 2 / (δ * R ^ 2) ^ 2 := by
    rw [hx1, hx2]; field_simp; ring
  have : 27 * ((x - ρ * y) * Q2) ^ 2 = (δ * R ^ 2) ^ 2 * (27 * x1 * x2 ^ 2) := by
    rw [mul_assoc 27 x1, hprod]; field_simp
  rw [this, show (-δ * R ^ 2) ^ 2 = (δ * R ^ 2) ^ 2 by ring]
  exact mul_le_mul_of_nonneg_left hAM (by positivity)

lemma q_lower_y (A B C x y : ℝ) :
    (4 * A * C - B ^ 2) * y ^ 2 ≤ 4 * A * qv A B C x y := by
  have : 4 * A * qv A B C x y = (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 := by
    simp only [qv]; ring
  nlinarith [sq_nonneg (2 * A * x + B * y)]

lemma q_lower_x (A B C x y : ℝ) :
    (4 * A * C - B ^ 2) * x ^ 2 ≤ 4 * C * qv A B C x y := by
  have : 4 * C * qv A B C x y = (B * x + 2 * C * y) ^ 2 + (4 * A * C - B ^ 2) * x ^ 2 := by
    simp only [qv]; ring
  nlinarith [sq_nonneg (B * x + 2 * C * y)]

@[nolint unusedHavesSuffices]
lemma q_pos {A B C : ℝ} (hA : 0 < A) (hΔ : 0 < 4 * A * C - B ^ 2) {x y : ℤ} (h : (x, y) ≠ (0, 0)) :
    0 < qv A B C x y := by
  have e : 4 * A * qv A B C x y = (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * (y : ℝ) ^ 2 := by
    simp only [qv]; ring
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := by rintro rfl; exact h rfl
    have : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    simp only [qv, Int.cast_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    positivity
  · have : (0 : ℝ) < (y : ℝ) ^ 2 := by
      have : (y : ℝ) ≠ 0 := by exact_mod_cast hy
      positivity
    nlinarith [sq_nonneg (2 * A * x + B * y), mul_pos hΔ this]

lemma int_abs_le_sq (x : ℤ) : |x| ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · have : 1 ≤ |x| := Int.one_le_abs h
    nlinarith [abs_mul_abs_self x, sq_abs x]

/-- **Gauss reduction** over `ℤ²` for a real positive definite form: a basis `v₁, v₂` (`det = 1`)
with `q(v₁) ≤ q(v₂) ≤ q(v₂ ± v₁)`. -/
@[nolint unusedHavesSuffices]
theorem gauss_reduce {A B C : ℝ} (hA : 0 < A) (hΔ : 0 < 4 * A * C - B ^ 2) :
    ∃ x1 y1 x2 y2 : ℤ, x1 * y2 - x2 * y1 = 1 ∧ 0 < qv A B C x1 y1 ∧
      qv A B C x1 y1 ≤ qv A B C x2 y2 ∧ qv A B C x2 y2 ≤ qv A B C (x2 + x1) (y2 + y1) ∧
      qv A B C x2 y2 ≤ qv A B C (x2 - x1) (y2 - y1) := by
  have hC : 0 < C := by nlinarith [sq_nonneg B]
  set Δ := 4 * A * C - B ^ 2 with hΔdef
  -- a finite box containing every nonzero vector with q ≤ A = q(1, 0)
  set N : ℕ := ⌈4 * C * A / Δ + 4 * A * A / Δ⌉₊ with hN
  have hbox : ∀ x y : ℤ, qv A B C x y ≤ A → |x| ≤ N ∧ |y| ≤ N := by
    intro x y hq
    have hx := q_lower_x A B C (x : ℝ) (y : ℝ)
    have hy := q_lower_y A B C (x : ℝ) (y : ℝ)
    have hx2 : ((x : ℝ)) ^ 2 ≤ 4 * C * A / Δ := by
      rw [le_div_iff₀ hΔ]; nlinarith
    have hy2 : ((y : ℝ)) ^ 2 ≤ 4 * A * A / Δ := by
      rw [le_div_iff₀ hΔ]; nlinarith
    have h1 : (4 * C * A / Δ + 4 * A * A / Δ) ≤ (N : ℝ) := Nat.le_ceil _
    have p1 : 0 ≤ 4 * C * A / Δ := by positivity
    have p2 : 0 ≤ 4 * A * A / Δ := by positivity
    constructor
    · have : ((x ^ 2 : ℤ) : ℝ) ≤ N := by push_cast; linarith
      have := int_abs_le_sq x
      exact_mod_cast (show ((|x| : ℤ) : ℝ) ≤ N by
        calc ((|x| : ℤ) : ℝ) ≤ ((x ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
          _ ≤ N := by assumption)
    · have : ((y ^ 2 : ℤ) : ℝ) ≤ N := by push_cast; linarith
      have := int_abs_le_sq y
      exact_mod_cast (show ((|y| : ℤ) : ℝ) ≤ N by
        calc ((|y| : ℤ) : ℝ) ≤ ((y ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
          _ ≤ N := by assumption)
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ 4 * C * A / Δ := by
      rw [le_div_iff₀ hΔ]; nlinarith [sq_nonneg B]
    have h2 : 0 ≤ 4 * A * A / Δ := by positivity
    have : (1 : ℝ) ≤ N := le_trans (by linarith) (Nat.le_ceil _)
    exact_mod_cast this
  set S : Finset (ℤ × ℤ) := ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N)).filter (· ≠ (0, 0))
  have h10 : ((1 : ℤ), (0 : ℤ)) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by simp⟩
  obtain ⟨v, hvS, hvmin⟩ := Finset.exists_min_image S (fun w : ℤ × ℤ => qv A B C w.1 w.2) ⟨_, h10⟩
  have hq10 : qv A B C ((1 : ℤ) : ℝ) ((0 : ℤ) : ℝ) = A := by simp [qv]
  -- v is a global minimum over nonzero vectors
  have hglob : ∀ w : ℤ × ℤ, w ≠ (0, 0) → qv A B C v.1 v.2 ≤ qv A B C w.1 w.2 := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact hvmin w hwS
    · rcases le_or_lt (qv A B C v.1 v.2) (qv A B C w.1 w.2) with hle' | hlt
      · exact hle'
      exfalso
      have hle : qv A B C w.1 w.2 ≤ A := by
        have := hvmin _ h10; simp only at this; rw [hq10] at this; linarith
      obtain ⟨hx, hy⟩ := hbox w.1 w.2 hle
      apply hwS
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨abs_le.mp hx, abs_le.mp hy⟩, hw⟩
  have hv0 : v ≠ (0, 0) := (Finset.mem_filter.mp hvS).2
  obtain ⟨x1, y1⟩ := v
  have hq1 : 0 < qv A B C x1 y1 := q_pos hA hΔ hv0
  -- v is primitive
  have hprim : Int.gcd x1 y1 = 1 := by
    by_contra hg
    set g := Int.gcd x1 y1 with hgdef
    have hg0 : g ≠ 0 := by
      intro h0
      rw [hgdef, Int.gcd_eq_zero_iff] at h0
      exact hv0 (by rw [h0.1, h0.2])
    have hg1 : g ≠ 1 := hg
    have hg2 : 2 ≤ g := by omega
    obtain ⟨x', hx'⟩ := Int.gcd_dvd_left x1 y1
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right x1 y1
    have hw0 : (x', y') ≠ (0, 0) := by
      intro h0; simp only [Prod.mk.injEq] at h0
      exact hv0 (by rw [hx', hy', h0.1, h0.2]; simp)
    have hmin := hglob (x', y') hw0
    have e1 : (x1 : ℝ) = (g : ℝ) * x' := by rw [hgdef]; exact_mod_cast hx'
    have e2 : (y1 : ℝ) = (g : ℝ) * y' := by rw [hgdef]; exact_mod_cast hy'
    have hscale : qv A B C x1 y1 = (g : ℝ) ^ 2 * qv A B C x' y' := by
      rw [e1, e2]; simp only [qv]; ring
    have hpos' : 0 < qv A B C x' y' := q_pos hA hΔ hw0
    have : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ g := by exact_mod_cast hg2
      nlinarith
    simp only at hmin
    nlinarith
  -- complete to a basis
  have hbez := Int.gcd_eq_gcd_ab x1 y1
  rw [hprim] at hbez
  set s0 := -Int.gcdB x1 y1
  set t0 := Int.gcdA x1 y1
  have hdet0 : x1 * t0 - s0 * y1 = 1 := by simp only [s0, t0]; push_cast at hbez; linarith
  set A1 := qv A B C x1 y1
  set L := 2 * A * x1 * s0 + B * (x1 * t0 + y1 * s0) + 2 * C * y1 * t0
  set n : ℤ := ⌊(1 : ℝ) / 2 - L / (2 * A1)⌋
  have hn1 : (n : ℝ) ≤ 1 / 2 - L / (2 * A1) := Int.floor_le _
  have hn2 : 1 / 2 - L / (2 * A1) < n + 1 := Int.lt_floor_add_one _
  have hL1 : L + 2 * n * A1 ≤ A1 := by
    have : (n : ℝ) * (2 * A1) ≤ (1 / 2 - L / (2 * A1)) * (2 * A1) := by nlinarith
    rw [show (1 / 2 - L / (2 * A1)) * (2 * A1) = A1 - L by field_simp] at this
    linarith
  have hL2 : -A1 ≤ L + 2 * n * A1 := by
    have : (1 / 2 - L / (2 * A1)) * (2 * A1) < ((n : ℝ) + 1) * (2 * A1) := by nlinarith
    rw [show (1 / 2 - L / (2 * A1)) * (2 * A1) = A1 - L by field_simp] at this
    linarith
  refine ⟨x1, y1, s0 + n * x1, t0 + n * y1, by linear_combination hdet0, hq1, ?_, ?_, ?_⟩
  · have hw : (s0 + n * x1, t0 + n * y1) ≠ ((0 : ℤ), (0 : ℤ)) := by
      intro h0; simp only [Prod.mk.injEq] at h0
      have : x1 * (t0 + n * y1) - (s0 + n * x1) * y1 = 1 := by linear_combination hdet0
      rw [h0.1, h0.2] at this; simp at this
    have := hglob _ hw
    simpa using this
  · have e : qv A B C (↑(s0 + n * x1) + ↑x1) (↑(t0 + n * y1) + ↑y1) - qv A B C ↑(s0 + n * x1) ↑(t0 + n * y1) =
        (L + 2 * n * A1) + A1 := by simp only [qv, A1, L]; push_cast; ring
    push_cast at e ⊢; linarith
  · have e : qv A B C (↑(s0 + n * x1) - ↑x1) (↑(t0 + n * y1) - ↑y1) - qv A B C ↑(s0 + n * x1) ↑(t0 + n * y1) =
        -(L + 2 * n * A1) + A1 := by simp only [qv, A1, L]; push_cast; ring
    push_cast at e ⊢; linarith

lemma det_transport (A B C : ℝ) (x1 y1 x2 y2 : ℝ) :
    4 * qv A B C x1 y1 * qv A B C x2 y2 -
      (qv A B C (x1 + x2) (y1 + y2) - qv A B C x1 y1 - qv A B C x2 y2) ^ 2 =
    (4 * A * C - B ^ 2) * (x1 * y2 - x2 * y1) ^ 2 := by
  simp only [qv]; ring

lemma parallelogram (A B C : ℝ) (x1 y1 x2 y2 : ℝ) :
    qv A B C (x2 - x1) (y2 - y1) =
      2 * qv A B C x1 y1 + 2 * qv A B C x2 y2 - qv A B C (x1 + x2) (y1 + y2) := by
  simp only [qv]; ring

/-- **The reduced basis.**  For `a ≠ 0` and `D < 0` there are `v₁, v₂` (`det = 1`) and reals
`s = q(v₁)`, `c = q(v₂)`, `b = q(v₁ + v₂) − s − c` with `|b| ≤ s ≤ c`, `(4sc − b²)|D| = 12`, and
`27 F(v)² ≤ D² q(v)³` at `v₁`, `v₂`, `v₁ + v₂`, `v₁ − v₂`. -/
@[nolint unusedHavesSuffices]
theorem reduce_box {a B C d : ℝ} (ha : a ≠ 0) (hD : disc4 a B C d < 0) :
    ∃ x1 y1 x2 y2 : ℤ, x1 * y2 - x2 * y1 = 1 ∧ ∃ s b c : ℝ, 0 < s ∧ |b| ≤ s ∧ s ≤ c ∧
      (4 * s * c - b ^ 2) * |disc4 a B C d| = 12 ∧
      27 * ev4 a B C d x1 y1 ^ 2 ≤ disc4 a B C d ^ 2 * s ^ 3 ∧
      27 * ev4 a B C d x2 y2 ^ 2 ≤ disc4 a B C d ^ 2 * c ^ 3 ∧
      27 * ev4 a B C d (x1 + x2) (y1 + y2) ^ 2 ≤ disc4 a B C d ^ 2 * (s + b + c) ^ 3 ∧
      27 * ev4 a B C d (x1 - x2) (y1 - y2) ^ 2 ≤ disc4 a B C d ^ 2 * (s - b + c) ^ 3 := by
  obtain ⟨ρ, hρ⟩ := cubic_root a B C d ha
  set β := B + a * ρ with hβ
  set γ := C + β * ρ with hγ
  set R := a * ρ ^ 2 + β * ρ + γ with hRdef
  set δ := 4 * a * γ - β ^ 2 with hδdef
  have hdisc : disc4 a B C d = -δ * R ^ 2 := by rw [disc_factor hρ]
  have hRδ : 0 < δ * R ^ 2 := by linarith
  have hR : R ≠ 0 := by intro h0; rw [h0] at hRδ; simp at hRδ
  have hδ : 0 < δ := by by_contra hc; push_neg at hc; nlinarith [sq_nonneg R]
  set qa := qA a ρ β γ
  set qb := qB a ρ β γ
  set qc := qC a ρ β γ
  have hdet : 4 * qa * qc - qb ^ 2 = 12 / (R ^ 2 * δ) := q_det a ρ β γ hR hδ.ne'
  have hdetpos : 0 < 4 * qa * qc - qb ^ 2 := by rw [hdet]; positivity
  have hqa : 0 < qa := by
    have e := q_eq a ρ β γ 1 0 hR hδ.ne'
    have hv : qv qa qb qc 1 0 = qa := by simp [qv]
    rw [hv] at e
    rw [e]
    have hQR : 0 ≤ a / (R * δ) := by
      have haR : 0 < a * R := by
        have : 4 * a * R = (2 * a * ρ + β) ^ 2 + δ := by simp only [hRdef, hδdef]; ring
        nlinarith [sq_nonneg (2 * a * ρ + β)]
      rw [show a / (R * δ) = (a * R) / (R ^ 2 * δ) by field_simp; ring]
      positivity
    have : (1 - ρ * 0) ^ 2 / R ^ 2 > 0 := by simp; positivity
    have h2 : 0 ≤ 2 * (a * 1 ^ 2 + β * 1 * 0 + γ * 0 ^ 2) / (R * δ) := by
      simp only [one_pow, mul_one, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      rw [mul_div_assoc]; positivity
    linarith
  obtain ⟨x1, y1, x2, y2, hdet1, hq1, h12, hp, hm⟩ := gauss_reduce hqa hdetpos
  set sv := qv qa qb qc x1 y1
  set cv := qv qa qb qc x2 y2
  set bv := qv qa qb qc ((x1 : ℝ) + x2) ((y1 : ℝ) + y2) - sv - cv
  have hpar := parallelogram qa qb qc x1 y1 x2 y2
  refine ⟨x1, y1, x2, y2, hdet1, sv, bv, cv, hq1, ?_, h12, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor
    · have e : qv qa qb qc ((x2 : ℝ) + x1) ((y2 : ℝ) + y1) = qv qa qb qc ((x1 : ℝ) + x2) ((y1 : ℝ) + y2) := by
        rw [add_comm (x2 : ℝ), add_comm (y2 : ℝ)]
      simp only [bv]; rw [e] at hp; linarith
    · simp only [bv]; rw [hpar] at hm; linarith
  · have e := det_transport qa qb qc x1 y1 x2 y2
    have hd1 : ((x1 : ℝ) * y2 - x2 * y1) = 1 := by exact_mod_cast hdet1
    rw [hd1, one_pow, mul_one, hdet] at e
    have : 4 * sv * cv - bv ^ 2 = 12 / (R ^ 2 * δ) := by simp only [sv, cv, bv]; linarith
    rw [this, hdisc, abs_of_neg (by nlinarith), show -(-δ * R ^ 2) = R ^ 2 * δ by ring]
    field_simp
  · have := value_bound hρ hD x1 y1; exact this
  · have := value_bound hρ hD x2 y2; exact this
  · have := value_bound hρ hD ((x1 : ℝ) + x2) ((y1 : ℝ) + y2)
    have e : sv + bv + cv = qv qa qb qc ((x1 : ℝ) + x2) ((y1 : ℝ) + y2) := by simp only [bv]; ring
    rw [e]; exact this
  · have := value_bound hρ hD ((x1 : ℝ) - x2) ((y1 : ℝ) - y2)
    have e : sv - bv + cv = qv qa qb qc ((x1 : ℝ) - x2) ((y1 : ℝ) - y2) := by
      have : qv qa qb qc ((x1 : ℝ) - x2) ((y1 : ℝ) - y2) = qv qa qb qc ((x2 : ℝ) - x1) ((y2 : ℝ) - y1) := by
        simp only [qv]; ring
      rw [this, hpar]; simp only [bv]; ring
    rw [e]; exact this

/-- **From the reduced basis to integer bounds**, with explicit parameters (checked per `k` by
`norm_num`): `X₁ = F(v₁)` is `0` or `|X₁| ≤ amax`, and then `|X₂|, |X₃|, |X₄| ≤ M`. -/
@[nolint unusedHavesSuffices]
theorem int_bounds {Dabs s b c s0 s1 H M amax : ℝ} {X1 X2 X3 X4 : ℤ} (hD : 0 < Dabs)
    (hs : 0 < s) (hb : |b| ≤ s) (hsc : s ≤ c) (hdet : (4 * s * c - b ^ 2) * Dabs = 12)
    (h1 : 27 * (X1 : ℝ) ^ 2 ≤ Dabs ^ 2 * s ^ 3) (h2 : 27 * (X2 : ℝ) ^ 2 ≤ Dabs ^ 2 * c ^ 3)
    (h3 : 27 * (X3 : ℝ) ^ 2 ≤ Dabs ^ 2 * (s + b + c) ^ 3) (h4 : 27 * (X4 : ℝ) ^ 2 ≤ Dabs ^ 2 * (s - b + c) ^ 3)
    (hs0 : 0 < s0) (hp0 : Dabs ^ 2 * s0 ^ 3 ≤ 27) (hp1 : 4 ≤ Dabs * s1 ^ 2) (hs01 : s0 ≤ s1)
    (hH0 : 9 * s0 ^ 2 * Dabs + 12 ≤ 4 * H * s0 * Dabs) (hH1 : 9 * s1 ^ 2 * Dabs + 12 ≤ 4 * H * s1 * Dabs)
    (hM : Dabs ^ 2 * H ^ 3 ≤ 27 * M ^ 2) (hA : Dabs ^ 2 * s1 ^ 3 ≤ 27 * amax ^ 2) (hM0 : 0 ≤ M) (hA0 : 0 ≤ amax) :
    X1 = 0 ∨ (|(X1 : ℝ)| ≤ amax ∧ |(X2 : ℝ)| ≤ M ∧ |(X3 : ℝ)| ≤ M ∧ |(X4 : ℝ)| ≤ M) := by
  rcases eq_or_ne X1 0 with h0 | h0
  · exact Or.inl h0
  right
  have hb2 : b ^ 2 ≤ s ^ 2 := by rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hs1pos : 0 < s1 := lt_of_lt_of_le hs0 hs01
  -- s ≤ s1
  have e1 : s * s ≤ s * c := mul_le_mul_of_nonneg_left hsc hs.le
  have e2 : 3 * s ^ 2 ≤ 4 * s * c - b ^ 2 := by
    have : s ^ 2 = s * s := by ring
    linarith
  have e3 : 3 * s ^ 2 * Dabs ≤ 12 := by
    have := mul_le_mul_of_nonneg_right e2 hD.le
    have e : (4 * s * c - b ^ 2) * Dabs = 12 := hdet
    linarith
  have hs1 : s ≤ s1 := by
    have : s ^ 2 ≤ s1 ^ 2 := by
      have h' : s ^ 2 * Dabs ≤ s1 ^ 2 * Dabs := by linarith
      exact le_of_mul_le_mul_right h' hD
    exact (pow_le_pow_iff_left₀ hs.le hs1pos.le (by norm_num : (2 : ℕ) ≠ 0)).mp this
  -- s ≥ s0
  have hX1 : (1 : ℝ) ≤ (X1 : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ X1 ^ 2 := by
      have := Int.one_le_abs h0
      nlinarith [sq_abs X1]
    exact_mod_cast this
  have hs0' : s0 ≤ s := by
    have h' : s0 ^ 3 * Dabs ^ 2 ≤ s ^ 3 * Dabs ^ 2 := by linarith
    have : s0 ^ 3 ≤ s ^ 3 := le_of_mul_le_mul_right h' (by positivity)
    exact (pow_le_pow_iff_left₀ hs0.le hs.le (by norm_num : (3 : ℕ) ≠ 0)).mp this
  -- 4 s c D ≤ 12 + s² D
  have hc : 4 * s * c * Dabs ≤ 12 + s ^ 2 * Dabs := by
    have e : 4 * s * c * Dabs = 12 + b ^ 2 * Dabs := by linear_combination hdet
    have := mul_le_mul_of_nonneg_right hb2 hD.le; linarith
  -- p(s) = 9 s² D + 12 − 4 H s D ≤ 0 on [s0, s1] (convexity)
  have hp : 9 * s ^ 2 * Dabs + 12 ≤ 4 * H * s * Dabs := by
    rcases eq_or_lt_of_le hs01 with heq | hlt
    · have : s = s0 := le_antisymm (heq ▸ hs1) hs0'
      rw [this]; exact hH0
    · have key : (9 * s ^ 2 * Dabs + 12 - 4 * H * s * Dabs) * (s1 - s0) =
          (9 * s0 ^ 2 * Dabs + 12 - 4 * H * s0 * Dabs) * (s1 - s) +
          (9 * s1 ^ 2 * Dabs + 12 - 4 * H * s1 * Dabs) * (s - s0) +
          9 * Dabs * (s - s0) * (s - s1) * (s1 - s0) := by ring
      have t1 : (9 * s0 ^ 2 * Dabs + 12 - 4 * H * s0 * Dabs) * (s1 - s) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have t2 : (9 * s1 ^ 2 * Dabs + 12 - 4 * H * s1 * Dabs) * (s - s0) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have t3 : 9 * Dabs * (s - s0) * (s - s1) * (s1 - s0) ≤ 0 := by
        have : 0 ≤ 9 * Dabs * (s - s0) := mul_nonneg (by positivity) (by linarith)
        have : 9 * Dabs * (s - s0) * (s - s1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this (by linarith)
        exact mul_nonpos_of_nonpos_of_nonneg this (by linarith)
      have : (9 * s ^ 2 * Dabs + 12 - 4 * H * s * Dabs) * (s1 - s0) ≤ 0 := by linarith
      have := nonpos_of_mul_nonpos_left this (by linarith : 0 < s1 - s0)
      linarith
  have hq : 2 * s + c ≤ H := by
    have h' : (2 * s + c) * (4 * s * Dabs) ≤ H * (4 * s * Dabs) := by
      have : (2 * s + c) * (4 * s * Dabs) = 8 * s ^ 2 * Dabs + 4 * s * c * Dabs := by ring
      have : H * (4 * s * Dabs) = 4 * H * s * Dabs := by ring
      linarith
    exact le_of_mul_le_mul_right h' (by positivity)
  have hcpos : 0 < c := by linarith
  have hb' := abs_le.mp hb
  have bound : ∀ X : ℤ, ∀ q : ℝ, 0 ≤ q → q ≤ H → 27 * (X : ℝ) ^ 2 ≤ Dabs ^ 2 * q ^ 3 → |(X : ℝ)| ≤ M := by
    intro X q hq0 hqH hX
    have hq3 : q ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ hq0 hqH 3
    have : 27 * (X : ℝ) ^ 2 ≤ 27 * M ^ 2 := by
      calc 27 * (X : ℝ) ^ 2 ≤ Dabs ^ 2 * q ^ 3 := hX
        _ ≤ Dabs ^ 2 * H ^ 3 := by gcongr
        _ ≤ 27 * M ^ 2 := hM
    exact abs_le_of_sq_le_sq' (by linarith) hM0 |> fun h => abs_le.mpr ⟨h.1, h.2⟩
  refine ⟨?_, bound X2 c hcpos.le (by linarith) h2, bound X3 (s + b + c) (by linarith) (by linarith) h3,
    bound X4 (s - b + c) (by linarith) (by linarith) h4⟩
  have hs3 : s ^ 3 ≤ s1 ^ 3 := pow_le_pow_left₀ hs.le hs1 3
  have : 27 * (X1 : ℝ) ^ 2 ≤ 27 * amax ^ 2 := by
    calc 27 * (X1 : ℝ) ^ 2 ≤ Dabs ^ 2 * s ^ 3 := h1
      _ ≤ Dabs ^ 2 * s1 ^ 3 := by gcongr
      _ ≤ 27 * amax ^ 2 := hA
  exact abs_le_of_sq_le_sq' (by linarith) hA0 |> fun h => abs_le.mpr ⟨h.1, h.2⟩

end

end PerfectPower.CubicReduction
