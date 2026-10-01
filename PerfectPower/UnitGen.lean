import PerfectPower.UnitPremises
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# Unit generation from a finite fundamental-domain check

`UnitPremises.UnitGen P Q ε₁ ε₁⁻¹ ε₂ ε₂⁻¹` says every unit of `ℤ[x]`, `x³ = Px + Q`, is
`±ε₁^a ε₂^b`.  Here it is **proved** from a finite certificate checked by evaluation
(`ugCheck`), for a cubic with three real roots.

1. **Embeddings.**  The three real roots `tᵢ` (from rational brackets with a sign change, by the
   intermediate value theorem) give ring maps `σᵢ(A, B, C) = A + B tᵢ + C tᵢ²` (`sig_mul`).
   The norm is `σ₁σ₂σ₃` (`nrm_eq`), and an element is determined by its three embeddings
   (Lagrange interpolation, `coords`, `sig_inj`).
2. **Logarithms.**  For a unit, `Lᵢ = log|σᵢ|` sums to zero.  The `2 × 2` matrix of `Lᵢ(ε_r)`,
   `i, r ∈ {1, 2}`, has nonzero determinant: each entry is enclosed by rationals through
   `n (1 − 1/s) ≤ log y ≤ n (s' − 1)` for `sⁿ ≤ y ≤ s'ⁿ`, with `y` enclosed from the brackets.
3. **Rounding.**  Any unit `u`, multiplied by `ε₁^{−k₁} ε₂^{−k₂}` with `kᵣ` the nearest integers
   to its log coordinates, gets `|Lᵢ| ≤ (|Lᵢ ε₁| + |Lᵢ ε₂|)/2`, hence
   `|σᵢ|² ≤ max(|σᵢε₁|, |σᵢε₁|⁻¹) · max(|σᵢε₂|, |σᵢε₂|⁻¹) ≤ Uᵢ²`.  No logarithm is evaluated here.
4. **The box.**  Lagrange interpolation and the bracket gaps bound the coordinates, so the reduced
   unit lies in a finite box; every element of norm `±1` there is listed (`unitBoxB`), and each
   listed one is checked to be `±ε₁^x ε₂^y` by evaluation.
-/

namespace PerfectPower.UnitGenProof

open PerfectPower UnitBox UnitPremises Real

/-! ### Embeddings -/

/-- The embedding `A + B t + C t²`. -/
def sig (t : ℝ) (g : Z3) : ℝ := g.1 + g.2.1 * t + g.2.2 * t ^ 2

lemma sig_mul {P Q : ℤ} {t : ℝ} (ht : t ^ 3 = P * t + Q) (x y : Z3) :
    sig t (mul P Q x y) = sig t x * sig t y := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp only [sig, mul]
  push_cast
  linear_combination (-((b : ℝ) * f + c * e) - (c : ℝ) * f * t) * ht

lemma sig_one (t : ℝ) : sig t (1, 0, 0) = 1 := by simp [sig]

lemma sig_neg (t : ℝ) (g : Z3) : sig t (neg g) = -sig t g := by
  obtain ⟨a, b, c⟩ := g
  simp only [sig, neg]
  push_cast
  ring

lemma sig_pow {P Q : ℤ} {t : ℝ} (ht : t ^ 3 = P * t + Q) (x : Z3) :
    ∀ n : ℕ, sig t (pow P Q x n) = sig t x ^ n
  | 0 => by simp [pow, sig_one]
  | n + 1 => by rw [pow, sig_mul ht, sig_pow ht x n, pow_succ]

lemma sig_zp {P Q : ℤ} {t : ℝ} (ht : t ^ 3 = P * t + Q) {x xinv : Z3} (hx : mul P Q x xinv = (1, 0, 0))
    (e : ℤ) : sig t (zp P Q x xinv e) = sig t x ^ e := by
  have hinv : sig t x * sig t xinv = 1 := by rw [← sig_mul ht, hx, sig_one]
  unfold zp
  split_ifs with h
  · rw [sig_pow ht]
    conv_rhs => rw [show e = ((e.toNat : ℕ) : ℤ) by omega]
    rw [zpow_natCast]
  · rw [sig_pow ht, eq_inv_of_mul_eq_one_right hinv, inv_pow]
    conv_rhs => rw [show e = -(((-e).toNat : ℕ) : ℤ) by omega]
    rw [zpow_neg, zpow_natCast]

/-! ### The three roots -/

/-- Three distinct roots of `X³ − PX − Q`. -/
structure Roots (P Q : ℤ) where
  /-- The first root. -/
  t1 : ℝ
  /-- The second root. -/
  t2 : ℝ
  /-- The third root. -/
  t3 : ℝ
  h1 : t1 ^ 3 = P * t1 + Q
  h2 : t2 ^ 3 = P * t2 + Q
  h3 : t3 ^ 3 = P * t3 + Q
  d12 : t1 ≠ t2
  d13 : t1 ≠ t3
  d23 : t2 ≠ t3

variable {P Q : ℤ}

lemma Roots.sym (R : Roots P Q) :
    R.t3 = -R.t1 - R.t2 ∧ (P : ℝ) = R.t1 ^ 2 + R.t1 * R.t2 + R.t2 ^ 2 ∧
      (Q : ℝ) = -(R.t1 * R.t2 * (R.t1 + R.t2)) := by
  obtain ⟨t1, t2, t3, h1, h2, h3, d12, d13, d23⟩ := R
  have s12 : (t1 - t2) * (t1 ^ 2 + t1 * t2 + t2 ^ 2 - P) = 0 := by linear_combination h1 - h2
  have s13 : (t1 - t3) * (t1 ^ 2 + t1 * t3 + t3 ^ 2 - P) = 0 := by linear_combination h1 - h3
  have e12 : t1 ^ 2 + t1 * t2 + t2 ^ 2 = P := by
    have := (mul_eq_zero.mp s12).resolve_left (sub_ne_zero.mpr d12); linarith
  have e13 : t1 ^ 2 + t1 * t3 + t3 ^ 2 = P := by
    have := (mul_eq_zero.mp s13).resolve_left (sub_ne_zero.mpr d13); linarith
  have hs : (t2 - t3) * (t1 + t2 + t3) = 0 := by linear_combination e12 - e13
  have h0 := (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr d23)
  refine ⟨by linarith, e12.symm, ?_⟩
  have : (Q : ℝ) = t1 ^ 3 - P * t1 := by linarith
  rw [this, ← e12]
  ring

/-- **The norm is the product of the embeddings.** -/
lemma Roots.nrm_eq (R : Roots P Q) (g : Z3) :
    (nrm P Q g : ℝ) = sig R.t1 g * sig R.t2 g * sig R.t3 g := by
  obtain ⟨h3, hP, hQ⟩ := R.sym
  obtain ⟨a, b, c⟩ := g
  simp only [nrm, sig]
  push_cast
  rw [h3, hP, hQ]
  ring

lemma Roots.nrm_mul (R : Roots P Q) (x y : Z3) : nrm P Q (mul P Q x y) = nrm P Q x * nrm P Q y := by
  have := R.nrm_eq (mul P Q x y)
  rw [sig_mul R.h1, sig_mul R.h2, sig_mul R.h3] at this
  have h := R.nrm_eq x
  have h' := R.nrm_eq y
  exact_mod_cast (show (nrm P Q (mul P Q x y) : ℝ) = nrm P Q x * nrm P Q y by rw [this, h, h']; ring)

/-- The denominators of Lagrange interpolation. -/
def Roots.D1 (R : Roots P Q) : ℝ := (R.t1 - R.t2) * (R.t1 - R.t3)
/-- The second Lagrange denominator. -/
def Roots.D2 (R : Roots P Q) : ℝ := (R.t2 - R.t1) * (R.t2 - R.t3)
/-- The third Lagrange denominator. -/
def Roots.D3 (R : Roots P Q) : ℝ := (R.t3 - R.t1) * (R.t3 - R.t2)

/-- **Lagrange interpolation**: the coordinates from the embeddings. -/
lemma Roots.coords (R : Roots P Q) (g : Z3) :
    (g.2.2 : ℝ) = sig R.t1 g / R.D1 + sig R.t2 g / R.D2 + sig R.t3 g / R.D3 ∧
    (g.2.1 : ℝ) = -((R.t2 + R.t3) * sig R.t1 g / R.D1 + (R.t1 + R.t3) * sig R.t2 g / R.D2 +
      (R.t1 + R.t2) * sig R.t3 g / R.D3) ∧
    (g.1 : ℝ) = R.t2 * R.t3 * sig R.t1 g / R.D1 + R.t1 * R.t3 * sig R.t2 g / R.D2 +
      R.t1 * R.t2 * sig R.t3 g / R.D3 := by
  obtain ⟨t1, t2, t3, -, -, -, d12, d13, d23⟩ := R
  obtain ⟨a, b, c⟩ := g
  have a12 : t1 - t2 ≠ 0 := sub_ne_zero.mpr d12
  have a13 : t1 - t3 ≠ 0 := sub_ne_zero.mpr d13
  have a23 : t2 - t3 ≠ 0 := sub_ne_zero.mpr d23
  have a21 : t2 - t1 ≠ 0 := sub_ne_zero.mpr d12.symm
  have a31 : t3 - t1 ≠ 0 := sub_ne_zero.mpr d13.symm
  have a32 : t3 - t2 ≠ 0 := sub_ne_zero.mpr d23.symm
  simp only [sig, Roots.D1, Roots.D2, Roots.D3]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **An element is determined by its embeddings.** -/
lemma Roots.sig_inj (R : Roots P Q) {x y : Z3} (h1 : sig R.t1 x = sig R.t1 y)
    (h2 : sig R.t2 x = sig R.t2 y) (h3 : sig R.t3 x = sig R.t3 y) : x = y := by
  obtain ⟨cx, bx, ax⟩ := R.coords x
  obtain ⟨cy, by', ay⟩ := R.coords y
  rw [h1, h2, h3] at cx bx ax
  have e1 : (x.1 : ℝ) = y.1 := by rw [ax, ay]
  have e2 : (x.2.1 : ℝ) = y.2.1 := by rw [bx, by']
  have e3 : (x.2.2 : ℝ) = y.2.2 := by rw [cx, cy]
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp only at e1 e2 e3
  simp only [Prod.mk.injEq]
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3⟩

/-! ### Units and logarithms -/

/-- A unit of `ℤ[x]`, with a witness inverse. -/
def IsUnit' (P Q : ℤ) (u : Z3) : Prop := ∃ v, mul P Q u v = (1, 0, 0)

lemma sig_ne_of_unit {u : Z3} (hu : IsUnit' P Q u) {t : ℝ} (ht : t ^ 3 = P * t + Q) :
    sig t u ≠ 0 := by
  obtain ⟨v, hv⟩ := hu
  intro h0
  have := sig_mul ht u v
  rw [hv, sig_one, h0, zero_mul] at this
  exact one_ne_zero this

lemma Roots.abs_prod (R : Roots P Q) {u : Z3} (hu : IsUnit' P Q u) :
    |sig R.t1 u * sig R.t2 u * sig R.t3 u| = 1 := by
  obtain ⟨v, hv⟩ := hu
  have h := R.nrm_mul u v
  rw [hv] at h
  have h1 : nrm P Q ((1, 0, 0) : Z3) = 1 := by simp [nrm]
  rw [h1] at h
  rw [← R.nrm_eq]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h.symm with h2 | h2 <;> rw [h2] <;> simp

lemma mul_swap4 (x y x' y' : Z3) :
    mul P Q (mul P Q x y) (mul P Q x' y') = mul P Q (mul P Q x x') (mul P Q y y') := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  obtain ⟨g, h, i⟩ := x'
  obtain ⟨j, k, l⟩ := y'
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma isUnit_mul {x y : Z3} (hx : IsUnit' P Q x) (hy : IsUnit' P Q y) : IsUnit' P Q (mul P Q x y) := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  refine ⟨mul P Q x' y', ?_⟩
  rw [mul_swap4, hx', hy']
  simp [mul]

lemma isUnit_zp {x xinv : Z3} (hx : mul P Q x xinv = (1, 0, 0)) (R : Roots P Q) (e : ℤ) :
    IsUnit' P Q (zp P Q x xinv e) := by
  refine ⟨zp P Q x xinv (-e), R.sig_inj ?_ ?_ ?_⟩ <;>
  · simp only [sig_mul R.h1, sig_mul R.h2, sig_mul R.h3, sig_one,
      sig_zp R.h1 hx, sig_zp R.h2 hx, sig_zp R.h3 hx]
    rw [← zpow_add₀ (sig_ne_of_unit ⟨xinv, hx⟩ (by first | exact R.h1 | exact R.h2 | exact R.h3)), add_neg_cancel,
      zpow_zero]

/-- `log |σ|`. -/
noncomputable def L (t : ℝ) (g : Z3) : ℝ := Real.log |sig t g|

lemma Roots.L_sum (R : Roots P Q) {u : Z3} (hu : IsUnit' P Q u) :
    L R.t1 u + L R.t2 u + L R.t3 u = 0 := by
  have n1 := sig_ne_of_unit hu R.h1
  have n2 := sig_ne_of_unit hu R.h2
  have n3 := sig_ne_of_unit hu R.h3
  simp only [L]
  rw [← Real.log_mul (abs_ne_zero.mpr n1) (abs_ne_zero.mpr n2),
    ← Real.log_mul (by positivity) (abs_ne_zero.mpr n3), ← abs_mul, ← abs_mul, R.abs_prod hu,
    Real.log_one]

lemma exp_abs_log {y : ℝ} (hy : 0 < y) : Real.exp |Real.log y| = max y y⁻¹ := by
  rcases le_or_lt 1 y with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h), Real.exp_log hy, max_eq_left]
    calc y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      _ ≤ y := h
  · have hl : Real.log y < 0 := Real.log_neg hy h
    rw [abs_of_neg hl, ← Real.log_inv, Real.exp_log (inv_pos.mpr hy), max_eq_right]
    calc y ≤ 1 := h.le
      _ ≤ y⁻¹ := one_le_inv₀ hy |>.mpr h.le

/-- **The rounding step**, over the reals. -/
lemma round_step (a11 a12 a21 a22 x1 x2 : ℝ) (hdet : a11 * a22 - a12 * a21 ≠ 0) :
    ∃ k1 k2 : ℤ, |x1 - k1 * a11 - k2 * a12| ≤ (|a11| + |a12|) / 2 ∧
      |x2 - k1 * a21 - k2 * a22| ≤ (|a21| + |a22|) / 2 ∧
      |(-x1 - x2) - k1 * (-a11 - a21) - k2 * (-a12 - a22)| ≤ (|-a11 - a21| + |-a12 - a22|) / 2 := by
  set d := a11 * a22 - a12 * a21
  set s1 := (x1 * a22 - x2 * a12) / d
  set s2 := (a11 * x2 - a21 * x1) / d
  have e1 : x1 = s1 * a11 + s2 * a12 := by simp only [s1, s2]; field_simp; ring
  have e2 : x2 = s1 * a21 + s2 * a22 := by simp only [s1, s2]; field_simp; ring
  refine ⟨⌊s1 + 1 / 2⌋, ⌊s2 + 1 / 2⌋, ?_⟩
  have r1 : |s1 - ⌊s1 + 1 / 2⌋| ≤ 1 / 2 := by
    have := Int.floor_le (s1 + 1 / 2)
    have := Int.lt_floor_add_one (s1 + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  have r2 : |s2 - ⌊s2 + 1 / 2⌋| ≤ 1 / 2 := by
    have := Int.floor_le (s2 + 1 / 2)
    have := Int.lt_floor_add_one (s2 + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  set k1 : ℝ := ((⌊s1 + 1 / 2⌋ : ℤ) : ℝ)
  set k2 : ℝ := ((⌊s2 + 1 / 2⌋ : ℤ) : ℝ)
  have key : ∀ b1 b2 : ℝ, |(s1 - k1) * b1 + (s2 - k2) * b2| ≤ (|b1| + |b2|) / 2 := by
    intro b1 b2
    calc |(s1 - k1) * b1 + (s2 - k2) * b2| ≤ |(s1 - k1) * b1| + |(s2 - k2) * b2| := abs_add_le _ _
      _ = |s1 - k1| * |b1| + |s2 - k2| * |b2| := by rw [abs_mul, abs_mul]
      _ ≤ 1 / 2 * |b1| + 1 / 2 * |b2| := by gcongr
      _ = (|b1| + |b2|) / 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · have := key a11 a12; rw [e1]; convert this using 2; ring
  · have := key a21 a22; rw [e2]; convert this using 2; ring
  · have := key (-a11 - a21) (-a12 - a22); rw [e1, e2]; convert this using 2; ring

lemma L_mul {t : ℝ} (ht : t ^ 3 = P * t + Q) {x y : Z3} (hx : sig t x ≠ 0) (hy : sig t y ≠ 0) :
    L t (mul P Q x y) = L t x + L t y := by
  simp only [L]
  rw [sig_mul ht, abs_mul, Real.log_mul (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hy)]

lemma L_zp {t : ℝ} (ht : t ^ 3 = P * t + Q) {x xinv : Z3} (hx : mul P Q x xinv = (1, 0, 0)) (k : ℤ) :
    L t (zp P Q x xinv k) = k * L t x := by
  simp only [L]
  rw [sig_zp ht hx, show |sig t x ^ k| = |sig t x| ^ k from map_zpow₀ (absHom (α := ℝ)) _ _,
    Real.log_zpow]

/-- **Every unit moves into the bounded region.**  For a unit `u` there are `k₁, k₂` such that
`u' = u ε₁^{−k₁} ε₂^{−k₂}` has `|σᵢ(u')|² ≤ max(|σᵢε₁|, |σᵢε₁|⁻¹) · max(|σᵢε₂|, |σᵢε₂|⁻¹)`. -/
lemma Roots.reduce_unit (R : Roots P Q) {e1 e1i e2 e2i : Z3} (h1 : mul P Q e1 e1i = (1, 0, 0))
    (h2 : mul P Q e2 e2i = (1, 0, 0))
    (hdet : L R.t1 e1 * L R.t2 e2 - L R.t1 e2 * L R.t2 e1 ≠ 0) {u : Z3} (hu : IsUnit' P Q u) :
    ∃ k1 k2 : ℤ, ∀ t ∈ ({R.t1, R.t2, R.t3} : Set ℝ),
      |sig t (mul P Q u (mul P Q (zp P Q e1 e1i (-k1)) (zp P Q e2 e2i (-k2))))| ^ 2 ≤
        max |sig t e1| |sig t e1|⁻¹ * max |sig t e2| |sig t e2|⁻¹ := by
  have u1 : IsUnit' P Q e1 := ⟨e1i, h1⟩
  have u2 : IsUnit' P Q e2 := ⟨e2i, h2⟩
  obtain ⟨k1, k2, b1, b2, b3⟩ := round_step (L R.t1 e1) (L R.t1 e2) (L R.t2 e1) (L R.t2 e2)
    (L R.t1 u) (L R.t2 u) hdet
  refine ⟨k1, k2, ?_⟩
  have s3u : L R.t3 u = -L R.t1 u - L R.t2 u := by linarith [R.L_sum hu]
  have s31 : L R.t3 e1 = -L R.t1 e1 - L R.t2 e1 := by linarith [R.L_sum u1]
  have s32 : L R.t3 e2 = -L R.t1 e2 - L R.t2 e2 := by linarith [R.L_sum u2]
  -- the log of the reduced unit, at any root
  have hL : ∀ t : ℝ, t ^ 3 = P * t + Q →
      L t (mul P Q u (mul P Q (zp P Q e1 e1i (-k1)) (zp P Q e2 e2i (-k2)))) =
        L t u - k1 * L t e1 - k2 * L t e2 := by
    intro t ht
    have z1 := sig_ne_of_unit (isUnit_zp h1 R (-k1)) ht
    have z2 := sig_ne_of_unit (isUnit_zp h2 R (-k2)) ht
    rw [L_mul ht (sig_ne_of_unit hu ht) (by rw [sig_mul ht]; exact mul_ne_zero z1 z2), L_mul ht z1 z2,
      L_zp ht h1, L_zp ht h2]
    push_cast
    ring
  -- `|σ|² = exp(2L) ≤ exp(|L ε₁| + |L ε₂|)`
  have fin : ∀ t : ℝ, t ^ 3 = P * t + Q →
      |L t (mul P Q u (mul P Q (zp P Q e1 e1i (-k1)) (zp P Q e2 e2i (-k2))))| ≤
        (|L t e1| + |L t e2|) / 2 →
      |sig t (mul P Q u (mul P Q (zp P Q e1 e1i (-k1)) (zp P Q e2 e2i (-k2))))| ^ 2 ≤
        max |sig t e1| |sig t e1|⁻¹ * max |sig t e2| |sig t e2|⁻¹ := by
    intro t ht hb
    set w := mul P Q u (mul P Q (zp P Q e1 e1i (-k1)) (zp P Q e2 e2i (-k2)))
    have hw : IsUnit' P Q w := isUnit_mul hu (isUnit_mul (isUnit_zp h1 R _) (isUnit_zp h2 R _))
    have pw : 0 < |sig t w| := abs_pos.mpr (sig_ne_of_unit hw ht)
    have p1 : 0 < |sig t e1| := abs_pos.mpr (sig_ne_of_unit u1 ht)
    have p2 : 0 < |sig t e2| := abs_pos.mpr (sig_ne_of_unit u2 ht)
    rw [← exp_abs_log p1, ← exp_abs_log p2, ← Real.exp_add, ← Real.exp_log pw, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : Real.log |sig t w| ≤ |L t w| := le_abs_self _
    simp only [L] at hb this ⊢
    push_cast
    linarith
  intro t htm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htm
  rcases htm with rfl | rfl | rfl
  · apply fin _ R.h1
    rw [hL _ R.h1]
    convert b1 using 2
  · apply fin _ R.h2
    rw [hL _ R.h2]
    convert b2 using 2
  · apply fin _ R.h3
    rw [hL _ R.h3, s3u, s31, s32]
    convert b3 using 2

/-! ### Rational enclosures -/

/-- `X³ − PX − Q` at a rational. -/
def cub (P Q : ℤ) (x : ℚ) : ℚ := x ^ 3 - P * x - Q

/-- **A root in a bracket with a sign change** (intermediate value theorem). -/
lemma root_in (P Q : ℤ) (lo hi : ℚ) (hle : lo ≤ hi) (hs : cub P Q lo * cub P Q hi < 0) :
    ∃ t : ℝ, (lo : ℝ) ≤ t ∧ t ≤ hi ∧ t ^ 3 = P * t + Q := by
  let f : ℝ → ℝ := fun x => x ^ 3 - P * x - Q
  have hc : ContinuousOn f (Set.Icc (lo : ℝ) hi) := by fun_prop
  have hle' : (lo : ℝ) ≤ hi := by exact_mod_cast hle
  have fl : f lo = ((cub P Q lo : ℚ) : ℝ) := by simp only [f, cub]; push_cast; ring
  have fh : f hi = ((cub P Q hi : ℚ) : ℝ) := by simp only [f, cub]; push_cast; ring
  have key : (0 : ℝ) ∈ f '' Set.Icc (lo : ℝ) hi := by
    rcases lt_or_gt_of_ne (show cub P Q lo ≠ 0 by intro h; rw [h, zero_mul] at hs; exact lt_irrefl _ hs)
      with h | h
    · have hh : 0 < cub P Q hi := by nlinarith
      apply intermediate_value_Icc hle' hc
      rw [fl, fh]; constructor <;> exact_mod_cast le_of_lt (by assumption)
    · have hh : cub P Q hi < 0 := by nlinarith
      apply intermediate_value_Icc' hle' hc
      rw [fl, fh]; constructor <;> exact_mod_cast le_of_lt (by assumption)
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := key
  exact ⟨t, h1, h2, by simp only [f] at ht; linarith⟩

/-- The embedding at a rational point. -/
def sigQ (x : ℚ) (g : Z3) : ℚ := g.1 + g.2.1 * x + g.2.2 * x ^ 2

/-- How far `σ` can move over `[lo, hi]`. -/
def rad (g : Z3) (lo hi : ℚ) : ℚ := (hi - lo) * (|(g.2.1 : ℚ)| + 2 * |(g.2.2 : ℚ)| * max |lo| |hi|)

/-- Lower end of the enclosure of `|σ|` on `[lo, hi]`. -/
def pLo (g : Z3) (lo hi : ℚ) : ℚ := |sigQ lo g| - rad g lo hi
/-- Upper end of the enclosure of `|σ|` on `[lo, hi]`. -/
def pHi (g : Z3) (lo hi : ℚ) : ℚ := |sigQ lo g| + rad g lo hi

lemma abs_le_max_of {x : ℝ} {lo hi : ℚ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    |x| ≤ ((max |lo| |hi| : ℚ) : ℝ) := by
  push_cast
  exact DirectReduction.abs_le_of_between h1 h2

lemma encl_sound (g : Z3) {lo hi : ℚ} {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    ((pLo g lo hi : ℚ) : ℝ) ≤ |sig t g| ∧ |sig t g| ≤ ((pHi g lo hi : ℚ) : ℝ) := by
  have hR := abs_le_max_of h1 h2
  have hR0 : |(lo : ℝ)| ≤ ((max |lo| |hi| : ℚ) : ℝ) := by push_cast; exact le_max_left _ _
  have hd : sig t g - ((sigQ lo g : ℚ) : ℝ) = (t - lo) * (g.2.1 + g.2.2 * (t + lo)) := by
    simp only [sig, sigQ]; push_cast; ring
  have hb : |sig t g - ((sigQ lo g : ℚ) : ℝ)| ≤ ((rad g lo hi : ℚ) : ℝ) := by
    rw [hd, abs_mul]
    have e1 : |t - lo| ≤ (hi : ℝ) - lo := by rw [abs_of_nonneg (by linarith)]; linarith
    have e2 : |(g.2.1 : ℝ) + g.2.2 * (t + lo)| ≤ |(g.2.1 : ℝ)| + 2 * |(g.2.2 : ℝ)| * ((max |lo| |hi| : ℚ) : ℝ) := by
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
  have := abs_sub_abs_le_abs_sub (sig t g) ((sigQ lo g : ℚ) : ℝ)
  have := abs_sub_abs_le_abs_sub ((sigQ lo g : ℚ) : ℝ) (sig t g)
  rw [abs_sub_comm] at this
  simp only [pLo, pHi]
  push_cast
  push_cast at hb
  constructor <;> linarith

lemma log_ge_of {y : ℝ} {s : ℚ} {n : ℕ} (hs : 0 < s) (h : ((s : ℝ)) ^ n ≤ y) :
    ((n * (1 - 1 / s) : ℚ) : ℝ) ≤ Real.log y := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : Real.log ((s : ℝ) ^ n) ≤ Real.log y := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  have h2 : Real.log (s : ℝ)⁻¹ ≤ (s : ℝ)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hs')
  rw [Real.log_inv] at h2
  have h3 : 1 - 1 / (s : ℝ) ≤ Real.log s := by rw [one_div]; linarith
  push_cast
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hn]

lemma log_le_of {y : ℝ} {s : ℚ} {n : ℕ} (hy : 0 < y) (hs : 0 < s) (h : y ≤ ((s : ℝ)) ^ n) :
    Real.log y ≤ ((n * (s - 1) : ℚ) : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : Real.log y ≤ Real.log ((s : ℝ) ^ n) := Real.log_le_log hy h
  rw [Real.log_pow] at h1
  have h2 := Real.log_le_sub_one_of_pos hs'
  push_cast
  nlinarith [show (0 : ℝ) ≤ n by positivity]

/-- Interval product, lower end. -/
def imin (a b c d : ℚ) : ℚ := min (min (a * c) (a * d)) (min (b * c) (b * d))
/-- Interval product, upper end. -/
def imax (a b c d : ℚ) : ℚ := max (max (a * c) (a * d)) (max (b * c) (b * d))

lemma imul_sound {x y : ℝ} {a b c d : ℚ} (h1 : (a : ℝ) ≤ x) (h2 : x ≤ b) (h3 : (c : ℝ) ≤ y)
    (h4 : y ≤ d) : ((imin a b c d : ℚ) : ℝ) ≤ x * y ∧ x * y ≤ ((imax a b c d : ℚ) : ℝ) := by
  simp only [imin, imax, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  have lo1 : min ((a : ℝ) * y) (b * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hy)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hy)
  have hi1 : x * y ≤ max ((a : ℝ) * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact le_trans (mul_le_mul_of_nonneg_right h2 hy) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_right h1 hy) (le_max_left _ _)
  have la : min ((a : ℝ) * c) ((a : ℝ) * d) ≤ a * y := by
    rcases le_total 0 (a : ℝ) with ha | ha
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h3 ha)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h4 ha)
  have lb : min ((b : ℝ) * c) ((b : ℝ) * d) ≤ b * y := by
    rcases le_total 0 (b : ℝ) with hb | hb
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h3 hb)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h4 hb)
  have ua : (a : ℝ) * y ≤ max ((a : ℝ) * c) ((a : ℝ) * d) := by
    rcases le_total 0 (a : ℝ) with ha | ha
    · exact le_trans (mul_le_mul_of_nonneg_left h4 ha) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left h3 ha) (le_max_left _ _)
  have ub : (b : ℝ) * y ≤ max ((b : ℝ) * c) ((b : ℝ) * d) := by
    rcases le_total 0 (b : ℝ) with hb | hb
    · exact le_trans (mul_le_mul_of_nonneg_left h4 hb) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left h3 hb) (le_max_left _ _)
  constructor
  · calc _ ≤ min ((a : ℝ) * y) (b * y) := min_le_min la lb
      _ ≤ x * y := lo1
  · calc x * y ≤ max ((a : ℝ) * y) (b * y) := hi1
      _ ≤ _ := max_le_max ua ub

/-! ### The coordinate box -/

lemma term_le {N s D Nb U G : ℝ} (hN : |N| ≤ Nb) (hs : |s| ≤ U) (hG : 0 < G) (hD : G ≤ |D|) :
    |N * s / D| ≤ Nb * U / G := by
  rw [abs_div, abs_mul]
  have hNb : 0 ≤ Nb := le_trans (abs_nonneg _) hN
  have hD0 : 0 < |D| := lt_of_lt_of_le hG hD
  calc |N| * |s| / |D| ≤ Nb * U / |D| := by
        apply div_le_div_of_nonneg_right _ hD0.le
        exact mul_le_mul hN hs (abs_nonneg _) hNb
    _ ≤ Nb * U / G := div_le_div_of_nonneg_left (mul_nonneg hNb (le_trans (abs_nonneg _) hs)) hG hD

/-- **The coordinates are bounded by the embeddings** (Lagrange interpolation). -/
lemma Roots.coord_bounds (R : Roots P Q) (g : Z3) {U1 U2 U3 G1 G2 G3 S1 S2 S3 T1 T2 T3 : ℝ}
    (hU1 : |sig R.t1 g| ≤ U1) (hU2 : |sig R.t2 g| ≤ U2) (hU3 : |sig R.t3 g| ≤ U3)
    (hG1 : 0 < G1) (hG2 : 0 < G2) (hG3 : 0 < G3)
    (hD1 : G1 ≤ |R.D1|) (hD2 : G2 ≤ |R.D2|) (hD3 : G3 ≤ |R.D3|)
    (hS1 : |R.t2 + R.t3| ≤ S1) (hS2 : |R.t1 + R.t3| ≤ S2) (hS3 : |R.t1 + R.t2| ≤ S3)
    (hT1 : |R.t2 * R.t3| ≤ T1) (hT2 : |R.t1 * R.t3| ≤ T2) (hT3 : |R.t1 * R.t2| ≤ T3) :
    |(g.2.2 : ℝ)| ≤ U1 / G1 + U2 / G2 + U3 / G3 ∧
    |(g.2.1 : ℝ)| ≤ S1 * U1 / G1 + S2 * U2 / G2 + S3 * U3 / G3 ∧
    |(g.1 : ℝ)| ≤ T1 * U1 / G1 + T2 * U2 / G2 + T3 * U3 / G3 := by
  obtain ⟨hc, hb, ha⟩ := R.coords g
  have one : |(1 : ℝ)| ≤ 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]
    have e1 := term_le one hU1 hG1 hD1
    have e2 := term_le one hU2 hG2 hD2
    have e3 := term_le one hU3 hG3 hD3
    simp only [one_mul] at e1 e2 e3
    calc _ ≤ |sig R.t1 g / R.D1| + |sig R.t2 g / R.D2| + |sig R.t3 g / R.D3| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  · rw [hb, abs_neg]
    have e1 := term_le hS1 hU1 hG1 hD1
    have e2 := term_le hS2 hU2 hG2 hD2
    have e3 := term_le hS3 hU3 hG3 hD3
    calc _ ≤ |(R.t2 + R.t3) * sig R.t1 g / R.D1| + |(R.t1 + R.t3) * sig R.t2 g / R.D2| +
          |(R.t1 + R.t2) * sig R.t3 g / R.D3| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  · rw [ha]
    have e1 := term_le hT1 hU1 hG1 hD1
    have e2 := term_le hT2 hU2 hG2 hD2
    have e3 := term_le hT3 hU3 hG3 hD3
    calc _ ≤ |R.t2 * R.t3 * sig R.t1 g / R.D1| + |R.t1 * R.t3 * sig R.t2 g / R.D2| +
          |R.t1 * R.t2 * sig R.t3 g / R.D3| := abs_add_three _ _ _
      _ ≤ _ := by linarith

/-! ### The certificate -/

/-- A unit-generation certificate: root brackets, log witnesses, the bounds `Uᵢ`, the box, and a
representation `(sign, x, y)` of every unit in the box. -/
structure UGCert where
  /-- Bracket of the first root. -/
  lo1 : ℚ
  /-- Bracket of the first root. -/
  hi1 : ℚ
  /-- Bracket of the second root. -/
  lo2 : ℚ
  /-- Bracket of the second root. -/
  hi2 : ℚ
  /-- Bracket of the third root. -/
  lo3 : ℚ
  /-- Bracket of the third root. -/
  hi3 : ℚ
  /-- The exponent of the log witnesses. -/
  n : ℕ
  /-- `sⁿ ≤ |σ₁ ε₁|`. -/
  s11 : ℚ
  /-- `|σ₁ ε₁| ≤ Sⁿ`. -/
  S11 : ℚ
  /-- `sⁿ ≤ |σ₂ ε₁|`. -/
  s21 : ℚ
  /-- `|σ₂ ε₁| ≤ Sⁿ`. -/
  S21 : ℚ
  /-- `sⁿ ≤ |σ₁ ε₂|`. -/
  s12 : ℚ
  /-- `|σ₁ ε₂| ≤ Sⁿ`. -/
  S12 : ℚ
  /-- `sⁿ ≤ |σ₂ ε₂|`. -/
  s22 : ℚ
  /-- `|σ₂ ε₂| ≤ Sⁿ`. -/
  S22 : ℚ
  /-- Bound on the first embedding of a reduced unit. -/
  U1 : ℚ
  /-- Bound on the second embedding of a reduced unit. -/
  U2 : ℚ
  /-- Bound on the third embedding of a reduced unit. -/
  U3 : ℚ
  /-- Box bound for the first coordinate. -/
  ba : ℕ
  /-- Box bound for the second coordinate. -/
  bb : ℕ
  /-- Box bound for the third coordinate. -/
  bc : ℕ
  /-- The units of the box, as `(sign, x, y)`: `±ε₁^x ε₂^y`. -/
  reps : List (ℤ × ℤ × ℤ)

/-- `±ε₁^x ε₂^y`. -/
def evalRep (P Q : ℤ) (e1 e1i e2 e2i : Z3) (r : ℤ × ℤ × ℤ) : Z3 :=
  if r.1 = 1 then mul P Q (zp P Q e1 e1i r.2.1) (zp P Q e2 e2i r.2.2)
  else neg (mul P Q (zp P Q e1 e1i r.2.1) (zp P Q e2 e2i r.2.2))

/-- The root brackets: sign changes, and in increasing order. -/
def bracketsB (P Q : ℤ) (C : UGCert) : Bool :=
  decide (C.lo1 ≤ C.hi1) && decide (cub P Q C.lo1 * cub P Q C.hi1 < 0) &&
  decide (C.lo2 ≤ C.hi2) && decide (cub P Q C.lo2 * cub P Q C.hi2 < 0) &&
  decide (C.lo3 ≤ C.hi3) && decide (cub P Q C.lo3 * cub P Q C.hi3 < 0) &&
  decide (C.hi1 < C.lo2) && decide (C.hi2 < C.lo3)

/-- A log witness: `0 < sⁿ ≤ pLo` and `pHi ≤ Sⁿ`. -/
def logB (g : Z3) (lo hi s S : ℚ) (n : ℕ) : Bool :=
  decide (0 < s) && decide (s ^ n ≤ pLo g lo hi) && decide (0 < pLo g lo hi) &&
    decide (pHi g lo hi ≤ S ^ n) && decide (0 < S)

/-- The log determinant is enclosed away from zero. -/
def detB (C : UGCert) : Bool :=
  let l := fun s : ℚ => (C.n : ℚ) * (1 - 1 / s)
  let u := fun S : ℚ => (C.n : ℚ) * (S - 1)
  let lo := imin (l C.s11) (u C.S11) (l C.s22) (u C.S22) - imax (l C.s12) (u C.S12) (l C.s21) (u C.S21)
  let hi := imax (l C.s11) (u C.S11) (l C.s22) (u C.S22) - imin (l C.s12) (u C.S12) (l C.s21) (u C.S21)
  decide (0 < lo) || decide (hi < 0)

/-- `max(|σ|, |σ|⁻¹) ≤ max(pHi, 1/pLo)`. -/
def mB (g : Z3) (lo hi : ℚ) : ℚ := max (pHi g lo hi) (1 / pLo g lo hi)

/-- The bounds `Uᵢ`. -/
def uB (e1 e2 : Z3) (C : UGCert) : Bool :=
  decide (0 < pLo e1 C.lo1 C.hi1) && decide (0 < pLo e2 C.lo1 C.hi1) &&
  decide (0 < pLo e1 C.lo2 C.hi2) && decide (0 < pLo e2 C.lo2 C.hi2) &&
  decide (0 < pLo e1 C.lo3 C.hi3) && decide (0 < pLo e2 C.lo3 C.hi3) &&
  decide (0 ≤ C.U1) && decide (0 ≤ C.U2) && decide (0 ≤ C.U3) &&
  decide (mB e1 C.lo1 C.hi1 * mB e2 C.lo1 C.hi1 ≤ C.U1 ^ 2) &&
  decide (mB e1 C.lo2 C.hi2 * mB e2 C.lo2 C.hi2 ≤ C.U2 ^ 2) &&
  decide (mB e1 C.lo3 C.hi3 * mB e2 C.lo3 C.hi3 ≤ C.U3 ^ 2)

/-- Gap bounds and the coordinate box. -/
def boxB (C : UGCert) : Bool :=
  let g12 := C.lo2 - C.hi1
  let g13 := C.lo3 - C.hi1
  let g23 := C.lo3 - C.hi2
  let G1 := g12 * g13
  let G2 := g12 * g23
  let G3 := g13 * g23
  let m1 := max |C.lo1| |C.hi1|
  let m2 := max |C.lo2| |C.hi2|
  let m3 := max |C.lo3| |C.hi3|
  let S1 := max |C.lo2 + C.lo3| |C.hi2 + C.hi3|
  let S2 := max |C.lo1 + C.lo3| |C.hi1 + C.hi3|
  let S3 := max |C.lo1 + C.lo2| |C.hi1 + C.hi2|
  decide (C.U1 / G1 + C.U2 / G2 + C.U3 / G3 < C.bc + 1) &&
  decide (S1 * C.U1 / G1 + S2 * C.U2 / G2 + S3 * C.U3 / G3 < C.bb + 1) &&
  decide (m2 * m3 * C.U1 / G1 + m1 * m3 * C.U2 / G2 + m1 * m2 * C.U3 / G3 < C.ba + 1)

/-- **The whole certificate.** -/
def ugCheck (P Q : ℤ) (e1 e1i e2 e2i : Z3) (C : UGCert) : Bool :=
  decide (mul P Q e1 e1i = (1, 0, 0)) && decide (mul P Q e2 e2i = (1, 0, 0)) && bracketsB P Q C &&
  logB e1 C.lo1 C.hi1 C.s11 C.S11 C.n && logB e1 C.lo2 C.hi2 C.s21 C.S21 C.n &&
  logB e2 C.lo1 C.hi1 C.s12 C.S12 C.n && logB e2 C.lo2 C.hi2 C.s22 C.S22 C.n &&
  detB C && uB e1 e2 C && boxB C &&
  unitBoxB P Q C.ba C.bb C.bc (C.reps.map (evalRep P Q e1 e1i e2 e2i))

/-! ### The main theorem -/

lemma solve_u {su s1 s2 sw c : ℝ} (h1 : s1 ≠ 0) (h2 : s2 ≠ 0) {k1 k2 x y : ℤ}
    (hw : sw = su * (s1 ^ (-k1) * s2 ^ (-k2))) (hc : sw = c * (s1 ^ x * s2 ^ y)) :
    su = c * (s1 ^ (x + k1) * s2 ^ (y + k2)) := by
  have e1 : s1 ^ (-k1) * s1 ^ k1 = 1 := by rw [← zpow_add₀ h1, neg_add_cancel, zpow_zero]
  have e2 : s2 ^ (-k2) * s2 ^ k2 = 1 := by rw [← zpow_add₀ h2, neg_add_cancel, zpow_zero]
  rw [zpow_add₀ h1, zpow_add₀ h2]
  calc su = su * (s1 ^ (-k1) * s1 ^ k1) * (s2 ^ (-k2) * s2 ^ k2) := by rw [e1, e2]; ring
    _ = (su * (s1 ^ (-k1) * s2 ^ (-k2))) * s1 ^ k1 * s2 ^ k2 := by ring
    _ = _ := by rw [← hw, hc]; ring

lemma gap_le {a b : ℝ} {hia lob : ℚ} (ha : a ≤ hia) (hb : (lob : ℝ) ≤ b) :
    ((lob - hia : ℚ) : ℝ) ≤ |a - b| := by
  push_cast
  rw [abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

lemma L_encl {g : Z3} {lo hi s S : ℚ} {n : ℕ} (h : logB g lo hi s S n = true) {t : ℝ}
    (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    (((n : ℚ) * (1 - 1 / s) : ℚ) : ℝ) ≤ L t g ∧ L t g ≤ (((n : ℚ) * (S - 1) : ℚ) : ℝ) := by
  simp only [logB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs, hsn⟩, hp⟩, hSn⟩, hS⟩ := h
  obtain ⟨e1, e2⟩ := encl_sound g h1 h2
  have hpR : (0 : ℝ) < ((pLo g lo hi : ℚ) : ℝ) := by exact_mod_cast hp
  constructor
  · apply log_ge_of hs
    calc ((s : ℝ)) ^ n = ((s ^ n : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((pLo g lo hi : ℚ) : ℝ) := by exact_mod_cast hsn
      _ ≤ _ := e1
  · apply log_le_of (lt_of_lt_of_le hpR e1) hS
    calc |sig t g| ≤ ((pHi g lo hi : ℚ) : ℝ) := e2
      _ ≤ ((S ^ n : ℚ) : ℝ) := by exact_mod_cast hSn
      _ = (S : ℝ) ^ n := by push_cast; ring

lemma max_le_mB {g : Z3} {lo hi : ℚ} {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) (hp : 0 < pLo g lo hi) :
    max |sig t g| |sig t g|⁻¹ ≤ ((mB g lo hi : ℚ) : ℝ) := by
  obtain ⟨e1, e2⟩ := encl_sound g h1 h2
  have hpR : (0 : ℝ) < ((pLo g lo hi : ℚ) : ℝ) := by exact_mod_cast hp
  simp only [mB, Rat.cast_max, Rat.cast_div, Rat.cast_one]
  apply max_le
  · exact le_trans e2 (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [one_div]
    exact inv_anti₀ hpR e1

/-- **Unit generation from a checked certificate.** -/
theorem unitGen_of_cert (P Q : ℤ) (e1 e1i e2 e2i : Z3) (C : UGCert)
    (h : ugCheck P Q e1 e1i e2 e2i C = true) : UnitGen P Q e1 e1i e2 e2i := by
  simp only [ugCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi1, hi2⟩, hbr⟩, hl11⟩, hl21⟩, hl12⟩, hl22⟩, hdt⟩, hub⟩, hbx⟩, hun⟩ := h
  simp only [bracketsB, Bool.and_eq_true, decide_eq_true_eq] at hbr
  obtain ⟨⟨⟨⟨⟨⟨⟨b1, c1⟩, b2⟩, c2⟩, b3⟩, c3⟩, o12⟩, o23⟩ := hbr
  obtain ⟨t1, a1, a1', r1⟩ := root_in P Q _ _ b1 c1
  obtain ⟨t2, a2, a2', r2⟩ := root_in P Q _ _ b2 c2
  obtain ⟨t3, a3, a3', r3⟩ := root_in P Q _ _ b3 c3
  have o12' : (C.hi1 : ℝ) < C.lo2 := by exact_mod_cast o12
  have o23' : (C.hi2 : ℝ) < C.lo3 := by exact_mod_cast o23
  let R : Roots P Q := ⟨t1, t2, t3, r1, r2, r3, by intro h; linarith, by intro h; linarith,
    by intro h; linarith⟩
  -- the log determinant
  have hdet : L R.t1 e1 * L R.t2 e2 - L R.t1 e2 * L R.t2 e1 ≠ 0 := by
    obtain ⟨x11l, x11u⟩ := L_encl hl11 a1 a1'
    obtain ⟨x21l, x21u⟩ := L_encl hl21 a2 a2'
    obtain ⟨x12l, x12u⟩ := L_encl hl12 a1 a1'
    obtain ⟨x22l, x22u⟩ := L_encl hl22 a2 a2'
    obtain ⟨p1l, p1u⟩ := imul_sound x11l x11u x22l x22u
    obtain ⟨p2l, p2u⟩ := imul_sound x12l x12u x21l x21u
    simp only [detB, Bool.or_eq_true, decide_eq_true_eq] at hdt
    rcases hdt with hd | hd
    · have hd' := (Rat.cast_lt (K := ℝ)).mpr hd
      push_cast at hd'
      intro h0
      linarith
    · have hd' := (Rat.cast_lt (K := ℝ)).mpr hd
      push_cast at hd'
      intro h0
      linarith
  intro u v huv
  have hu : IsUnit' P Q u := ⟨v, huv⟩
  obtain ⟨k1, k2, hb⟩ := R.reduce_unit hi1 hi2 hdet hu
  set w := mul P Q u (mul P Q (zp P Q e1 e1i (-k1)) (zp P Q e2 e2i (-k2))) with hwdef
  have hw : IsUnit' P Q w := isUnit_mul hu (isUnit_mul (isUnit_zp hi1 R _) (isUnit_zp hi2 R _))
  -- the bounds |σᵢ w| ≤ Uᵢ
  simp only [uB, Bool.and_eq_true, decide_eq_true_eq] at hub
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨p11, p21⟩, p12⟩, p22⟩, p13⟩, p23⟩, hU1⟩, hU2⟩, hU3⟩, q1⟩, q2⟩, q3⟩ := hub
  have Ubound : ∀ (t : ℝ) (lo hi U : ℚ), t ∈ ({R.t1, R.t2, R.t3} : Set ℝ) → (lo : ℝ) ≤ t → t ≤ hi →
      0 < pLo e1 lo hi → 0 < pLo e2 lo hi → 0 ≤ U → mB e1 lo hi * mB e2 lo hi ≤ U ^ 2 →
      |sig t w| ≤ U := by
    intro t lo hi U ht h1 h2 hp1 hp2 hU hq
    have m1 := max_le_mB (g := e1) h1 h2 hp1
    have m2 := max_le_mB (g := e2) h1 h2 hp2
    have hq' : ((mB e1 lo hi : ℚ) : ℝ) * ((mB e2 lo hi : ℚ) : ℝ) ≤ (U : ℝ) ^ 2 := by exact_mod_cast hq
    have hU' : (0 : ℝ) ≤ U := by exact_mod_cast hU
    have := hb t ht
    have n2 : 0 ≤ max |sig t e2| |sig t e2|⁻¹ := le_trans (abs_nonneg _) (le_max_left _ _)
    have n1 : 0 ≤ ((mB e1 lo hi : ℚ) : ℝ) := le_trans (le_trans (abs_nonneg _) (le_max_left _ _)) m1
    have hsq : |sig t w| ^ 2 ≤ (U : ℝ) ^ 2 :=
      le_trans this (le_trans (mul_le_mul m1 m2 n2 n1) hq')
    exact (sq_le_sq₀ (abs_nonneg _) hU').mp hsq
  have u1 := Ubound R.t1 C.lo1 C.hi1 C.U1 (by simp) a1 a1' p11 p21 hU1 q1
  have u2 := Ubound R.t2 C.lo2 C.hi2 C.U2 (by simp) a2 a2' p12 p22 hU2 q2
  have u3 := Ubound R.t3 C.lo3 C.hi3 C.U3 (by simp) a3 a3' p13 p23 hU3 q3
  -- the coordinate box
  have g12 := gap_le (a := R.t1) (b := R.t2) a1' a2
  have g13 := gap_le (a := R.t1) (b := R.t3) a1' a3
  have g23 := gap_le (a := R.t2) (b := R.t3) a2' a3
  have g21 : ((C.lo2 - C.hi1 : ℚ) : ℝ) ≤ |R.t2 - R.t1| := by rw [abs_sub_comm]; exact g12
  have g31 : ((C.lo3 - C.hi1 : ℚ) : ℝ) ≤ |R.t3 - R.t1| := by rw [abs_sub_comm]; exact g13
  have g32 : ((C.lo3 - C.hi2 : ℚ) : ℝ) ≤ |R.t3 - R.t2| := by rw [abs_sub_comm]; exact g23
  have z12 : (0 : ℝ) < ((C.lo2 - C.hi1 : ℚ) : ℝ) := by push_cast; linarith
  have z13 : (0 : ℝ) < ((C.lo3 - C.hi1 : ℚ) : ℝ) := by push_cast; linarith [a2, a2']
  have z23 : (0 : ℝ) < ((C.lo3 - C.hi2 : ℚ) : ℝ) := by push_cast; linarith
  have D1 : ((C.lo2 - C.hi1 : ℚ) : ℝ) * ((C.lo3 - C.hi1 : ℚ) : ℝ) ≤ |R.D1| := by
    simp only [Roots.D1, abs_mul]; exact mul_le_mul g12 g13 z13.le (abs_nonneg _)
  have D2 : ((C.lo2 - C.hi1 : ℚ) : ℝ) * ((C.lo3 - C.hi2 : ℚ) : ℝ) ≤ |R.D2| := by
    simp only [Roots.D2, abs_mul]; exact mul_le_mul g21 g23 z23.le (abs_nonneg _)
  have D3 : ((C.lo3 - C.hi1 : ℚ) : ℝ) * ((C.lo3 - C.hi2 : ℚ) : ℝ) ≤ |R.D3| := by
    simp only [Roots.D3, abs_mul]; exact mul_le_mul g31 g32 z23.le (abs_nonneg _)
  have m1 := abs_le_max_of a1 a1'
  have m2 := abs_le_max_of a2 a2'
  have m3 := abs_le_max_of a3 a3'
  have S1 : |R.t2 + R.t3| ≤ ((max |C.lo2 + C.lo3| |C.hi2 + C.hi3| : ℚ) : ℝ) := by
    have := DirectReduction.abs_le_of_between (x := R.t2 + R.t3) (a := ((C.lo2 + C.lo3 : ℚ) : ℝ))
      (b := ((C.hi2 + C.hi3 : ℚ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
    simpa [Rat.cast_max, Rat.cast_abs] using this
  have S2 : |R.t1 + R.t3| ≤ ((max |C.lo1 + C.lo3| |C.hi1 + C.hi3| : ℚ) : ℝ) := by
    have := DirectReduction.abs_le_of_between (x := R.t1 + R.t3) (a := ((C.lo1 + C.lo3 : ℚ) : ℝ))
      (b := ((C.hi1 + C.hi3 : ℚ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
    simpa [Rat.cast_max, Rat.cast_abs] using this
  have S3 : |R.t1 + R.t2| ≤ ((max |C.lo1 + C.lo2| |C.hi1 + C.hi2| : ℚ) : ℝ) := by
    have := DirectReduction.abs_le_of_between (x := R.t1 + R.t2) (a := ((C.lo1 + C.lo2 : ℚ) : ℝ))
      (b := ((C.hi1 + C.hi2 : ℚ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
    simpa [Rat.cast_max, Rat.cast_abs] using this
  have T1 : |R.t2 * R.t3| ≤ ((max |C.lo2| |C.hi2| : ℚ) : ℝ) * ((max |C.lo3| |C.hi3| : ℚ) : ℝ) := by
    rw [abs_mul]; exact mul_le_mul m2 m3 (abs_nonneg _) (le_trans (abs_nonneg _) m2)
  have T2 : |R.t1 * R.t3| ≤ ((max |C.lo1| |C.hi1| : ℚ) : ℝ) * ((max |C.lo3| |C.hi3| : ℚ) : ℝ) := by
    rw [abs_mul]; exact mul_le_mul m1 m3 (abs_nonneg _) (le_trans (abs_nonneg _) m1)
  have T3 : |R.t1 * R.t2| ≤ ((max |C.lo1| |C.hi1| : ℚ) : ℝ) * ((max |C.lo2| |C.hi2| : ℚ) : ℝ) := by
    rw [abs_mul]; exact mul_le_mul m1 m2 (abs_nonneg _) (le_trans (abs_nonneg _) m1)
  obtain ⟨cC, cB, cA⟩ := R.coord_bounds w u1 u2 u3 (mul_pos z12 z13) (mul_pos z12 z23)
    (mul_pos z13 z23) D1 D2 D3 S1 S2 S3 T1 T2 T3
  simp only [boxB, Bool.and_eq_true, decide_eq_true_eq] at hbx
  obtain ⟨⟨bxc, bxb⟩, bxa⟩ := hbx
  have bxc' := (Rat.cast_lt (K := ℝ)).mpr bxc
  have bxb' := (Rat.cast_lt (K := ℝ)).mpr bxb
  have bxa' := (Rat.cast_lt (K := ℝ)).mpr bxa
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one] at bxc' bxb' bxa'
  have wc : |w.2.2| ≤ (C.bc : ℤ) := by
    have : |(w.2.2 : ℝ)| < (C.bc : ℝ) + 1 := by linarith
    have : |w.2.2| < (C.bc : ℤ) + 1 := by exact_mod_cast this
    omega
  have wb : |w.2.1| ≤ (C.bb : ℤ) := by
    have : |(w.2.1 : ℝ)| < (C.bb : ℝ) + 1 := by linarith
    have : |w.2.1| < (C.bb : ℤ) + 1 := by exact_mod_cast this
    omega
  have wa : |w.1| ≤ (C.ba : ℤ) := by
    have : |(w.1 : ℝ)| < (C.ba : ℝ) + 1 := by linarith
    have : |w.1| < (C.ba : ℤ) + 1 := by exact_mod_cast this
    omega
  -- the reduced unit is listed
  have hn : nrm P Q w = 1 ∨ nrm P Q w = -1 := by
    have := R.abs_prod hw
    rw [← R.nrm_eq] at this
    rcases abs_eq (zero_le_one' ℝ) |>.mp this with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hmem := unitBox_sound hun w wa wb wc hn
  obtain ⟨r, -, hr⟩ := List.mem_map.mp hmem
  -- read off the exponents
  refine ⟨r.2.1 + k1, r.2.2 + k2, ?_⟩
  have key : ∀ t : ℝ, t ^ 3 = P * t + Q → ∀ c : ℝ,
      sig t w = c * (sig t e1 ^ r.2.1 * sig t e2 ^ r.2.2) →
      sig t u = c * (sig t e1 ^ (r.2.1 + k1) * sig t e2 ^ (r.2.2 + k2)) := by
    intro t ht c hc
    apply solve_u (sig_ne_of_unit ⟨e1i, hi1⟩ ht) (sig_ne_of_unit ⟨e2i, hi2⟩ ht) _ hc
    rw [hwdef, sig_mul ht, sig_mul ht, sig_zp ht hi1, sig_zp ht hi2]
  by_cases hs : r.1 = 1
  · left
    have hw' : w = mul P Q (zp P Q e1 e1i r.2.1) (zp P Q e2 e2i r.2.2) := by
      rw [← hr]; simp [evalRep, hs]
    have fin : ∀ t : ℝ, t ^ 3 = P * t + Q →
        sig t u = sig t (mul P Q (zp P Q e1 e1i (r.2.1 + k1)) (zp P Q e2 e2i (r.2.2 + k2))) := by
      intro t ht
      rw [sig_mul ht, sig_zp ht hi1, sig_zp ht hi2]
      have := key t ht 1 (by rw [hw', sig_mul ht, sig_zp ht hi1, sig_zp ht hi2, one_mul])
      rw [this, one_mul]
    exact R.sig_inj (fin _ R.h1) (fin _ R.h2) (fin _ R.h3)
  · right
    have hw' : w = neg (mul P Q (zp P Q e1 e1i r.2.1) (zp P Q e2 e2i r.2.2)) := by
      rw [← hr]; simp [evalRep, hs]
    have fin : ∀ t : ℝ, t ^ 3 = P * t + Q →
        sig t u = sig t (neg (mul P Q (zp P Q e1 e1i (r.2.1 + k1)) (zp P Q e2 e2i (r.2.2 + k2)))) := by
      intro t ht
      rw [sig_neg, sig_mul ht, sig_zp ht hi1, sig_zp ht hi2]
      have := key t ht (-1) (by rw [hw', sig_neg, sig_mul ht, sig_zp ht hi1, sig_zp ht hi2]; ring)
      rw [this]
      ring
    exact R.sig_inj (fin _ R.h1) (fin _ R.h2) (fin _ R.h3)

/-! ### The certificate in slices

For a large unit box the single evaluation of `unitBoxB` is too heavy for the kernel.  The same
check is split into slices of the first coordinate, each a separate kernel evaluation:
`ugCore` is everything except the box, and `unitBoxB_of_slices` assembles the slices. -/

/-- Everything in `ugCheck` except the final box enumeration. -/
def ugCore (P Q : ℤ) (e1 e1i e2 e2i : Z3) (C : UGCert) : Bool :=
  decide (mul P Q e1 e1i = (1, 0, 0)) && decide (mul P Q e2 e2i = (1, 0, 0)) && bracketsB P Q C &&
  logB e1 C.lo1 C.hi1 C.s11 C.S11 C.n && logB e1 C.lo2 C.hi2 C.s21 C.S21 C.n &&
  logB e2 C.lo1 C.hi1 C.s12 C.S12 C.n && logB e2 C.lo2 C.hi2 C.s22 C.S22 C.n &&
  detB C && uB e1 e2 C && boxB C

/-- Slice `t` (width `w`) of the unit box: first coordinates `i ∈ [t w, t w + w)`, `i ≤ 2a`. -/
def unitBoxSlice (P Q : ℤ) (a b c : ℕ) (cands : List Z3) (w t : ℕ) : Bool :=
  (List.range' (t * w) w).all fun i => !decide (i < 2 * a + 1) ||
    (List.range (2 * b + 1)).all fun j => (List.range (2 * c + 1)).all fun k =>
      let g : Z3 := ((i : ℤ) - a, (j : ℤ) - b, (k : ℤ) - c)
      !decide (nrm P Q g = 1 ∨ nrm P Q g = -1) || decide (g ∈ cands)

lemma unitBoxB_of_slices {P Q : ℤ} {a b c : ℕ} {cands : List Z3} {w n : ℕ} (hw : 0 < w)
    (hn : 2 * a + 1 ≤ n * w) (h : ∀ t < n, unitBoxSlice P Q a b c cands w t = true) :
    unitBoxB P Q a b c cands = true := by
  simp only [unitBoxB, List.all_eq_true, List.mem_range]
  intro i hi
  have ht : i / w < n := by
    rw [Nat.div_lt_iff_lt_mul hw]; omega
  have hs := h (i / w) ht
  simp only [unitBoxSlice, List.all_eq_true, List.mem_range', Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hs
  have hmem : ∃ k < w, i = i / w * w + k := ⟨i % w, Nat.mod_lt _ hw, by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod i w).symm⟩
  obtain ⟨k, hk, hik⟩ := hmem
  rcases hs i ⟨k, hk, by simpa [Nat.mul_comm] using hik⟩ with hlt | hrest
  · exact absurd hi hlt
  · intro j hj k' hk'
    simpa using hrest j (List.mem_range.mpr hj) k' (List.mem_range.mpr hk')

/-- **Unit generation from a sliced certificate.** -/
theorem unitGen_of_slices (P Q : ℤ) (e1 e1i e2 e2i : Z3) (C : UGCert) {w n : ℕ}
    (hcore : ugCore P Q e1 e1i e2 e2i C = true) (hw : 0 < w) (hn : 2 * C.ba + 1 ≤ n * w)
    (h : ∀ t < n, unitBoxSlice P Q C.ba C.bb C.bc (C.reps.map (evalRep P Q e1 e1i e2 e2i)) w t = true) :
    UnitGen P Q e1 e1i e2 e2i := by
  refine unitGen_of_cert P Q e1 e1i e2 e2i C ?_
  have hb := unitBoxB_of_slices hw hn h
  simp only [ugCore, Bool.and_eq_true] at hcore
  simp only [ugCheck, Bool.and_eq_true]
  exact ⟨hcore, hb⟩

end PerfectPower.UnitGenProof
