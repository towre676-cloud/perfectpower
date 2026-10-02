import PerfectPower.UnitGen
import PerfectPower.NormRepProof
import PerfectPower.SkolemP

/-!
# Rank-one monic Thue sources, generically

For an order `ℤ[z]`, `z³ = P z + Q`, with one real root `ρ` and a complex pair (unit rank 1),
this module turns a small certificate into the complete solution set of
`−u³ + P u v² + Q v³ = 1`, i.e. `−N(u − v z) = 1`.

* **The norm without complex numbers** (`norm_split`): `N(g) = σ(g) (re² + κ² j²)` with
  `κ² = 3ρ²/4 − P`, `re = a − bρ/2 + c(P − ρ²/2)` and `j = b − cρ`.
* **Unit generation** (`units_eq`). Every `w` with `N(w) = ±1` has `Mx w = ±ηⁿ`, from a rational
  bracket of `ρ`, a bound `J ≥ 1/κ`, and a bound `C` on the `z²` coordinate.
  - All the side conditions are rational inequalities checked by the kernel (`condB`).
  - `|j| ≤ J` leaves one or two `b` per `c`, and `|re| ≤ 1` about three `a` per `(b, c)`.
  - A kernel check of these slabs (`slabB`) finds only `±1, ±η` among the units with `|σ| ≥ 1`.
* **The zero set** (`SkolemP.corner_zero`, at an odd prime `p`): the `z²` coordinate of `ηⁿ`
  vanishes only at `n = 0`, for every integer `n`.
* **The source theorem** (`source`): `−u³ + P u v² + Q v³ = 1 ↔ (u, v) = (−1, 0)`.

`Plus2.lean` is the hand-written instance `P = −3`, `Q = −2`; `Generated/RankOneSources.lean`
holds the generated ones.
-/

namespace PerfectPower.RankOne

open PerfectPower UnitBox UnitPremises UnitGenProof NormRepProof Matrix

/-! ### Multiplication matrices -/

/-- The matrix of multiplication by `g` on the basis `1, z, z²`. -/
def Mx (P Q : ℤ) (g : Z3) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j =>
    let c := mul P Q g (if j = 0 then (1, 0, 0) else if j = 1 then (0, 1, 0) else (0, 0, 1))
    if i = 0 then c.1 else if i = 1 then c.2.1 else c.2.2

theorem Mx_mul (P Q : ℤ) (g h : Z3) : Mx P Q (mul P Q g h) = Mx P Q g * Mx P Q h := by
  obtain ⟨a, b, c⟩ := g
  obtain ⟨d, e, f⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mx, mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem Mx_one (P Q : ℤ) : Mx P Q (1, 0, 0) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mx, mul]

theorem Mx_neg (P Q : ℤ) (g : Z3) : Mx P Q (UnitBox.neg g) = -Mx P Q g := by
  obtain ⟨a, b, c⟩ := g
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mx, mul, UnitBox.neg] <;> ring

theorem Mx_col (P Q : ℤ) (g : Z3) : Mx P Q g 0 0 = g.1 ∧ Mx P Q g 1 0 = g.2.1 ∧ Mx P Q g 2 0 = g.2.2 := by
  obtain ⟨a, b, c⟩ := g
  simp [Mx, mul]

theorem Mx_pow (P Q : ℤ) (g : Z3) : ∀ n : ℕ, Mx P Q (pow P Q g n) = Mx P Q g ^ n
  | 0 => by simp [pow, Mx_one]
  | n + 1 => by rw [pow, Mx_mul, Mx_pow P Q g n, pow_succ]

/-- `η` as a unit of the matrix ring, with inverse `ε`. -/
def uη (P Q : ℤ) (η ε : Z3) (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0)) :
    (Matrix (Fin 3) (Fin 3) ℤ)ˣ :=
  ⟨Mx P Q η, Mx P Q ε, by rw [← Mx_mul, h1, Mx_one], by rw [← Mx_mul, h2, Mx_one]⟩

theorem Mx_zp (P Q : ℤ) (η ε : Z3) (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0)) (e : ℤ) :
    Mx P Q (zp P Q η ε e) = ((uη P Q η ε h1 h2 ^ e : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
  unfold zp
  split_ifs with h
  · rw [Mx_pow]
    conv_rhs => rw [show e = ((e.toNat : ℕ) : ℤ) by omega, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · rw [Mx_pow]
    conv_rhs => rw [show e = -(((-e).toNat : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val]
    rfl

/-! ### The zero set -/

/-- The hypotheses of `SkolemP.corner_zero` for a matrix `A`. -/
def SkolemData (p M : ℕ) (A D : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  0 < M ∧ A ^ M = 1 + p • D ∧ ¬ (p : ℤ) ∣ D 2 0 ∧ ∀ r, 0 < r → r < M → ¬ (p : ℤ) ∣ (A ^ r) 2 0

/-- **The `z²` coordinate of `ηⁿ` vanishes only at `n = 0`**, for every integer `n`. -/
theorem corner_eq_zero {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {M M' : ℕ} {D D' : Matrix (Fin 3) (Fin 3) ℤ}
    (hη : SkolemData p M (Mx P Q η) D) (hε : SkolemData p M' (Mx P Q ε) D') (n : ℤ)
    (h : ((uη P Q η ε h1 h2 ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) :
    n = 0 := by
  rcases le_or_lt 0 n with hn | hn
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at h
    have := SkolemP.corner_zero hp3 hη.1 hη.2.1 hη.2.2.1 hη.2.2.2 N h
    simp [this]
  · exfalso
    obtain ⟨N, hN⟩ : ∃ N : ℕ, n = -((N : ℕ) : ℤ) ∧ 0 < N := ⟨(-n).toNat, by omega, by omega⟩
    rw [hN.1, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at h
    have := SkolemP.corner_zero hp3 hε.1 hε.2.1 hε.2.2.1 hε.2.2.2 N h
    omega

/-! ### The norm and the real reduction -/

/-- **The norm without complex numbers**: `N(g) = σ(g) (re² + κ² j²)`, `κ² = 3ρ²/4 − P`. -/
theorem norm_split {P Q : ℤ} {t : ℝ} (ht : t ^ 3 = (P : ℝ) * t + Q) (g : Z3) :
    (nrm P Q g : ℝ) = sig t g * ((g.1 - g.2.1 * t / 2 + g.2.2 * (P - t ^ 2 / 2)) ^ 2 +
      (3 * t ^ 2 / 4 - P) * (g.2.1 - g.2.2 * t) ^ 2) := by
  obtain ⟨a, b, c⟩ := g
  simp only [nrm, sig]
  push_cast
  linear_combination (P * b * c ^ 2 + P * c ^ 3 * t - Q * c ^ 3 + 3 * a * b * c - b ^ 3 - c ^ 3 * t ^ 3) * ht

lemma nrm_pow (P Q : ℤ) (x : Z3) (hx : nrm P Q x = 1) : ∀ k : ℕ, nrm P Q (pow P Q x k) = 1
  | 0 => by simp [pow, nrm]
  | k + 1 => by rw [pow, nrm_mul, nrm_pow P Q x hx k, hx]; rfl

lemma nrm_zp (P Q : ℤ) {η ε : Z3} (hη : nrm P Q η = 1) (hε : nrm P Q ε = 1) (e : ℤ) :
    nrm P Q (zp P Q η ε e) = 1 := by
  unfold zp
  split_ifs
  · exact nrm_pow P Q η hη _
  · exact nrm_pow P Q ε hε _

/-- A rank-one certificate: a bracket `[lo, hi]` of the real root, `J ≥ 1/κ`, and `|c| ≤ C`. -/
structure Cert where
  /-- The bracket of the real root. -/
  lo : ℚ
  /-- The bracket of the real root. -/
  hi : ℚ
  /-- A bound `|j| ≤ J`, valid when `K J² ≥ 1`. -/
  J : ℚ
  /-- The bound `|c| ≤ C` on the `z²` coordinate of a reduced unit. -/
  C : ℕ

/-- `max |lo| |hi|`. -/
def Cert.T (c : Cert) : ℚ := max |c.lo| |c.hi|
/-- A lower bound for `ρ²` on the bracket. -/
def Cert.t2lo (c : Cert) : ℚ := if 0 ≤ c.lo then c.lo ^ 2 else if c.hi ≤ 0 then c.hi ^ 2 else 0
/-- A lower bound for `κ² = 3ρ²/4 − P`. -/
def Cert.K (P : ℤ) (c : Cert) : ℚ := 3 * c.t2lo / 4 - P
/-- A lower bound for `3ρ² − P`. -/
def Cert.Dn (P : ℤ) (c : Cert) : ℚ := 3 * c.t2lo - P
/-- An upper bound for `σ(η)`. -/
def Cert.E (η : Z3) (c : Cert) : ℚ := sigQ c.lo η + rad η c.lo c.hi

/-- **The side conditions**, all rational inequalities. -/
def condB (P Q : ℤ) (η : Z3) (c : Cert) : Bool :=
  decide (c.lo ≤ c.hi) && decide (cub P Q c.lo * cub P Q c.hi < 0) && decide (0 < c.K P) &&
  decide (0 ≤ c.J) && decide (1 ≤ c.K P * c.J ^ 2) && decide (0 < c.Dn P) &&
  decide (1 < sigQ c.lo η - rad η c.lo c.hi) &&
  decide (c.E η + 1 + 3 / 2 * c.T * c.J < (c.C + 1) * c.Dn P)

/-- The lower end of `x · [lo, hi]`. -/
def lmin (x lo hi : ℚ) : ℚ := if 0 ≤ x then x * lo else x * hi
/-- The upper end of `x · [lo, hi]`. -/
def lmax (x lo hi : ℚ) : ℚ := if 0 ≤ x then x * hi else x * lo

/-- The integers in `[l, h]`. -/
def ints (l h : ℚ) : List ℤ := (List.range ((⌊h⌋ - ⌈l⌉ + 1).toNat)).map fun i : ℕ => ⌈l⌉ + (i : ℤ)

/-- The candidates for `b` given `c`: `b = j + cρ` with `|j| ≤ J`. -/
def bRange (c : Cert) (cc : ℤ) : List ℤ := ints (lmin cc c.lo c.hi - c.J) (lmax cc c.lo c.hi + c.J)

/-- The candidates for `a` given `b, c`: `a = re + bρ/2 − cP + cρ²/2` with `|re| ≤ 1`. -/
def aRange (P : ℤ) (c : Cert) (b cc : ℤ) : List ℤ :=
  ints (-1 + lmin b c.lo c.hi / 2 - cc * P + lmin cc c.t2lo (c.T ^ 2) / 2)
    (1 + lmax b c.lo c.hi / 2 - cc * P + lmax cc c.t2lo (c.T ^ 2) / 2)

/-- One slab of the reduction: `c = l − C`, and the few `(a, b)` allowed by `|j| ≤ J`, `|re| ≤ 1`. -/
def slabSliceB (P Q : ℤ) (η : Z3) (c : Cert) (l : ℕ) : Bool :=
  (bRange c ((l : ℤ) - c.C)).all fun b => (aRange P c b ((l : ℤ) - c.C)).all fun a =>
    let g : Z3 := (a, b, (l : ℤ) - c.C)
    decide (nrm P Q g ≠ 1 ∧ nrm P Q g ≠ -1) ||
      decide (g ∈ [((1 : ℤ), (0 : ℤ), (0 : ℤ)), (-1, 0, 0), η, UnitBox.neg η]) ||
      decide (pHi g c.lo c.hi < 1)

/-- **The reduction check**: every unit `g` in the slabs is `±1`, `±η`, or has `|σ(g)| < 1`. -/
def slabB (P Q : ℤ) (η : Z3) (c : Cert) : Bool :=
  (List.range (2 * c.C + 1)).all (slabSliceB P Q η c)

lemma mem_ints {l h : ℚ} {x : ℤ} (h1 : l ≤ x) (h2 : (x : ℚ) ≤ h) : x ∈ ints l h := by
  have e1 : ⌈l⌉ ≤ x := Int.ceil_le.mpr h1
  have e2 : x ≤ ⌊h⌋ := Int.le_floor.mpr h2
  unfold ints
  apply List.mem_map.mpr
  refine ⟨(x - ⌈l⌉).toNat, List.mem_range.mpr ?_, ?_⟩
  · have : (x - ⌈l⌉).toNat < (⌊h⌋ - ⌈l⌉ + 1).toNat := by omega
    exact this
  · show ⌈l⌉ + ((x - ⌈l⌉).toNat : ℤ) = x
    omega

lemma lmin_le (x : ℚ) {lo hi : ℚ} {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    ((lmin x lo hi : ℚ) : ℝ) ≤ x * t := by
  unfold lmin
  split_ifs with h
  · push_cast
    have : (0 : ℝ) ≤ x := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left h1 this
  · push_cast
    have : (x : ℝ) < 0 := by exact_mod_cast not_le.mp h
    nlinarith

lemma le_lmax (x : ℚ) {lo hi : ℚ} {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) :
    x * t ≤ ((lmax x lo hi : ℚ) : ℝ) := by
  unfold lmax
  split_ifs with h
  · push_cast
    have : (0 : ℝ) ≤ x := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left h2 this
  · push_cast
    have : (x : ℝ) < 0 := by exact_mod_cast not_le.mp h
    nlinarith

lemma t2lo_le {c : Cert} {t : ℝ} (h1 : (c.lo : ℝ) ≤ t) (h2 : t ≤ c.hi) : ((c.t2lo : ℚ) : ℝ) ≤ t ^ 2 := by
  unfold Cert.t2lo
  split_ifs with ha hb
  · push_cast
    have h0 : (0 : ℝ) ≤ c.lo := by exact_mod_cast ha
    nlinarith
  · push_cast
    have h0 : (c.hi : ℝ) ≤ 0 := by exact_mod_cast hb
    nlinarith
  · push_cast; positivity

set_option maxHeartbeats 1000000 in
/-- **The reduced unit is `±1` or `±η`.** -/
@[nolint unusedHavesSuffices]
theorem reduced_mem {P Q : ℤ} {η : Z3} {c : Cert} (hc : condB P Q η c = true) (hbox : slabB P Q η c = true)
    {t : ℝ} (h1 : (c.lo : ℝ) ≤ t) (h2 : t ≤ c.hi) (ht : t ^ 3 = (P : ℝ) * t + Q) (v : Z3)
    (hv : nrm P Q v = 1 ∨ nrm P Q v = -1) (hs1 : 1 ≤ |sig t v|) (hs2 : |sig t v| ≤ ((c.E η : ℚ) : ℝ)) :
    v ∈ [((1 : ℤ), (0 : ℤ), (0 : ℤ)), (-1, 0, 0), η, UnitBox.neg η] := by
  simp only [condB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hK⟩, hJ0⟩, hKJ⟩, hDn⟩, _⟩, hcC⟩ := hc
  obtain ⟨a, b, cc⟩ := v
  have hsplit := norm_split ht (a, b, cc)
  simp only at hsplit
  obtain ⟨s, hsdef⟩ : ∃ s, s = sig t (a, b, cc) := ⟨_, rfl⟩
  obtain ⟨re, hredef⟩ : ∃ re, re = (a : ℝ) - b * t / 2 + cc * (P - t ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ j, j = (b : ℝ) - cc * t := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = 3 * t ^ 2 / 4 - (P : ℝ) := ⟨_, rfl⟩
  rw [← hsdef, ← hredef, ← hjdef, ← hκdef] at hsplit
  rw [← hsdef] at hs1 hs2
  -- rational bounds as reals
  obtain ⟨T, hTdef⟩ : ∃ T, T = ((c.T : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨t2l, ht2ldef⟩ : ∃ x, x = ((c.t2lo : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ x, x = ((c.J : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ x, x = ((c.E η : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hEdef] at hs2
  have hta : |t| ≤ T := by rw [hTdef]; exact abs_le_max_of h1 h2
  have ht2l : t2l ≤ t ^ 2 := by rw [ht2ldef]; exact t2lo_le h1 h2
  have ht2h : t ^ 2 ≤ T ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) hta 2
  have hK' : (0 : ℝ) < 3 * t2l / 4 - P := by
    rw [ht2ldef]; have : (0 : ℚ) < c.K P := hK; simp only [Cert.K] at this; exact_mod_cast this
  have hKJ' : 1 ≤ (3 * t2l / 4 - P) * J ^ 2 := by
    rw [ht2ldef, hJdef]; have : (1 : ℚ) ≤ c.K P * c.J ^ 2 := hKJ; simp only [Cert.K] at this
    exact_mod_cast this
  have hJ0' : (0 : ℝ) ≤ J := by rw [hJdef]; exact_mod_cast hJ0
  have hDn' : (0 : ℝ) < 3 * t2l - P := by
    rw [ht2ldef]; have : (0 : ℚ) < c.Dn P := hDn; simp only [Cert.Dn] at this; exact_mod_cast this
  have hκK : 3 * t2l / 4 - P ≤ κ := by rw [hκdef]; linarith
  have hκ0 : 0 < κ := by linarith
  -- |s| G = 1, so G ≤ 1
  have hG0 : 0 ≤ re ^ 2 + κ * j ^ 2 := by positivity
  have hsG : |s| * (re ^ 2 + κ * j ^ 2) = 1 := by
    have : |s * (re ^ 2 + κ * j ^ 2)| = 1 := by
      rw [← hsplit]; rcases hv with h | h <;> rw [h] <;> simp
    rwa [abs_mul, abs_of_nonneg hG0] at this
  have hGle : re ^ 2 + κ * j ^ 2 ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hs1 hG0
    linarith
  have hκj : 0 ≤ κ * j ^ 2 := by positivity
  have hre2 : re ^ 2 ≤ 1 := by linarith
  have hre' : |re| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hre2
  have hj' : |j| ≤ J := by
    have hkj : (3 * t2l / 4 - P) * j ^ 2 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hκK (sq_nonneg j)
      have := sq_nonneg re
      linarith
    have hsq : j ^ 2 ≤ J ^ 2 := by
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hK'
      linarith
    exact abs_le_of_sq_le_sq' hsq hJ0' |> fun h => abs_le.mpr h
  -- invert: c (3t² − P) = s − re − (3t/2) j
  have ec : (cc : ℝ) * (3 * t ^ 2 - P) = s - re - 3 * t / 2 * j := by
    rw [hsdef, hredef, hjdef]; simp only [sig]; ring
  have htj : |t| * |j| ≤ T * J := mul_le_mul hta hj' (abs_nonneg j) (le_trans (abs_nonneg t) hta)
  have hden : 3 * t2l - P ≤ 3 * t ^ 2 - P := by linarith
  have hpos : (0 : ℝ) < 3 * t ^ 2 - P := by linarith
  have hcR : |(cc : ℝ)| < c.C + 1 := by
    have h3 : |3 * t / 2 * j| = 3 / 2 * (|t| * |j|) := by
      rw [abs_mul, abs_div, abs_mul]; norm_num; ring
    have hnum : |s - re - 3 * t / 2 * j| ≤ E + 1 + 3 / 2 * (T * J) := by
      have e1 := abs_sub (s - re) (3 * t / 2 * j)
      have e2 := abs_sub s re
      linarith only [e1, e2, h3, htj, hs2, hre']
    have hcabs : |(cc : ℝ) * (3 * t ^ 2 - P)| = |(cc : ℝ)| * (3 * t ^ 2 - P) := by
      rw [abs_mul, abs_of_pos hpos]
    rw [ec] at hcabs
    have hm := mul_le_mul_of_nonneg_left hden (abs_nonneg (cc : ℝ))
    have hq : E + 1 + 3 / 2 * (T * J) < (c.C + 1) * (3 * t2l - P) := by
      rw [hEdef, hTdef, hJdef, ht2ldef]
      have : c.E η + 1 + 3 / 2 * c.T * c.J < (c.C + 1) * c.Dn P := hcC
      simp only [Cert.Dn] at this
      have := (Rat.cast_lt (K := ℝ)).mpr this
      push_cast at this
      linarith
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hDn'.le
    linarith only [this, hq, hm, hcabs, hnum]
  have ic : |cc| ≤ c.C := by
    have : |(cc : ℝ)| < ((c.C : ℤ) : ℝ) + 1 := by exact_mod_cast hcR
    have : |cc| < (c.C : ℤ) + 1 := by exact_mod_cast this
    omega
  -- the slab: b from |j| ≤ J, a from |re| ≤ 1
  have hj2 := abs_le.mp hj'
  have hre3 := abs_le.mp hre'
  have hb : b ∈ bRange c cc := by
    have l1 := lmin_le (cc : ℚ) h1 h2
    have l2 := le_lmax (cc : ℚ) h1 h2
    push_cast at l1 l2
    apply mem_ints
    · have : ((lmin cc c.lo c.hi - c.J : ℚ) : ℝ) ≤ (b : ℝ) := by
        push_cast; rw [← hJdef]; linarith only [l1, hj2.1, hjdef]
      exact_mod_cast this
    · have : (b : ℝ) ≤ ((lmax cc c.lo c.hi + c.J : ℚ) : ℝ) := by
        push_cast; rw [← hJdef]; linarith only [l2, hj2.2, hjdef]
      exact_mod_cast this
  have ht2h' : t ^ 2 ≤ (((c.T ^ 2 : ℚ)) : ℝ) := by push_cast; rw [← hTdef]; exact ht2h
  have ht2l' : (((c.t2lo : ℚ)) : ℝ) ≤ t ^ 2 := by rw [← ht2ldef]; exact ht2l
  have ha : a ∈ aRange P c b cc := by
    have l1 := lmin_le (b : ℚ) h1 h2
    have l2 := le_lmax (b : ℚ) h1 h2
    have l3 := lmin_le (cc : ℚ) ht2l' ht2h'
    have l4 := le_lmax (cc : ℚ) ht2l' ht2h'
    push_cast at l1 l2 l3 l4
    apply mem_ints
    · have : ((-1 + lmin b c.lo c.hi / 2 - cc * P + lmin cc c.t2lo (c.T ^ 2) / 2 : ℚ) : ℝ) ≤ (a : ℝ) := by
        push_cast; linarith only [l1, l3, hre3.1, hredef]
      exact_mod_cast this
    · have : (a : ℝ) ≤ ((1 + lmax b c.lo c.hi / 2 - cc * P + lmax cc c.t2lo (c.T ^ 2) / 2 : ℚ) : ℝ) := by
        push_cast; linarith only [l2, l4, hre3.2, hredef]
      exact_mod_cast this
  simp only [slabB, List.all_eq_true, List.mem_range] at hbox
  have ic' := abs_le.mp ic
  have hh := hbox (cc + c.C).toNat (by omega)
  have e3 : ((cc + c.C).toNat : ℤ) - c.C = cc := by omega
  simp only [slabSliceB, e3, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hh
  rcases hh b hb a ha with (hn | hm) | hp
  · exfalso; rcases hv with h | h <;> simp [h] at hn
  · exact hm
  · exfalso
    have := (encl_sound (a, b, cc) h1 h2).2
    have hp' : ((pHi (a, b, cc) c.lo c.hi : ℚ) : ℝ) < 1 := by exact_mod_cast hp
    rw [← hsdef] at this
    linarith only [this, hp', hs1]

/-- **Unit generation**: every `w` with `N(w) = ±1` has `Mx w = ±ηⁿ`. -/
@[nolint unusedHavesSuffices]
theorem units_eq {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} (hc : condB P Q η c = true)
    (hbox : slabB P Q η c = true) (w : Z3) (hw : nrm P Q w = 1 ∨ nrm P Q w = -1) :
    ∃ n : ℤ, Mx P Q w = ((uη P Q η ε h1 h2 ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) ∨
      Mx P Q w = -((uη P Q η ε h1 h2 ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
  have hc' := hc
  simp only [condB, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨hle, hsgn⟩, _⟩, _⟩, _⟩, _⟩, hηlo⟩, _⟩ := hc'
  obtain ⟨t, ht1, ht2, ht⟩ := root_in P Q c.lo c.hi hle hsgn
  set E := sig t η with hE
  have hnear := sig_near η ht1 ht2
  have hE1 : 1 < E := by
    have : ((1 : ℚ) : ℝ) < ((sigQ c.lo η - rad η c.lo c.hi : ℚ) : ℝ) := by exact_mod_cast hηlo
    push_cast at this
    have := (abs_le.mp hnear).1
    linarith
  have hE2 : E ≤ ((c.E η : ℚ) : ℝ) := by
    have := (abs_le.mp hnear).2
    simp only [Cert.E]; push_cast; linarith
  have hs0 : sig t w ≠ 0 := by
    intro h0
    have := norm_split ht w
    rw [h0, zero_mul] at this
    rcases hw with h | h <;> rw [h] at this <;> norm_num at this
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hs0) hE1
  set v := mul P Q w (zp P Q η ε (-n))
  have hsv : sig t v = sig t w * E ^ (-n) := by
    simp only [v]; rw [sig_mul ht, sig_zp ht h1]
  have hEpos : 0 < E := by linarith
  have hv1 : 1 ≤ |sig t v| := by
    rw [hsv, abs_mul, abs_of_pos (zpow_pos hEpos _), zpow_neg]
    rw [le_mul_inv_iff₀ (zpow_pos hEpos _), one_mul]; exact hn1
  have hv2 : |sig t v| ≤ ((c.E η : ℚ) : ℝ) := by
    rw [hsv, abs_mul, abs_of_pos (zpow_pos hEpos _), zpow_neg]
    have : |sig t w| * (E ^ n)⁻¹ < E := by
      rw [mul_inv_lt_iff₀ (zpow_pos hEpos _), ← zpow_one_add₀ hEpos.ne', add_comm]; exact hn2
    linarith
  have hnv : nrm P Q v = 1 ∨ nrm P Q v = -1 := by
    simp only [v]; rw [nrm_mul, nrm_zp P Q hnη hnε, mul_one]; exact hw
  have hmem := reduced_mem hc hbox ht1 ht2 ht v hnv hv1 hv2
  have hMw : Mx P Q w = Mx P Q v * ((uη P Q η ε h1 h2 ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
    simp only [v]
    rw [Mx_mul, Mx_zp P Q η ε h1 h2, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, mul_one]
  have hMη : Mx P Q η = ((uη P Q η ε h1 h2 : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> rw [h] at hMw
  · exact ⟨n, Or.inl (by rw [hMw, Mx_one, one_mul])⟩
  · refine ⟨n, Or.inr ?_⟩
    rw [hMw, show ((-1 : ℤ), (0 : ℤ), (0 : ℤ)) = UnitBox.neg (1, 0, 0) by rfl, Mx_neg, Mx_one, neg_one_mul]
  · refine ⟨n + 1, Or.inl ?_⟩
    rw [hMw, hMη, ← Units.val_mul, (Commute.self_zpow (uη P Q η ε h1 h2) n).eq, ← zpow_add_one]
  · refine ⟨n + 1, Or.inr ?_⟩
    rw [hMw, Mx_neg, neg_mul, hMη, ← Units.val_mul, (Commute.self_zpow (uη P Q η ε h1 h2) n).eq,
      ← zpow_add_one]

/-- **The source theorem**: `−u³ + P u v² + Q v³ = 1` has the single integer solution `(−1, 0)`. -/
theorem source {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} (hc : condB P Q η c = true)
    (hbox : slabB P Q η c = true) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {M M' : ℕ}
    {D D' : Matrix (Fin 3) (Fin 3) ℤ} (hη : SkolemData p M (Mx P Q η) D)
    (hε : SkolemData p M' (Mx P Q ε) D') (u v : ℤ) :
    -u ^ 3 + P * u * v ^ 2 + Q * v ^ 3 = 1 ↔ (u = -1 ∧ v = 0) := by
  constructor
  · intro h
    have hn : nrm P Q (u, -v, 0) = -1 := by simp only [nrm]; linear_combination -h
    obtain ⟨n, hM⟩ := units_eq h1 h2 hnη hnε hc hbox (u, -v, 0) (Or.inr hn)
    have hcol := Mx_col P Q (u, -v, 0)
    simp only at hcol
    have hz : ((uη P Q η ε h1 h2 ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 := by
      rcases hM with hM | hM <;> rw [hM] at hcol
      · exact hcol.2.2
      · simpa using hcol.2.2
    have h0 := corner_eq_zero h1 h2 hp3 hη hε n hz
    subst h0
    simp only [zpow_zero, Units.val_one] at hM
    have hv : v = 0 := by
      rcases hM with hM | hM <;> rw [hM] at hcol <;> simp at hcol <;> omega
    subst hv
    have hu : u ^ 3 = -1 := by linarith
    have : u = -1 := by
      rcases hM with hM | hM <;> rw [hM] at hcol <;> simp at hcol
      · subst hcol; norm_num at hu
      · omega
    exact ⟨this, rfl⟩
  · rintro ⟨rfl, rfl⟩; norm_num

end PerfectPower.RankOne
