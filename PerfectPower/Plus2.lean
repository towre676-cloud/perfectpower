import PerfectPower.UnitGen
import PerfectPower.NormRepProof
import PerfectPower.Skolem3

/-!
# The first irreducible positive-`k` source: `−u³ − 3uv² − 2v³ = 1` only at `(−1, 0)`

The class `F = (−1, 0, −3, −2)` of `y² = x³ + 2` (`positive_k.json`) is `F(u, v) = −N(u − vz)` in
`ℤ[z]`, `z³ = −3z − 2` (one real embedding and a complex pair, unit rank 1).

* **Unit generation** (`units_eq`): every `w` with `N(w) = ±1` has `Mx w = ±ηⁿ` for
  `η = 17 − 3z + 5z²` (`ε = η⁻¹ = 1 + z − z²`).
  - Round with the real embedding: `|σ(w η⁻ⁿ)| ∈ [1, σ(η))` (`exists_mem_Ico_zpow`).
  - Without complex numbers, `N(g) = σ(g)·(re² + κ²j²)` with `κ² = 3ρ²/4 + 3`,
    `re = a − bρ/2 + c(P − ρ²/2)` and `j = b − cρ` (`norm_split`).
  - This bounds the reduced unit to a box, and a kernel check finds only `±1, ±η` there
    (`ε` is excluded by `|σ(ε)| < 1`).
* **Zero set** (`Skolem3.corner_zero`): the `z²` coordinate of `ηⁿ` vanishes only at `n = 0`
  (Skolem's method at `p = 3`, since `η³ ≡ 1` and `ε³ ≡ 1 (mod 3)`).
* **Source theorem** (`source`): `−u³ − 3uv² − 2v³ = 1 ↔ (u, v) = (−1, 0)`.
-/

namespace PerfectPower.Plus2

open PerfectPower UnitBox UnitPremises UnitGenProof NormRepProof Matrix

/-- The order: `z³ = P z + Q`. -/
abbrev P : ℤ := -3
/-- The order: `z³ = P z + Q`. -/
abbrev Q : ℤ := -2
/-- The unit with real embedding `σ(η) ≈ 20.56 > 1`. -/
def η : Z3 := (17, -3, 5)
/-- `ε = η⁻¹ = 1 + z − z²`. -/
def ε : Z3 := (1, 1, -1)

theorem η_ε : mul P Q η ε = (1, 0, 0) := by decide
theorem ε_η : mul P Q ε η = (1, 0, 0) := by decide

/-! ### Multiplication matrices -/

/-- The matrix of multiplication by `g` on the basis `1, z, z²`. -/
def Mx (g : Z3) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j =>
    let c := mul P Q g (if j = 0 then (1, 0, 0) else if j = 1 then (0, 1, 0) else (0, 0, 1))
    if i = 0 then c.1 else if i = 1 then c.2.1 else c.2.2

theorem Mx_mul (g h : Z3) : Mx (mul P Q g h) = Mx g * Mx h := by
  obtain ⟨a, b, c⟩ := g
  obtain ⟨d, e, f⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mx, mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem Mx_one : Mx (1, 0, 0) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mx, mul]

theorem Mx_neg (g : Z3) : Mx (UnitBox.neg g) = -Mx g := by
  obtain ⟨a, b, c⟩ := g
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mx, mul, UnitBox.neg] <;> ring

theorem Mx_corner (g : Z3) : Mx g 2 0 = g.2.2 := by
  obtain ⟨a, b, c⟩ := g
  simp [Mx, mul]

theorem Mx_pow (g : Z3) : ∀ n : ℕ, Mx (pow P Q g n) = Mx g ^ n
  | 0 => by simp [pow, Mx_one]
  | n + 1 => by rw [pow, Mx_mul, Mx_pow g n, pow_succ]

/-- `η` as a unit of the matrix ring. -/
def uη : (Matrix (Fin 3) (Fin 3) ℤ)ˣ :=
  ⟨Mx η, Mx ε, by rw [← Mx_mul, η_ε, Mx_one], by rw [← Mx_mul, ε_η, Mx_one]⟩

theorem Mx_zp (e : ℤ) : Mx (zp P Q η ε e) = ((uη ^ e : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
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

theorem Mη_cube : Mx η ^ 3 = 1 + 3 • !![2392, -1426, 850; -425, 253, -151; 713, -425, 253] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem Mε_cube : Mx ε ^ 3 = 1 + 3 • !![8, 10, -22; 11, 23, -23; -5, 11, 23] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- **The `z²` coordinate of `ηⁿ` vanishes only at `n = 0`.** -/
theorem corner_eq_zero (n : ℤ) (h : ((uη ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0) :
    n = 0 := by
  rcases le_or_lt 0 n with hn | hn
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at h
    have := Skolem3.corner_zero (A := Mx η) Mη_cube (by decide) (by decide) (by decide) N h
    simp [this]
  · exfalso
    obtain ⟨N, hN⟩ : ∃ N : ℕ, n = -((N : ℕ) : ℤ) ∧ 0 < N := ⟨(-n).toNat, by omega, by omega⟩
    rw [hN.1, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at h
    have := Skolem3.corner_zero (A := Mx ε) Mε_cube (by decide) (by decide) (by decide) N h
    omega

/-! ### Unit generation -/

/-- The bracket of the real root `ρ` of `z³ + 3z + 2`. -/
def lo : ℚ := -5961 / 10000
/-- The bracket of the real root. -/
def hi : ℚ := -5960 / 10000

theorem root : ∃ t : ℝ, (lo : ℝ) ≤ t ∧ t ≤ hi ∧ t ^ 3 = (P : ℝ) * t + Q :=
  root_in P Q lo hi (by norm_num [lo, hi]) (by norm_num [cub, lo, hi, P, Q])

/-- **The norm without complex numbers**: `N(g) = σ(g) (re² + κ² j²)`, `κ² = 3ρ²/4 + 3`. -/
theorem norm_split {t : ℝ} (ht : t ^ 3 = (P : ℝ) * t + Q) (g : Z3) :
    (nrm P Q g : ℝ) = sig t g * ((g.1 - g.2.1 * t / 2 + g.2.2 * (-3 - t ^ 2 / 2)) ^ 2 +
      (3 * t ^ 2 / 4 + 3) * (g.2.1 - g.2.2 * t) ^ 2) := by
  obtain ⟨a, b, c⟩ := g
  simp only [nrm, sig, P, Q] at ht ⊢
  push_cast at ht ⊢
  linear_combination (2 * c ^ 3 - 3 * c ^ 3 * t - c ^ 3 * t ^ 3 - 3 * b * c ^ 2 - b ^ 3 + 3 * a * b * c) * ht

lemma nrm_pow (x : Z3) (hx : nrm P Q x = 1) : ∀ k : ℕ, nrm P Q (pow P Q x k) = 1
  | 0 => by simp [pow, nrm, P, Q]
  | k + 1 => by rw [pow, nrm_mul, nrm_pow x hx k, hx]; rfl

lemma nrm_zp (e : ℤ) : nrm P Q (zp P Q η ε e) = 1 := by
  unfold zp
  split_ifs
  · exact nrm_pow η (by decide) _
  · exact nrm_pow ε (by decide) _

/-- The box of reduced units. -/
def boxB : Bool :=
  (List.range 49).all fun i => (List.range 7).all fun j => (List.range 11).all fun l =>
    let g : Z3 := ((i : ℤ) - 24, (j : ℤ) - 3, (l : ℤ) - 5)
    decide (nrm P Q g ≠ 1 ∧ nrm P Q g ≠ -1) ||
      decide (g ∈ [((1 : ℤ), (0 : ℤ), (0 : ℤ)), (-1, 0, 0), η, UnitBox.neg η]) || decide (pHi g lo hi < 1)

theorem box_ok : boxB = true := by decide +kernel

set_option maxHeartbeats 1000000 in
/-- **The reduced unit is `±1` or `±η`.** -/
theorem reduced_mem {t : ℝ} (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ hi) (ht : t ^ 3 = (P : ℝ) * t + Q) (v : Z3)
    (hv : nrm P Q v = 1 ∨ nrm P Q v = -1) (hs1 : 1 ≤ |sig t v|) (hs2 : |sig t v| ≤ 2057 / 100) :
    v ∈ [((1 : ℤ), (0 : ℤ), (0 : ℤ)), (-1, 0, 0), η, UnitBox.neg η] := by
  obtain ⟨a, b, c⟩ := v
  have hsplit := norm_split ht (a, b, c)
  simp only at hsplit
  obtain ⟨s, hsdef⟩ : ∃ s, s = sig t (a, b, c) := ⟨_, rfl⟩
  obtain ⟨re, hredef⟩ : ∃ re, re = (a : ℝ) - b * t / 2 + c * (-3 - t ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ j, j = (b : ℝ) - c * t := ⟨_, rfl⟩
  rw [← hsdef, ← hredef, ← hjdef] at hsplit
  rw [← hsdef] at hs1 hs2
  have hk0 : 0 ≤ (3 * t ^ 2 / 4 + 3) * j ^ 2 := by positivity
  have hG0 : 0 ≤ re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2 := by positivity
  have hsG : |s| * (re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2) = 1 := by
    have : |s * (re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2)| = 1 := by
      rw [← hsplit]; rcases hv with h | h <;> rw [h] <;> simp
    rwa [abs_mul, abs_of_nonneg hG0] at this
  have hGle : re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2 ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : 1 < |s| * (re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2) := by
      calc (1 : ℝ) < re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2 := hc
        _ = 1 * (re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2) := (one_mul _).symm
        _ ≤ |s| * (re ^ 2 + (3 * t ^ 2 / 4 + 3) * j ^ 2) := mul_le_mul_of_nonneg_right hs1 hG0
    linarith
  have elo : ((lo : ℚ) : ℝ) = -5961 / 10000 := by norm_num [lo]
  have ehi : ((hi : ℚ) : ℝ) = -5960 / 10000 := by norm_num [hi]
  have hl : (-5961 / 10000 : ℝ) ≤ t := by linarith
  have hh : t ≤ (-5960 / 10000 : ℝ) := by linarith
  have hre : re ^ 2 ≤ 1 := by linarith
  have hj : j ^ 2 ≤ 1 / 3 := by
    have e : (3 * t ^ 2 / 4 + 3) * j ^ 2 = 3 * t ^ 2 / 4 * j ^ 2 + 3 * j ^ 2 := by ring
    have : 0 ≤ 3 * t ^ 2 / 4 * j ^ 2 := by positivity
    have : 0 ≤ re ^ 2 := sq_nonneg _
    linarith
  have hre' : |re| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hre
  have hj' : |j| ≤ 3 / 5 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (j - 3 / 5), sq_nonneg (j + 3 / 5)]
  have hs' : |s| ≤ 2057 / 100 := hs2
  -- invert: c (3t² + 3) = s − re − (3t/2) j, b = j + c t, a = s − b t − c t²
  have ec : (c : ℝ) * (3 * t ^ 2 + 3) = s - re - 3 * t / 2 * j := by
    rw [hsdef, hredef, hjdef]; simp only [sig]; ring
  have eb : (b : ℝ) = j + c * t := by rw [hjdef]; ring
  have ea : (a : ℝ) = s - b * t - c * t ^ 2 := by rw [hsdef]; simp only [sig]; ring
  have hnt1 : (5960 / 10000 : ℝ) ≤ -t := by linarith
  have hnt2 : -t ≤ (5961 / 10000 : ℝ) := by linarith
  have et : t ^ 2 = (-t) * (-t) := by ring
  have ht2 : (355 / 1000 : ℝ) ≤ t ^ 2 := by
    rw [et]
    calc (355 / 1000 : ℝ) ≤ (5960 / 10000) * (5960 / 10000) := by norm_num
      _ ≤ (-t) * (-t) := mul_le_mul hnt1 hnt1 (by norm_num) (by linarith)
  have ht2' : t ^ 2 ≤ (3554 / 10000 : ℝ) := by
    rw [et]
    calc (-t) * (-t) ≤ (5961 / 10000) * (5961 / 10000) := mul_le_mul hnt2 hnt2 (by linarith) (by norm_num)
      _ ≤ (3554 / 10000 : ℝ) := by norm_num
  have hta : |t| ≤ 5961 / 10000 := by rw [abs_le]; constructor <;> linarith
  have htj : |t| * |j| ≤ 5961 / 10000 * (3 / 5) := mul_le_mul hta hj' (abs_nonneg j) (by norm_num)
  have hc : |(c : ℝ)| < 6 := by
    have hden : (4065 / 1000 : ℝ) ≤ 3 * t ^ 2 + 3 := by linarith
    have h3 : |3 * t / 2 * j| = 3 / 2 * (|t| * |j|) := by
      rw [abs_mul, abs_div, abs_mul]; norm_num; ring
    have hnum : |s - re - 3 * t / 2 * j| ≤ 2057 / 100 + 1 + 3 / 2 * (5961 / 10000 * (3 / 5)) := by
      have e1 := abs_sub (s - re) (3 * t / 2 * j)
      have e2 := abs_sub s re
      linarith only [e1, e2, h3, htj, hs', hre']
    have hpos : (0 : ℝ) < 3 * t ^ 2 + 3 := by positivity
    have hcabs : |(c : ℝ) * (3 * t ^ 2 + 3)| = |(c : ℝ)| * (3 * t ^ 2 + 3) := by
      rw [abs_mul, abs_of_pos hpos]
    rw [ec] at hcabs
    have hm := mul_le_mul_of_nonneg_left hden (abs_nonneg (c : ℝ))
    linarith only [hcabs, hnum, hm]
  have ic : |c| ≤ 5 := by
    have : |c| < 6 := by exact_mod_cast hc
    omega
  have icR : |(c : ℝ)| ≤ 5 := by exact_mod_cast ic
  have hct : |(c : ℝ)| * |t| ≤ 5 * (5961 / 10000) := mul_le_mul icR hta (abs_nonneg t) (by norm_num)
  have hb : |(b : ℝ)| < 4 := by
    rw [eb]
    have : |j + c * t| ≤ |j| + |(c : ℝ)| * |t| := by rw [← abs_mul]; exact abs_add_le _ _
    linarith only [this, hj', hct]
  have ib : |b| ≤ 3 := by
    have : |b| < 4 := by exact_mod_cast hb
    omega
  have ibR : |(b : ℝ)| ≤ 3 := by exact_mod_cast ib
  have hbt : |(b : ℝ)| * |t| ≤ 3 * (5961 / 10000) := mul_le_mul ibR hta (abs_nonneg t) (by norm_num)
  have hct2 : |(c : ℝ)| * t ^ 2 ≤ 5 * (3554 / 10000) := mul_le_mul icR ht2' (sq_nonneg t) (by norm_num)
  have ha : |(a : ℝ)| < 25 := by
    rw [ea]
    have h1' := abs_sub (s - b * t) (c * t ^ 2)
    have h2' := abs_sub s (b * t)
    rw [abs_mul (b : ℝ) t] at h2'
    rw [abs_mul (c : ℝ) (t ^ 2), abs_of_nonneg (sq_nonneg t)] at h1'
    linarith only [h1', h2', hs', hbt, hct2]
  have ia : |a| ≤ 24 := by
    have : |a| < 25 := by exact_mod_cast ha
    omega
  have hbox := box_ok
  simp only [boxB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hbox
  have ia' := abs_le.mp ia
  have ib' := abs_le.mp ib
  have ic' := abs_le.mp ic
  have hh := hbox (a + 24).toNat (by omega) (b + 3).toNat (by omega) (c + 5).toNat (by omega)
  have e1 : ((a + 24).toNat : ℤ) - 24 = a := by omega
  have e2 : ((b + 3).toNat : ℤ) - 3 = b := by omega
  have e3 : ((c + 5).toNat : ℤ) - 5 = c := by omega
  simp only [e1, e2, e3] at hh
  rcases hh with (hn | hm) | hp
  · exfalso; rcases hv with h | h <;> simp [h] at hn
  · exact hm
  · exfalso
    have := (encl_sound (a, b, c) h1 h2).2
    have hp' : ((pHi (a, b, c) lo hi : ℚ) : ℝ) < 1 := by exact_mod_cast hp
    rw [← hsdef] at this
    linarith only [this, hp', hs1]

/-- **Unit generation**: every `w` with `N(w) = ±1` has `Mx w = ±ηⁿ`. -/
theorem units_eq (w : Z3) (hw : nrm P Q w = 1 ∨ nrm P Q w = -1) :
    ∃ n : ℤ, Mx w = ((uη ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) ∨
      Mx w = -((uη ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
  obtain ⟨t, h1, h2, ht⟩ := root
  have elo : ((lo : ℚ) : ℝ) = -5961 / 10000 := by norm_num [lo]
  have ehi : ((hi : ℚ) : ℝ) = -5960 / 10000 := by norm_num [hi]
  have hl : (-5961 / 10000 : ℝ) ≤ t := by linarith
  have hh : t ≤ (-5960 / 10000 : ℝ) := by linarith
  set E := sig t η with hE
  have hE1 : 1 < E := by simp only [hE, sig, η]; push_cast; nlinarith
  have hE2 : E ≤ 2057 / 100 := by simp only [hE, sig, η]; push_cast; nlinarith
  have hs0 : sig t w ≠ 0 := by
    intro h0
    have := norm_split ht w
    rw [h0, zero_mul] at this
    rcases hw with h | h <;> rw [h] at this <;> norm_num at this
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hs0) hE1
  set v := mul P Q w (zp P Q η ε (-n))
  have hsv : sig t v = sig t w * E ^ (-n) := by
    simp only [v]; rw [sig_mul ht, sig_zp ht η_ε]
  have hEpos : 0 < E := by linarith
  have hv1 : 1 ≤ |sig t v| := by
    rw [hsv, abs_mul, abs_of_pos (zpow_pos hEpos _), zpow_neg]
    rw [le_mul_inv_iff₀ (zpow_pos hEpos _), one_mul]; exact hn1
  have hv2 : |sig t v| ≤ 2057 / 100 := by
    rw [hsv, abs_mul, abs_of_pos (zpow_pos hEpos _), zpow_neg]
    have : |sig t w| * (E ^ n)⁻¹ < E := by
      rw [mul_inv_lt_iff₀ (zpow_pos hEpos _), ← zpow_one_add₀ hEpos.ne', add_comm]; exact hn2
    linarith
  have hnv : nrm P Q v = 1 ∨ nrm P Q v = -1 := by
    simp only [v]; rw [nrm_mul, nrm_zp, mul_one]; exact hw
  have hmem := reduced_mem h1 h2 ht v hnv hv1 hv2
  -- Mx w = Mx v · ηⁿ
  have hMw : Mx w = Mx v * ((uη ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
    simp only [v]
    rw [Mx_mul, Mx_zp, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      mul_one]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> rw [h] at hMw
  · exact ⟨n, Or.inl (by rw [hMw, Mx_one, one_mul])⟩
  · refine ⟨n, Or.inr ?_⟩
    rw [hMw, show ((-1 : ℤ), (0 : ℤ), (0 : ℤ)) = UnitBox.neg (1, 0, 0) by rfl, Mx_neg, Mx_one, neg_one_mul]
  · refine ⟨n + 1, Or.inl ?_⟩
    rw [hMw, show Mx η = ((uη : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) from rfl,
      ← Units.val_mul, (Commute.self_zpow uη n).eq, ← zpow_add_one]
  · refine ⟨n + 1, Or.inr ?_⟩
    rw [hMw, Mx_neg, neg_mul, show Mx η = ((uη : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) from rfl,
      ← Units.val_mul, (Commute.self_zpow uη n).eq, ← zpow_add_one]

end PerfectPower.Plus2
