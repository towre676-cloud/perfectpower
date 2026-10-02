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

end PerfectPower.Plus2
