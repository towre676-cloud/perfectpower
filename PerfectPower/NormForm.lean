import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The nonmonic norm-form identity behind the Thue obligations

For `F(a, b) = c₀ a³ + c₁ a² b + c₂ a b² + c₃ b³` with `c₀ ≠ 0`, let `θ` be a root of `F(T, 1)` and
`β = c₀ θ`.  Then `β` is a root of the **monic** integral cubic
`g(X) = X³ + c₁ X² + c₀ c₂ X + c₀² c₃`, so it is integral even when `F` is not monic.  Put
`γ = c₀ a − β b`.

* `mulMat_spec`: in **any** commutative ring containing a root `β` of `g`, multiplication by `γ`
  acts on `(1, β, β²)` by the matrix `mulMat`.  So `mulMat` is the multiplication matrix.
* `det_mulMat`: `det (mulMat) = c₀² F(a, b)`, an exact polynomial identity.

Together these give `N_{ℚ(β)/ℚ}(γ) = c₀² F(a, b)`, because the norm is the determinant of the
multiplication matrix on a basis.  That standard step is not instantiated here.  Consequently
`F(a, b) = M` holds iff `N(γ) = c₀² M`, with `γ` in the lattice `c₀ ℤ + β ℤ`: a nonmonic Thue
equation is a *scaled* norm equation **plus** a lattice condition.

`D = 72` (the residual unit equation `H(u, v) = −3u³ + 9uv² − 2v³ = ±1`, `MORDELL_BRANCH.md` §7.1):
* `d72_det`: `det = 9 H(u, v)`, so `N(γ) = ±9` with `β³ − 27β − 18 = 0` and `γ = −3u − βv`;
* `d72_no_int_root`: `X³ − 27X − 18` has no integer root (none modulo 5), hence no rational root
  (the rational-root theorem for a monic integral polynomial, not formalized here).  A cubic with
  no rational root is irreducible over ℚ;
* `d72_disc`: the polynomial discriminant is `69984 > 0`, so the field is totally real with unit
  rank 2.  The field discriminant needs the maximal order; PARI gives 1944.

The missing global theorem is a bound on the unit exponents of `γ` (Baker-type, then reduction).
It is **not** proved here.
-/

namespace PerfectPower.NormForm

open Matrix

/-- The matrix of multiplication by `γ = c₀ a − β b` on the basis `(1, β, β²)`, where
`β³ = −c₁ β² − c₀ c₂ β − c₀² c₃` (columns are the images of the basis vectors). -/
def mulMat (c0 c1 c2 c3 a b : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![c0 * a, 0, b * c0 ^ 2 * c3;
     -b, c0 * a, b * c0 * c2;
     0, -b, c0 * a + b * c1]

/-- **`mulMat` is the multiplication matrix**, in any commutative ring with a root of `g`. -/
theorem mulMat_spec {R : Type*} [CommRing R] (c0 c1 c2 c3 a b : ℤ) (β : R)
    (hβ : β ^ 3 + (c1 : R) * β ^ 2 + (c0 : R) * c2 * β + (c0 : R) ^ 2 * c3 = 0) :
    let γ : R := (c0 : R) * a - β * b
    let M := mulMat c0 c1 c2 c3 a b
    ∀ j : Fin 3, γ * β ^ (j : ℕ) = (M 0 j : R) + (M 1 j : R) * β + (M 2 j : R) * β ^ 2 := by
  intro γ M j
  fin_cases j <;> simp [γ, M, mulMat]
  · ring
  · ring
  · linear_combination (-(b : R)) * hβ

/-- **The norm-form identity**: `det (mulMat) = c₀² F(a, b)`. -/
theorem det_mulMat (c0 c1 c2 c3 a b : ℤ) :
    (mulMat c0 c1 c2 c3 a b).det = c0 ^ 2 * (c0 * a ^ 3 + c1 * a ^ 2 * b + c2 * a * b ^ 2 + c3 * b ^ 3) := by
  simp [mulMat, det_fin_three]
  ring

/-- The `D = 72` residual form. -/
def H72 (u v : ℤ) : ℤ := -3 * u ^ 3 + 9 * u * v ^ 2 - 2 * v ^ 3

/-- `D = 72`: `β³ − 27β − 18 = 0`, `γ = −3u − βv`, and `N(γ) = det = 9 H(u, v)`. -/
theorem d72_det (u v : ℤ) : (mulMat (-3) 0 9 (-2) u v).det = 9 * H72 u v := by
  rw [det_mulMat, H72]
  ring

/-- The `D = 72` multiplication matrix, explicitly. -/
theorem d72_mulMat (u v : ℤ) :
    mulMat (-3) 0 9 (-2) u v = !![-3 * u, 0, -18 * v; -v, -3 * u, -27 * v; 0, -v, -3 * u] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mulMat] <;> ring

/-- `X³ + 3X + 2` has no root modulo 5. -/
theorem d72_no_root_mod5 : ∀ x : ZMod 5, x ^ 3 + 3 * x + 2 ≠ 0 := by decide

/-- **`X³ − 27X − 18` has no integer root** (it would give a root of `X³ + 3X + 2` mod 5). -/
theorem d72_no_int_root (x : ℤ) : x ^ 3 - 27 * x - 18 ≠ 0 := by
  intro h
  have h5 : ((x ^ 3 - 27 * x - 18 : ℤ) : ZMod 5) = 0 := by rw [h]; simp
  push_cast at h5
  apply d72_no_root_mod5 (x : ZMod 5)
  have e27 : (27 : ZMod 5) = -3 := by decide
  have e18 : (18 : ZMod 5) = -2 := by decide
  rw [e27, e18] at h5
  linear_combination h5

/-- The polynomial discriminant of `X³ − 27X − 18` is `−4(−27)³ − 27(−18)² = 69984 > 0`. -/
theorem d72_disc : -4 * (-27 : ℤ) ^ 3 - 27 * (-18) ^ 2 = 69984 := by norm_num

/-! ### `D = 72` in the integral basis `(1, δ, δ²)`, `δ³ = 9δ + 6`

`δ = (β² − 3β − 18)/6` satisfies `δ³ − 9δ − 6 = 0`, and `β = 6 − δ²`.  In this basis the residual
lattice is simple: `γ = −3u − βv = (−3u − 6v) + v δ²`, so `γ = A + Bδ + Cδ²` lies in the lattice
iff `B = 0` and `3 ∣ A`, and then `u = −A/3 − 2C`, `v = C`.  The pilot's units and norm-9 element
are `ε₁ = δ² − 3δ − 1`, `ε₂ = 2δ² − 1` (norm `−1`) and `α = δ² − 3δ − 3` (norm `9`).  That
`ε₁, ε₂` generate the unit group, and that every solution has bounded exponents, is **not**
proved here. -/

/-- Multiplication by `A + Bδ + Cδ²` on `(1, δ, δ²)` when `δ³ = pδ + q`. -/
def mulD (p q A B C : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![A, C * q, B * q;
     B, A + C * p, C * q + B * p;
     C, B, A + C * p]

/-- `mulD` is the multiplication matrix, in any commutative ring with `δ³ = pδ + q`. -/
theorem mulD_spec {R : Type*} [CommRing R] (p q A B C : ℤ) (δ : R)
    (hδ : δ ^ 3 = (p : R) * δ + q) :
    let x : R := (A : R) + B * δ + C * δ ^ 2
    let M := mulD p q A B C
    ∀ j : Fin 3, x * δ ^ (j : ℕ) = (M 0 j : R) + (M 1 j : R) * δ + (M 2 j : R) * δ ^ 2 := by
  intro x M j
  fin_cases j <;> simp [x, M, mulD] <;>
    first
    | linear_combination (C : R) * hδ
    | linear_combination ((B : R) + C * δ) * hδ

/-- `β = 6 − δ²` is a root of `X³ − 27X − 18` whenever `δ³ − 9δ − 6 = 0`. -/
theorem d72_beta_of_delta {R : Type*} [CommRing R] (δ : R) (hδ : δ ^ 3 - 9 * δ - 6 = 0) :
    (6 - δ ^ 2) ^ 3 - 27 * (6 - δ ^ 2) - 18 = 0 := by
  linear_combination (-δ ^ 3 + 9 * δ - 6) * hδ

/-- `γ = −3u − βv` in the `δ` basis. -/
theorem d72_gamma_delta {R : Type*} [CommRing R] (δ : R) (u v : ℤ) :
    -3 * (u : R) - (6 - δ ^ 2) * v = ((-3 * u - 6 * v : ℤ) : R) + ((0 : ℤ) : R) * δ + ((v : ℤ) : R) * δ ^ 2 := by
  push_cast; ring

/-- **The lattice in `δ` coordinates**: `A + Bδ + Cδ²` is some `−3u − βv` iff `B = 0` and `3 ∣ A`;
then `u = −A/3 − 2C` and `v = C`. -/
theorem d72_lattice (A B C : ℤ) :
    (∃ u v : ℤ, A = -3 * u - 6 * v ∧ B = 0 ∧ C = v) ↔ B = 0 ∧ 3 ∣ A := by
  constructor
  · rintro ⟨u, v, rfl, rfl, -⟩
    exact ⟨rfl, ⟨-u - 2 * v, by ring⟩⟩
  · rintro ⟨rfl, k, rfl⟩
    exact ⟨-k - 2 * C, C, by ring, rfl, rfl⟩

/-- The two bases agree on the norm: `det = 9 H(u, v)` in `δ` coordinates too. -/
theorem d72_det_delta (u v : ℤ) : (mulD 9 6 (-3 * u - 6 * v) 0 v).det = 9 * H72 u v := by
  simp [mulD, det_fin_three, H72]
  ring

/-- `N(ε₁) = −1` for `ε₁ = δ² − 3δ − 1`. -/
theorem d72_norm_eps1 : (mulD 9 6 (-1) (-3) 1).det = -1 := by
  simp [mulD, det_fin_three]

/-- `N(ε₂) = −1` for `ε₂ = 2δ² − 1`. -/
theorem d72_norm_eps2 : (mulD 9 6 (-1) 0 2).det = -1 := by
  simp [mulD, det_fin_three]

/-- `N(α) = 9` for `α = δ² − 3δ − 3`. -/
theorem d72_norm_alpha : (mulD 9 6 (-3) (-3) 1).det = 9 := by
  simp [mulD, det_fin_three]

end PerfectPower.NormForm
