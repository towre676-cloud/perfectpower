import PerfectPower.NormForm

/-!
# The `D = 72` residual unit equation, under a named external bound

`H(u, v) = −3u³ + 9uv² − 2v³ = ±1` (`MORDELL_BRANCH.md` §7.1; `NormForm.H72`).  In `ℤ[δ]`,
`δ³ = 9δ + 6`, the element `γ = −3u − βv` is `(−3u − 6v) + v δ²` (`NormForm.d72_gamma_delta`).

* **The external certificate, as a hypothesis** (`ExtBound`): every solution with `|v| > V` has
  `γ = ±α ε₁^{e₁} ε₂^{e₂}` with `|eᵢ| ≤ B`.  It rests on three things outside Lean:
  - PARI's certified unit group and norm-9 ideal: `h = 1`, `ε₁, ε₂` fundamental, `(α) = 𝔭²`;
  - Matveev's lower bound for linear forms in logarithms;
  - the interval reduction in `crosscheck/thue_bound_d72.py` (`receipts/d72_thue_bound.json`), which
    gives `B = 35` and `V = 1`.
* **Checked here, by the kernel:** `box_ok`.  None of the `71 × 71` products `α ε₁^{e₁} ε₂^{e₂}`,
  `|eᵢ| ≤ 35`, lies in the lattice `B = 0 ∧ 3 ∣ A` (`NormForm.d72_lattice`), and negation does not
  change that.
* `small_v`: no solution has `|v| ≤ 1`.
* `residual_empty`: **under `ExtBound 35 1`, `H(u, v) ≠ ±1` for all integers `u, v`.**
-/

namespace PerfectPower.D72Residual

open PerfectPower NormForm

/-- Elements of `ℤ[δ]` as coordinates `(A, B, C) = A + Bδ + Cδ²`. -/
abbrev Z3 := ℤ × ℤ × ℤ

/-- Multiplication in `ℤ[δ]`, `δ³ = 9δ + 6` (the matrix `NormForm.mulD 9 6`). -/
def mul (x y : Z3) : Z3 :=
  let (a, b, c) := x
  let (d, e, f) := y
  -- (a + bδ + cδ²)(d + eδ + fδ²); δ³ = 9δ + 6, δ⁴ = 9δ² + 6δ
  let c0 := a * d
  let c1 := a * e + b * d
  let c2 := a * f + b * e + c * d
  let c3 := b * f + c * e
  let c4 := c * f
  (c0 + 6 * c3, c1 + 9 * c3 + 6 * c4, c2 + 9 * c4)

def eps1 : Z3 := (-1, -3, 1)
def eps2 : Z3 := (-1, 0, 2)
def alpha : Z3 := (-3, -3, 1)

/-- The inverses, from the adjugate (the units have norm `−1`). -/
def eps1inv : Z3 := (-1, -3, -1)
def eps2inv : Z3 := (-289, -24, 34)

theorem eps1_inv : mul eps1 eps1inv = (1, 0, 0) := by decide
theorem eps2_inv : mul eps2 eps2inv = (1, 0, 0) := by decide

/-- `x^k` in `ℤ[δ]`. -/
def pow (x : Z3) : ℕ → Z3
  | 0 => (1, 0, 0)
  | k + 1 => mul (pow x k) x

/-- `ε^e` for `e ∈ [−B, B]`, indexed by `i = e + B`. -/
def zpow (x xinv : Z3) (B i : ℕ) : Z3 := if B ≤ i then pow x (i - B) else pow xinv (B - i)

/-- The candidate family `α ε₁^{e₁} ε₂^{e₂}`, `|eᵢ| ≤ B`. -/
def fam (B : ℕ) : List Z3 :=
  (List.range (2 * B + 1)).flatMap fun i =>
    (List.range (2 * B + 1)).map fun j => mul (mul alpha (zpow eps1 eps1inv B i)) (zpow eps2 eps2inv B j)

/-- The lattice test of `NormForm.d72_lattice`. -/
def inLattice (g : Z3) : Bool := decide (g.2.1 = 0 ∧ g.1 % 3 = 0)

/-- **The kernel-checked box:** no candidate (of either sign) lies in the lattice. -/
theorem box_ok : ((fam 35).all fun g => !inLattice g) = true := by decide +kernel

/-- `γ = −3u − βv` in `δ` coordinates. -/
def gamma (u v : ℤ) : Z3 := (-3 * u - 6 * v, 0, v)

/-- **The external certificate**, as an explicit hypothesis. -/
def ExtBound (B V : ℕ) : Prop :=
  ∀ u v : ℤ, (H72 u v = 1 ∨ H72 u v = -1) → (V : ℤ) < |v| →
    gamma u v ∈ fam B ∨ (-(gamma u v).1, -(gamma u v).2.1, -(gamma u v).2.2) ∈ fam B

/-- No solution has `|v| ≤ 1`. -/
theorem small_v (u v : ℤ) (hv : |v| ≤ 1) : H72 u v ≠ 1 ∧ H72 u v ≠ -1 := by
  have h1 : -1 ≤ v ∧ v ≤ 1 := abs_le.mp hv
  obtain ⟨hl, hh⟩ := h1
  interval_cases v <;> simp only [H72] <;> constructor <;> intro h
  all_goals
    first
    | omega
    | (have hu : -2 ≤ u ∧ u ≤ 2 := by constructor <;> nlinarith [sq_nonneg u, sq_nonneg (u - 2), sq_nonneg (u + 2)]
       obtain ⟨hu1, hu2⟩ := hu
       interval_cases u <;> omega)

/-- **The residual unit equation has no solution, under the external bound.** -/
theorem residual_empty (hB : ExtBound 35 1) (u v : ℤ) : H72 u v ≠ 1 ∧ H72 u v ≠ -1 := by
  by_cases hv : |v| ≤ 1
  · exact small_v u v hv
  · push_neg at hv
    constructor <;> intro h
    all_goals
      have hm := hB u v (by first | exact Or.inl h | exact Or.inr h) (by exact_mod_cast hv)
      have hbox := box_ok
      simp only [List.all_eq_true, Bool.not_eq_true'] at hbox
      rcases hm with hm | hm
      · have := hbox _ hm
        simp [inLattice, gamma] at this
        omega
      · have := hbox _ hm
        simp [inLattice, gamma] at this
        omega

end PerfectPower.D72Residual
