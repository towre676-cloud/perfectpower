import PerfectPower.NormForm
import PerfectPower.Generated.D72Unit

/-!
# The `D = 72` residual unit equation, under three named premises

`H(u, v) = −3u³ + 9uv² − 2v³ = ±1` (`MORDELL_BRANCH.md` §7.1; `NormForm.H72`).  In `ℤ[δ]`,
`δ³ = 9δ + 6`, the element `γ = −3u − βv` is `(−3u − 6v) + v δ²` (`NormForm.d72_gamma_delta`), of
norm `9 H(u, v)`.

* **Premises** (`Generated/D72Unit.lean`, statements in `UnitPremises`), not proved in Lean:
  - `unitGen`: the units of `ℤ[δ]` are `±ε₁^a ε₂^b`, with `ε₁ = δ² − 3δ − 1`, `ε₂ = 2δ² − 1`
    (evidence: the exact fundamental-domain witness, whose finite part is `D72Unit.unit_box`);
  - `normRep_pos`, `normRep_neg`: the elements of norm `±9` are `±α` times units, `α = δ² − 3δ − 3`
    (evidence: `(3) = 𝔭³` is totally ramified and `ℤ[δ]` is 3-maximal);
  - `analytic_pos`, `analytic_neg`: Siegel's identity, the conjugate estimates and Matveev's theorem.
* **Checked by the kernel:** the direct-`H` reduction chains (to `|eᵢ| ≤ 4`), the box of `9²`
  elements of either sign, and the search `|v| ≤ 1`.
* `small_v`: no solution has `|v| ≤ 1` (proved outright).
* `residual_empty`: **under the premises, `H(u, v) ≠ ±1` for all integers `u, v`.**
-/

namespace PerfectPower.D72Residual

open PerfectPower NormForm ThueLocal

lemma H72_eq (u v : ℤ) : H72 u v = evalF (-3, 0, 9, -2) u v := by
  simp only [H72, evalF]; ring

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

/-- **The residual unit equation has no solution, under the three premises.** -/
theorem residual_empty (hU : Generated.D72Unit.unitGen)
    (hNp : Generated.D72Unit.normRep_pos) (hNn : Generated.D72Unit.normRep_neg)
    (hAp : Generated.D72Unit.analytic_pos) (hAn : Generated.D72Unit.analytic_neg) (u v : ℤ) :
    H72 u v ≠ 1 ∧ H72 u v ≠ -1 := by
  rw [H72_eq]
  constructor <;> intro h
  · simpa using (Generated.D72Unit.class_pos hU hNp hAp u v).mp h
  · simpa using (Generated.D72Unit.class_neg hU hNn hAn u v).mp h

end PerfectPower.D72Residual
