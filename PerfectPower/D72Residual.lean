import PerfectPower.NormForm
import PerfectPower.Generated.D72Unit

/-!
# The `D = 72` residual unit equation, under Matveev's bound

`H(u, v) = −3u³ + 9uv² − 2v³ = ±1` (`MORDELL_BRANCH.md` §7.1; `NormForm.H72`).  In `ℤ[δ]`,
`δ³ = 9δ + 6`, the element `γ = −3u − βv` is `(−3u − 6v) + v δ²` (`NormForm.d72_gamma_delta`), of
norm `9 H(u, v)`.

* **Proved:** `D72Unit.unitGen_proved`, the units of `ℤ[δ]` are `±ε₁^a ε₂^b`, with
  `ε₁ = δ² − 3δ − 1`, `ε₂ = 2δ² − 1` (`UnitGenProof.unitGen_of_cert`, certificate checked by the
  kernel).
* **Proved:** `D72Unit.normRep_pos_proved`, the elements of norm `9` are `α` times units,
  `α = δ² − 3δ − 3`: `9 ∣ N(g)` forces `3 ∣ A, B`, and `g / α` is integral
  (`NormRepProof.normRep_d72`).
* **Proved:** `D72Unit.analytic_pos_proved`, the analytic statement, from Matveev's bound
  (`AnalyticBridge.analytic_of_cert`: Siegel's identity, the conjugate estimates, the inverse log
  matrix, the Matveev cutoff and a kernel-checked interval certificate).  The target `H = −1` reuses
  it, transported by sign (`UnitPremises.analytic_neg_of`).
* **Premise** (`Generated/D72Unit.lean`), not proved in Lean: `matveev_pos`, Matveev's lower bound
  for the three linear forms (`AnalyticBridge.MatveevCase`).
* **Checked by the kernel:** the direct-`H` reduction chains (to `|eᵢ| ≤ 4`), the box of `9²`
  elements of either sign, and the search `|v| ≤ 1`.
* `small_v`: no solution has `|v| ≤ 1` (proved outright).
* `residual_empty`: **under Matveev's bound, `H(u, v) ≠ ±1` for all integers `u, v`.**
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

/-- **The residual unit equation has no solution, under Matveev's bound.**  Unit generation
(`Generated.D72Unit.unitGen_proved`), the norm representatives
(`Generated.D72Unit.normRep_pos_proved`) and the analytic statement
(`Generated.D72Unit.analytic_pos_proved`) are proved.  The target `H = −1` needs no premise of its
own: it uses that of `H = 1`, transported by sign. -/
theorem residual_empty (hM : Generated.D72Unit.matveev_pos) (u v : ℤ) :
    H72 u v ≠ 1 ∧ H72 u v ≠ -1 := by
  rw [H72_eq]
  constructor <;> intro h
  · simpa using (Generated.D72Unit.class_pos hM u v).mp h
  · simpa using (Generated.D72Unit.class_neg hM u v).mp h

end PerfectPower.D72Residual
