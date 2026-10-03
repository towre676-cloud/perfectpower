import PerfectPower.FormulaTransport
import PerfectPower.Generated.ClassLists.K2

namespace PerfectPower.FormulaPilot
/-- A complete source theorem composed with an arbitrary residual constraint. -/
theorem plus2_consumer (C : ℤ → ℤ → Prop) :
    (∃ x y : ℤ, y ^ 2 = x ^ 3 + 2 ∧ C x y) ↔
      (C (-1) (-1) ∨ C (-1) 1) := by
  simpa using FormulaTransport.finite_exists
    (fun x y : ℤ => y ^ 2 = x ^ 3 + 2)
    ([((-1), (-1)), ((-1), 1)] : List (ℤ × ℤ))
    Generated.ClassLists.K2.plus2 C
#print axioms plus2_consumer
end PerfectPower.FormulaPilot
