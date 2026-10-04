import PerfectPower.FormulaAffine
import PerfectPower.QuarticPilot
-- Source SHA256: cac1b5198e3c007dfec18bf64f981d7289c9a105ab05c53c300ef01c6cb5c771
-- Integer symbols mapped to Lean names: {'x': 'x', 'y': 'y', 'z': 'z0', 'w': 'z1'}
namespace PerfectPower.GeneratedFiniteFormula.Scac1b5198e3c
private def residual (z0 : ℤ) (z1 : ℤ) (x y : ℤ) : Prop := (z1 = (x * z0)) ∧ (¬ (z1 = (0 : ℤ)))
private def pointList : List (ℤ × ℤ) := [((0), (-1)), ((0), (1))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y ^ 2 = 3*x^4+3*x^2+1) x y ↔ (x,y) ∈ pointList := by simpa [pointList, and_or_left, or_comm] using QuarticPilot.complete x y
private theorem relation (z0 : ℤ) (z1 : ℤ) (x y : ℤ) : ((y * y) = (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ))) ↔ y ^ 2 = 3*x^4+3*x^2+1 := by
  have identity : (y * y) - (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ)) =
      (1:ℤ) * ((y ^ 2) - (3*x^4+3*x^2+1)) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite (z0 : ℤ) (z1 : ℤ) :
    (∃ x y : ℤ, ((y * y) = (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ))) ∧ (residual z0 z1) x y) ↔
      ((residual z0 z1) (0) (-1) ∨ (residual z0 z1) (0) (1)) := by
  simp_rw [relation z0 z1]
  simpa [pointList] using FormulaTransport.finite_exists (fun x y : ℤ => y ^ 2 = 3*x^4+3*x^2+1) pointList pointList_complete (residual z0 z1)
#print axioms original_iff_finite
theorem whole_query_iff :
    (∃ z0 z1 : ℤ, ∃ x y : ℤ, ((y * y) = (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ))) ∧ (residual z0 z1) x y) ↔
      (∃ z0 z1 : ℤ, (residual z0 z1) (0) (-1) ∨ (residual z0 z1) (0) (1)) := by
  simp_rw [original_iff_finite]
#print axioms whole_query_iff
end PerfectPower.GeneratedFiniteFormula.Scac1b5198e3c
