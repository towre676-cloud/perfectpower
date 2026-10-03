import PerfectPower.FormulaAffine
import PerfectPower.QuarticPilot
-- Source SHA256: 79cd9ec345a2a3b792468bdec5360f9a365f6d3062733c40ee0197026951267b
-- Integer symbols mapped to Lean names: {'u': 'x', 'v': 'y'}
namespace PerfectPower.GeneratedFiniteFormula.S79cd9ec345a2
private def residual  (x y : ℤ) : Prop := (x > (0 : ℤ))
private def pointList : List (ℤ × ℤ) := [((0), (-1)), ((0), (1))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y ^ 2 = 3*x^4+3*x^2+1) x y ↔ (x,y) ∈ pointList := by simpa [pointList, and_or_left, or_comm] using QuarticPilot.complete x y
private theorem relation  (x y : ℤ) : ((y * y) = (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ))) ↔ y ^ 2 = 3*x^4+3*x^2+1 := by
  have identity : (y * y) - (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ)) =
      (1:ℤ) * ((y ^ 2) - (3*x^4+3*x^2+1)) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite  :
    (∃ x y : ℤ, ((y * y) = (((3 : ℤ) * x * x * x * x) + ((3 : ℤ) * x * x) + (1 : ℤ))) ∧ residual x y) ↔
      (residual (0) (-1) ∨ residual (0) (1)) := by
  simp_rw [relation ]
  simpa [pointList] using FormulaTransport.finite_exists (fun x y : ℤ => y ^ 2 = 3*x^4+3*x^2+1) pointList pointList_complete residual
#print axioms original_iff_finite
end PerfectPower.GeneratedFiniteFormula.S79cd9ec345a2
