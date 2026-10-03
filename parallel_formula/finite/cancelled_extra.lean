import PerfectPower.FormulaAffine
import PerfectPower.Generated.ClassLists.K2
-- Source SHA256: a9d86e7c81e1c80912d3c0d2d1bd49e656bfcc9064bea9c6a388adc3bdc43bc5
-- Integer symbols mapped to Lean names: {'n': 'x', 'm': 'y', 'z': 'z0'}
namespace PerfectPower.GeneratedFiniteFormula.Sa9d86e7c81e1
private def residual (z0 : ℤ) (x y : ℤ) : Prop := (z0 = (x + y))
private def pointList : List (ℤ × ℤ) := [((-1), (-1)), ((-1), (1))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(2)) x y ↔ (x,y) ∈ pointList := Generated.ClassLists.K2.plus2 x y
private theorem relation (z0 : ℤ) (x y : ℤ) : ((y * y) = ((x * x * x) + (2 : ℤ) + (z0 - z0))) ↔ ((1:ℤ)*y+(0))^2 = ((1:ℤ)*x+(0))^3+(2) := by
  have identity : (y * y) - ((x * x * x) + (2 : ℤ) + (z0 - z0)) =
      (1:ℤ) * ((((1:ℤ)*y+(0))^2) - (((1:ℤ)*x+(0))^3+(2))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite (z0 : ℤ) :
    (∃ x y : ℤ, ((y * y) = ((x * x * x) + (2 : ℤ) + (z0 - z0))) ∧ (residual z0) x y) ↔
      ((residual z0) (-1) (-1) ∨ (residual z0) (-1) (1)) := by
  simp_rw [relation z0]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(2)) pointList pointList_complete (1) (0) (1) (0) (by norm_num) (by norm_num) (residual z0)
#print axioms original_iff_finite
theorem whole_query_iff :
    (∃ z0 : ℤ, ∃ x y : ℤ, ((y * y) = ((x * x * x) + (2 : ℤ) + (z0 - z0))) ∧ (residual z0) x y) ↔
      (∃ z0 : ℤ, (residual z0) (-1) (-1) ∨ (residual z0) (-1) (1)) := by
  simp_rw [original_iff_finite]
#print axioms whole_query_iff
end PerfectPower.GeneratedFiniteFormula.Sa9d86e7c81e1
