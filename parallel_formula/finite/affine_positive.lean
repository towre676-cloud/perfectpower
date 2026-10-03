import PerfectPower.FormulaAffine
import PerfectPower.Generated.ClassLists.K2
-- Source SHA256: 1521b47b6533dd3000fec11f8f62bc285c14cf9cc837969c7c5c1776372327ad
-- Integer symbols mapped to Lean names: {'n': 'x', 'm': 'y', 'z': 'z0'}
namespace PerfectPower.GeneratedFiniteFormula.S1521b47b6533
private def residual (z0 : ℤ) (x y : ℤ) : Prop := ((z0 = (x + y)) ∧ (z0 ≥ (0 : ℤ)))
private def pointList : List (ℤ × ℤ) := [((-1), (-1)), ((-1), (1))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(2)) x y ↔ (x,y) ∈ pointList := Generated.ClassLists.K2.plus2 x y
private theorem relation (z0 : ℤ) (x y : ℤ) : (((((2 : ℤ) * y) + (1 : ℤ)) * (((2 : ℤ) * y) + (1 : ℤ))) = (((((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ))) + (2 : ℤ))) ↔ ((2:ℤ)*y+(1))^2 = ((3:ℤ)*x+(2))^3+(2) := by
  have identity : ((((2 : ℤ) * y) + (1 : ℤ)) * (((2 : ℤ) * y) + (1 : ℤ))) - (((((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ))) + (2 : ℤ)) =
      (1:ℤ) * ((((2:ℤ)*y+(1))^2) - (((3:ℤ)*x+(2))^3+(2))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite (z0 : ℤ) :
    (∃ x y : ℤ, (((((2 : ℤ) * y) + (1 : ℤ)) * (((2 : ℤ) * y) + (1 : ℤ))) = (((((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ))) + (2 : ℤ))) ∧ (residual z0) x y) ↔
      ((residual z0) (-1) (-1) ∨ (residual z0) (-1) (0)) := by
  simp_rw [relation z0]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(2)) pointList pointList_complete (3) (2) (2) (1) (by norm_num) (by norm_num) (residual z0)
#print axioms original_iff_finite
theorem whole_query_iff :
    (∃ z0 : ℤ, ∃ x y : ℤ, (((((2 : ℤ) * y) + (1 : ℤ)) * (((2 : ℤ) * y) + (1 : ℤ))) = (((((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ)) * (((3 : ℤ) * x) + (2 : ℤ))) + (2 : ℤ))) ∧ (residual z0) x y) ↔
      (∃ z0 : ℤ, (residual z0) (-1) (-1) ∨ (residual z0) (-1) (0)) := by
  simp_rw [original_iff_finite]
#print axioms whole_query_iff
end PerfectPower.GeneratedFiniteFormula.S1521b47b6533
