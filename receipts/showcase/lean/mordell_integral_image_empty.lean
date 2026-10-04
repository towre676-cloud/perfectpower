import PerfectPower.FormulaAffine
import PerfectPower.Generated.ClassLists.K22
-- Source SHA256: 955a951118a3d8dcab78882d921ec65128f317e1ff62f0f175001073c8d5d577
-- Integer symbols mapped to Lean names: {'x': 'x', 'y': 'y', 'z': 'z0', 'w': 'z1'}
namespace PerfectPower.GeneratedFiniteFormula.S955a951118a3
private def residual (z0 : ℤ) (z1 : ℤ) (x y : ℤ) : Prop := True
private def pointList : List (ℤ × ℤ) := [((3), (-7)), ((3), (7))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(22)) x y ↔ (x,y) ∈ pointList := Generated.ClassLists.K22.plus22 x y
private theorem relation (z0 : ℤ) (z1 : ℤ) (x y : ℤ) : (((((1 : ℤ) * y) + (0 : ℤ)) * (((1 : ℤ) * y) + (0 : ℤ))) = (((((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ))) + (22 : ℤ))) ↔ ((1:ℤ)*y+(0))^2 = ((6:ℤ)*x+(1))^3+(22) := by
  have identity : ((((1 : ℤ) * y) + (0 : ℤ)) * (((1 : ℤ) * y) + (0 : ℤ))) - (((((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ))) + (22 : ℤ)) =
      (1:ℤ) * ((((1:ℤ)*y+(0))^2) - (((6:ℤ)*x+(1))^3+(22))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite (z0 : ℤ) (z1 : ℤ) :
    (∃ x y : ℤ, (((((1 : ℤ) * y) + (0 : ℤ)) * (((1 : ℤ) * y) + (0 : ℤ))) = (((((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ))) + (22 : ℤ))) ∧ (residual z0 z1) x y) ↔
      (False) := by
  simp_rw [relation z0 z1]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(22)) pointList pointList_complete (6) (1) (1) (0) (by norm_num) (by norm_num) (residual z0 z1)
#print axioms original_iff_finite
theorem whole_query_iff :
    (∃ z0 z1 : ℤ, ∃ x y : ℤ, (((((1 : ℤ) * y) + (0 : ℤ)) * (((1 : ℤ) * y) + (0 : ℤ))) = (((((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ)) * (((6 : ℤ) * x) + (1 : ℤ))) + (22 : ℤ))) ∧ (residual z0 z1) x y) ↔
      (∃ z0 z1 : ℤ, False) := by
  simp_rw [original_iff_finite]
#print axioms whole_query_iff
end PerfectPower.GeneratedFiniteFormula.S955a951118a3
