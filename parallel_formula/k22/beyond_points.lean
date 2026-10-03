import PerfectPower.FormulaAffine
import PerfectPower.Generated.ClassLists.K22
-- Source SHA256: e3a1bd8856b33a95013280c551d01728128daed12faf4b113da0eab69fabc5f8
-- Integer symbols mapped to Lean names: {'x': 'x', 'y': 'y'}
namespace PerfectPower.GeneratedFiniteFormula.Se3a1bd8856b3
private def residual  (x y : ℤ) : Prop := (x > (3 : ℤ))
private def pointList : List (ℤ × ℤ) := [((3), (-7)), ((3), (7))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(22)) x y ↔ (x,y) ∈ pointList := Generated.ClassLists.K22.plus22 x y
private theorem relation  (x y : ℤ) : ((y * y) = ((x * x * x) + (22 : ℤ))) ↔ ((1:ℤ)*y+(0))^2 = ((1:ℤ)*x+(0))^3+(22) := by
  have identity : (y * y) - ((x * x * x) + (22 : ℤ)) =
      (1:ℤ) * ((((1:ℤ)*y+(0))^2) - (((1:ℤ)*x+(0))^3+(22))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite  :
    (∃ x y : ℤ, ((y * y) = ((x * x * x) + (22 : ℤ))) ∧ residual x y) ↔
      (residual (3) (-7) ∨ residual (3) (7)) := by
  simp_rw [relation ]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(22)) pointList pointList_complete (1) (0) (1) (0) (by norm_num) (by norm_num) residual
#print axioms original_iff_finite
end PerfectPower.GeneratedFiniteFormula.Se3a1bd8856b3
