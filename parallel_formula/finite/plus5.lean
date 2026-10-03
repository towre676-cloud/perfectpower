import PerfectPower.FormulaAffine
import PerfectPower.Generated.ClassLists.K5
-- Source SHA256: 477081b5786d89134a6d9f12498fcf3b1aa13175709d95a2ed4f623594c0c7d0
-- Integer symbols mapped to Lean names: {'n': 'x', 'm': 'y'}
namespace PerfectPower.GeneratedFiniteFormula.S477081b5786d
private def residual  (x y : ℤ) : Prop := (x > (0 : ℤ))
private def pointList : List (ℤ × ℤ) := [((-1), (-2)), ((-1), (2))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(5)) x y ↔ (x,y) ∈ pointList := Generated.ClassLists.K5.plus5 x y
private theorem relation  (x y : ℤ) : ((y * y) = ((x * x * x) + (5 : ℤ))) ↔ ((1:ℤ)*y+(0))^2 = ((1:ℤ)*x+(0))^3+(5) := by
  have identity : (y * y) - ((x * x * x) + (5 : ℤ)) =
      (1:ℤ) * ((((1:ℤ)*y+(0))^2) - (((1:ℤ)*x+(0))^3+(5))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite  :
    (∃ x y : ℤ, ((y * y) = ((x * x * x) + (5 : ℤ))) ∧ residual x y) ↔
      (residual (-1) (-2) ∨ residual (-1) (2)) := by
  simp_rw [relation ]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(5)) pointList pointList_complete (1) (0) (1) (0) (by norm_num) (by norm_num) residual
#print axioms original_iff_finite
end PerfectPower.GeneratedFiniteFormula.S477081b5786d
