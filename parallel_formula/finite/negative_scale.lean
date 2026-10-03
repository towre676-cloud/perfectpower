import PerfectPower.FormulaAffine
import PerfectPower.MordellMinus1
-- Source SHA256: bb2f321274cd7450ab0b8c227d0b3edab6e571bcf604b22130ebaca6d3a7e58e
-- Integer symbols mapped to Lean names: {'n': 'x', 'm': 'y'}
namespace PerfectPower.GeneratedFiniteFormula.Sbb2f321274cd
private def residual  (x y : ℤ) : Prop := (x ≥ (0 : ℤ))
private def pointList : List (ℤ × ℤ) := [((1), (0))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(-1)) x y ↔ (x,y) ∈ pointList := by simpa [pointList, sub_eq_add_neg] using MordellMinus1.complete x y
private theorem relation  (x y : ℤ) : ((y * y) = (((((-(3 : ℤ)) * x) + (1 : ℤ)) * (((-(3 : ℤ)) * x) + (1 : ℤ)) * (((-(3 : ℤ)) * x) + (1 : ℤ))) - (1 : ℤ))) ↔ ((1:ℤ)*y+(0))^2 = ((-3:ℤ)*x+(1))^3+(-1) := by
  have identity : (y * y) - (((((-(3 : ℤ)) * x) + (1 : ℤ)) * (((-(3 : ℤ)) * x) + (1 : ℤ)) * (((-(3 : ℤ)) * x) + (1 : ℤ))) - (1 : ℤ)) =
      (1:ℤ) * ((((1:ℤ)*y+(0))^2) - (((-3:ℤ)*x+(1))^3+(-1))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite  :
    (∃ x y : ℤ, ((y * y) = (((((-(3 : ℤ)) * x) + (1 : ℤ)) * (((-(3 : ℤ)) * x) + (1 : ℤ)) * (((-(3 : ℤ)) * x) + (1 : ℤ))) - (1 : ℤ))) ∧ residual x y) ↔
      (residual (0) (0)) := by
  simp_rw [relation ]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(-1)) pointList pointList_complete (-3) (1) (1) (0) (by norm_num) (by norm_num) residual
#print axioms original_iff_finite
end PerfectPower.GeneratedFiniteFormula.Sbb2f321274cd
