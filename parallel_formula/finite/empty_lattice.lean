import PerfectPower.FormulaAffine
import PerfectPower.Generated.ClassLists.K2
-- Source SHA256: c86782a1a91a3b53d23e2b413a68c4512e8db15c3d3134c829236446ed22ecc2
-- Integer symbols mapped to Lean names: {'n': 'x', 'm': 'y'}
namespace PerfectPower.GeneratedFiniteFormula.Sc86782a1a91a
private def residual  (x y : ℤ) : Prop := True
private def pointList : List (ℤ × ℤ) := [((-1), (-1)), ((-1), (1))]
private theorem pointList_complete (x y : ℤ) :
    (fun x y : ℤ => y^2 = x^3+(2)) x y ↔ (x,y) ∈ pointList := Generated.ClassLists.K2.plus2 x y
private theorem relation  (x y : ℤ) : ((y * y) = (((((2 : ℤ) * x) + (0 : ℤ)) * (((2 : ℤ) * x) + (0 : ℤ)) * (((2 : ℤ) * x) + (0 : ℤ))) + (2 : ℤ))) ↔ ((1:ℤ)*y+(0))^2 = ((2:ℤ)*x+(0))^3+(2) := by
  have identity : (y * y) - (((((2 : ℤ) * x) + (0 : ℤ)) * (((2 : ℤ) * x) + (0 : ℤ)) * (((2 : ℤ) * x) + (0 : ℤ))) + (2 : ℤ)) =
      (1:ℤ) * ((((1:ℤ)*y+(0))^2) - (((2:ℤ)*x+(0))^3+(2))) := by ring
  constructor <;> intro h <;> nlinarith [identity]
theorem original_iff_finite  :
    (∃ x y : ℤ, ((y * y) = (((((2 : ℤ) * x) + (0 : ℤ)) * (((2 : ℤ) * x) + (0 : ℤ)) * (((2 : ℤ) * x) + (0 : ℤ))) + (2 : ℤ))) ∧ residual x y) ↔
      (False) := by
  simp_rw [relation ]
  simpa [pointList] using FormulaTransport.affine_pair_finite_exists (fun x y : ℤ => y^2 = x^3+(2)) pointList pointList_complete (2) (0) (1) (0) (by norm_num) (by norm_num) residual
#print axioms original_iff_finite
end PerfectPower.GeneratedFiniteFormula.Sc86782a1a91a
