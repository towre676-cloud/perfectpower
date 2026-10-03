import PerfectPower.FormulaTransport
-- Source SHA256: e0db798188db6dc568ee3638f4946eb9e90db88cc11b1c924f08cbaa23646ef4
-- Symbols: square coordinate 'x'; cube coordinate 'y'
namespace PerfectPower.GeneratedFormula
private def residual (x y : ℤ) : Prop := ((x = (5 : ℤ)) ∨ (x = (7 : ℤ)) ∨ (x = (9 : ℤ)) ∨ (x = (27 : ℤ)) ∨ (x = (10 : ℤ))) ∧ ((y = (0 : ℤ)) ∨ (y = (1 : ℤ)) ∨ (y = (9 : ℤ)) ∨ (y = (8 : ℤ)))
-- All residual assertions retain their exact integer and Boolean meaning.
theorem original_iff_parameter :
    (∃ x y : ℤ, x * x = y * y * y ∧ residual x y) ↔
      ∃ t : ℤ, residual (t ^ 3) (t ^ 2) := by
  simpa only [pow_succ, pow_zero, mul_one, one_mul] using
    FormulaTransport.square_cube_exists residual
#print axioms original_iff_parameter
end PerfectPower.GeneratedFormula
