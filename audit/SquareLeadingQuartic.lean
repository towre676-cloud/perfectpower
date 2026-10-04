import PerfectPower.Tactic.SquareLeadingQuartic
import PerfectPower.Generated.RepunitQuartic
#print axioms PerfectPower.SquareLeadingQuartic.scaling_identity
#print axioms PerfectPower.SquareLeadingQuartic.coordinate_bound
#print axioms PerfectPower.SquareLeadingQuartic.complete
native_square_leading_quartic fractional_cubic for 1, 1, 0, 0, 0
native_square_leading_quartic fractional_quadratic for 1, 0, 1, 0, 1
native_square_leading_quartic repunit_quartic for 1, 1, 1, 1, 1
native_square_leading_quartic nonsquare_monic_completion for 2, 1, 0, 0, 0
#print axioms fractional_cubic_complete
#print axioms fractional_quadratic_complete
#print axioms repunit_quartic_complete
#print axioms nonsquare_monic_completion_complete
example : (3,11) ∈ repunit_quartic := by decide +kernel
example : (3,-11) ∈ repunit_quartic := by decide +kernel
example : fractional_cubic = {(-1,0),(0,0)} := by decide +kernel

#print axioms PerfectPower.RepunitQuartic.inputs
#print axioms PerfectPower.RepunitQuartic.positive
