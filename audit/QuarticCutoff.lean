import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.QuarticCutoffAudit
native_square_leading_quartic large_old_bound for 1, 1, 1, 1, -199
example : large_old_bound = {(7,-51),(7,51)} := by decide +kernel
-- This zero-perturbation point lies well outside the domination cutoff.
native_square_leading_quartic exceptional_fibre for 1, 0, 0, 1, -100
example : (100,10000) ∈ exceptional_fibre := by decide +kernel
example : (100,-10000) ∈ exceptional_fibre := by decide +kernel
#print axioms PerfectPower.QuarticCutoff.bound_or_zero
#print axioms PerfectPower.QuarticCutoff.zeroRoots_complete
#print axioms PerfectPower.QuarticCutoff.complete
#print axioms large_old_bound_complete
#print axioms exceptional_fibre_complete
end PerfectPower.QuarticCutoffAudit
