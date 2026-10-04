import PerfectPower.BoundedReconstruction
import PerfectPower.RecoveredOperators
import PerfectPower.RecurrenceRecovery

#print axioms PerfectPower.BoundedReconstruction.unique
#print axioms PerfectPower.RecoveredOperators.hypergeometric_coefficient
#print axioms PerfectPower.RecoveredOperators.hypergeometric_all
#print axioms PerfectPower.RecoveredOperators.wilson_projectors
#print axioms PerfectPower.RecurrenceRecovery.order_three_unique
#print axioms PerfectPower.RecurrenceRecovery.padovan_unique

-- Strictness is essential: at M=2AB distinct bounded fractions can collide.
example : (2:ℤ) ∣ 1-(-1) := by decide
example : (1:ℚ)/1 ≠ (-1:ℚ)/1 := by norm_num
example : ¬ (2*(1:ℤ)*1 < 2) := by decide
