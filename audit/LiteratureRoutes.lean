import PerfectPower.CubicCovariants
import PerfectPower.RankTwoSieve

#print axioms PerfectPower.CubicCovariants.syzygy
#print axioms PerfectPower.CubicCovariants.mordell_forward
#print axioms PerfectPower.CubicCovariants.reduced_quadratic_lower
#print axioms PerfectPower.CubicCovariants.complete_of_mordell_bound
#print axioms PerfectPower.CubicCovariants.sixth_scale
#print axioms PerfectPower.RankTwoSieve.signed_periodic
#print axioms PerfectPower.RankTwoSieve.signed_residue_iff
#print axioms PerfectPower.RankTwoSieve.intersect_necessary

example : PerfectPower.CubicCovariants.form (-3) 0 3 1 (-1) 0 = 3 := by decide
example : PerfectPower.CubicCovariants.discriminant (-3) 0 3 1 = 81 := by decide
example : PerfectPower.CubicCovariants.discriminant (-1) 0 9 6 = 1944 := by decide
example : PerfectPower.CubicCovariants.hessian (-1) 0 9 6 1 0 = 27 := by decide
example : PerfectPower.CubicCovariants.jacobian (-1) 0 9 6 1 0 = -162 := by decide

-- The reduced-Hessian condition cannot be silently assumed for the D=1944 source.
example : ¬ (|0 * 9 - 9 * (-1) * 6| ≤ (0:ℤ)^2-3*(-1)*9) := by decide
