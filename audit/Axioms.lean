import PerfectPower
/-! Axiom audit: every public theorem must depend only on `propext`, `Classical.choice` and
`Quot.sound` (no `sorryAx`, no custom axioms).  Run with `lake env lean audit/Axioms.lean`. -/
open PerfectPower
-- Basic / Density
#print axioms H_eq_of_hasDensity
#print axioms hasDensity_zero_of_finite
#print axioms A_sub_eq_const
#print axioms H_surgery
#print axioms hasDensity_of_periodic
-- Rigid / Estimates / Dichotomy
#print axioms exists_denominator
#print axioms frac_periodic
#print axioms integral_closure_step
#print axioms exists_truncated_root
#print axioms pow_diff_bound
#print axioms eventually_no_hit
#print axioms rigid_dichotomy
-- ZeroOne
#print axioms hasDensity_one_of_pow
#print axioms rigid_zero_one
#print axioms rigid_H_mem
#print axioms twisted_hits_subset
#print axioms twisted_finite
#print axioms twisted_density_zero
-- Monomial
#print axioms rat_pow_eq_nat
#print axioms monomial_isHit_iff
#print axioms monomial_hitSet
#print axioms monomial_count
-- Examples
#print axioms consecutive_four_not_square
#print axioms consecutive_four_hitSet
#print axioms ljunggren_quartic
#print axioms ljunggren_hitSet
-- Pell example 2n^2 + 1
#print axioms hasDensity_zero_of_count_le
#print axioms pell_descent
#print axioms pell_hit_iff
#print axioms pell_hitSet_infinite
#print axioms pell_count_le
#print axioms pell_hasDensity_zero
