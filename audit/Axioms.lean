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
-- Theorem R (integer form)
#print axioms pow_diff_bound'
#print axioms runge_pointwise
#print axioms runge_uniform
#print axioms runge_finite
#print axioms power_type_finite
-- Certificates and machine-generated hit sets
#print axioms not_isHit_between
#print axioms not_isHit_neg
#print axioms PerfectPower.Generated.ljunggren_quartic_hits
#print axioms PerfectPower.Generated.n4_plus_1_square_hits
#print axioms PerfectPower.Generated.consecutive4_square_hits
#print axioms PerfectPower.Generated.consecutive4_fourth_power_hits
#print axioms PerfectPower.Generated.consecutive6_square_hits
#print axioms PerfectPower.Generated.consecutive6_cube_hits
#print axioms PerfectPower.Generated.consecutive6_sixth_power_hits
#print axioms PerfectPower.Generated.consecutive8_square_hits
#print axioms PerfectPower.Generated.consecutive8_fourth_power_hits
#print axioms PerfectPower.Generated.consecutive8_eighth_power_hits
#print axioms PerfectPower.Generated.consecutive10_fifth_power_hits
#print axioms PerfectPower.Generated.consecutive12_square_hits
#print axioms PerfectPower.Generated.consecutive12_cube_hits
#print axioms PerfectPower.Generated.consecutive12_sixth_power_hits
#print axioms PerfectPower.Generated.n6_plus_n_plus_1_cube_hits
#print axioms PerfectPower.Generated.n4_plus_7_square_hits
#print axioms PerfectPower.Generated.sextic_1_2_3_4_5_6_1_cube_hits
-- Exponential sequences
#print axioms isHit_exp_shift
#print axioms exp_hasDensity
#print axioms two_pow_hasDensity_half
#print axioms PerfectPower.Generated.consecutive10_square_hits
#print axioms PerfectPower.Generated.consecutive12_fourth_power_hits
#print axioms no_hit_of_sandwich
-- Function field (unconditional) and abc-conditional layer (abc is a hypothesis, not an axiom)
#print axioms davenport
#print axioms davenport_sharp
#print axioms hall_of_abc
#print axioms pillai_bound_of_abc
#print axioms pillai_finite_of_abc
-- Mordell census points lie on their curves (completeness NOT checked; see TRUST_BOUNDARY)
#print axioms PerfectPower.Generated.Mordell.census_points_valid
-- Binomial coefficients via elliptic curves (point-list completeness is an explicit hypothesis)
#print axioms two_mul_choose_two
#print axioms six_mul_choose_three
#print axioms binomial_curve_points_valid
#print axioms choose_two_cube_iff
#print axioms choose_two_cube_hits
#print axioms choose_three_square_iff
#print axioms choose_three_square_hits
-- Valuation core of Theorem B
#print axioms exists_pow_iff_factorization
#print axioms isHit_iff_natAbs
#print axioms isHit_iff_rat
#print axioms mul_pow_isPow_iff_congr
#print axioms mul_pow_isPow_iff_param
-- PellGeneral (Theorem Q interfaces)
#print axioms quadratic_isHit_iff_norm
#print axioms unitAct_norm
#print axioms unitOrbit_norm
#print axioms unitOrbit_periodic
#print axioms goodClass_hits
#print axioms index_le_of_geometric
#print axioms le_of_index_le_geometric
#print axioms geometric_count_le
#print axioms le_geometric_count
-- RadicalCount (Theorem B count)
#print axioms count_periodic_eq
#print axioms count_periodic_le
#print axioms le_count_periodic
#print axioms card_Icc_filter_eq_count
#print axioms radical_hits_card
#print axioms radical_count_bound
