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
-- Pell orbit representatives (finite box) and function-field Pillai
#print axioms pell_descent_box
#print axioms pell_box_finite
#print axioms pell_orbits_exhaust
#print axioms pillai_polynomial
#print axioms pillai_polynomial_balanced
#print axioms pillai_polynomial_sq_sharp
-- ProfileG (Theorem G, combinatorial half)
#print axioms S_le_one_iff
#print axioms profile_table_ok
#print axioms profiles12_length
-- Reflect (verified certificate checkers) and the reflective census
#print axioms PerfectPower.Reflect.check_sound
#print axioms PerfectPower.Reflect.mordellOK_sound
#print axioms PerfectPower.Reflect.ev_shift
#print axioms PerfectPower.Reflect.intervalPos_sound
#print axioms PerfectPower.Generated.cert_consecutive10_square_hits_ok
#print axioms PerfectPower.Generated.cert_consecutive12_fourth_power_hits_ok
#print axioms PerfectPower.Generated.Mordell.census_ok
#print axioms PerfectPower.Generated.Mordell.census_size
#print axioms unitOrbit_growth
#print axioms pell_count_log
#print axioms PerfectPower.Reflect.rungeCheck_sound
-- PellExact (exact Pell count) and the general Theorem G statement
#print axioms PerfectPower.PellExact.exists_root
#print axioms PerfectPower.PellExact.root_unique
#print axioms PerfectPower.PellExact.roots_finite
#print axioms PerfectPower.PellExact.orbit_fst_bracket
#print axioms PerfectPower.PellExact.count_near_geometric
#print axioms PerfectPower.PellExact.class_count
#print axioms PerfectPower.PellExact.orbit_count
#print axioms PerfectPower.PellExact.pell_exact_count
#print axioms chi_eq
#print axioms chi_neg_iff
-- RadicalAsymp (radical real-power asymptotic) and the Atlas interface
#print axioms radW_spec
#print axioms radW_approx
#print axioms radical_asymptotic
#print axioms radical_asymptotic_int
#print axioms isHit_mul_pow_iff
#print axioms atlas_power
#print axioms atlas_radical
#print axioms atlas_pell
#print axioms atlas_finite
-- Genus1 (checked Weierstrass reductions; Sage points as named hypotheses)
#print axioms PerfectPower.Genus1.cubic_sound
#print axioms PerfectPower.Genus1.quad_sound
#print axioms PerfectPower.Generated.Genus1.g1_sq_m1_m3_2_1_hits
#print axioms PerfectPower.Generated.Genus1.g1_cube_m6_m7_6_hits
-- MordellDescent (unconditional: no integral points on y^2 = x^3 + k)
#print axioms PerfectPower.MordellDescent.good_of_dvd
#print axioms PerfectPower.MordellDescent.exists_bad_prime
#print axioms PerfectPower.MordellDescent.goodDivisors_of_cert
#print axioms PerfectPower.MordellDescent.no_points
#print axioms PerfectPower.MordellDescent.not_isHit
#print axioms PerfectPower.MordellDescent.mordell_7
#print axioms PerfectPower.Generated.MordellDescent.no_points_m9985
#print axioms PerfectPower.Generated.MordellDescent.no_points_m9957
#print axioms PerfectPower.Generated.MordellDescent.no_points_m9201
-- MordellFLT3 (unconditional nonempty list, via Mathlib's FLT for exponent 3)
#print axioms PerfectPower.MordellFLT3.points
#print axioms PerfectPower.MordellFLT3.isHit_iff
#print axioms PerfectPower.MordellFLT3.hitSet_432
-- Positive rank, unconditional: y^2 = x^3 - 2 and y^2 = x^3 - 4
#print axioms PerfectPower.MordellMinus2.norm_mod_lt
#print axioms PerfectPower.MordellMinus2.points
#print axioms PerfectPower.MordellMinus2.hitSet
#print axioms PerfectPower.MordellMinus4.unit_is_cube
#print axioms PerfectPower.MordellMinus4.points
#print axioms PerfectPower.MordellMinus4.hitSet
-- Transport with integrality and exact counts
#print axioms PerfectPower.Transport.affine_count
#print axioms PerfectPower.Transport.affine_count_le
#print axioms PerfectPower.Transport.affine_cube_sub_two
#print axioms PerfectPower.Transport.complete_fermat
#print axioms PerfectPower.Transport.complete_of_no_points
#print axioms PerfectPower.Transport.cubic_sound_image
#print axioms PerfectPower.Transport.n3m2_hits
-- Class number two, unconditional: the ideal-free template and its instances D = 13, 5, 6
#print axioms PerfectPower.ClassTwo.exists_short
#print axioms PerfectPower.ClassTwo.box
#print axioms PerfectPower.ClassTwo.short_relation
#print axioms PerfectPower.ClassTwo.halvesOK_of_mod8
#print axioms PerfectPower.ClassTwo.cube_of_table
#print axioms PerfectPower.MordellMinus13.table13
#print axioms PerfectPower.MordellMinus13.points
#print axioms PerfectPower.MordellMinus13.hitSet
#print axioms PerfectPower.MordellMinus5.table5
#print axioms PerfectPower.MordellMinus5.no_points
#print axioms PerfectPower.MordellMinus5.not_isHit
#print axioms PerfectPower.MordellMinus6.table6
#print axioms PerfectPower.MordellMinus6.no_points
#print axioms PerfectPower.MordellMinus6.not_isHit
#print axioms PerfectPower.Transport.complete_cube_sub_thirteen
