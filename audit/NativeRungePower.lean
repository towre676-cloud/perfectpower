import PerfectPower.Tactic.RungePower

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace NativeRungePowerAudit
#print axioms PerfectPower.NativePowerRoots.search_bounds
#print axioms PerfectPower.NativePowerRoots.root_bounds
#print axioms PerfectPower.NativePowerRoots.root_exact
#print axioms PerfectPower.NativePowerRoots.roots_complete
#print axioms PerfectPower.RungePower.nonneg_gap
#print axioms PerfectPower.RungePower.power_gap
#print axioms PerfectPower.RungePower.coordinate_bound
#print axioms PerfectPower.RungePower.complete
#print axioms PerfectPower.RungePower.power_family

native_runge_power exponent_2 for [1, 1, 0, 0, 1], 2
theorem exponent_2_packet : exponent_2 = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms exponent_2_decomposition
#print axioms exponent_2_dominating_power
#print axioms exponent_2_bound
#print axioms exponent_2_complete
#print axioms exponent_2_packet

native_runge_power exponent_3 for [1, 1, 0, 0, 0, 0, 1], 3
theorem exponent_3_packet : exponent_3 = {(-1,1), (0,1)} := by decide +kernel
#print axioms exponent_3_decomposition
#print axioms exponent_3_dominating_power
#print axioms exponent_3_bound
#print axioms exponent_3_complete
#print axioms exponent_3_packet

native_runge_power exponent_4 for [1, 1, 0, 0, 0, 0, 0, 0, 1], 4
theorem exponent_4_packet : exponent_4 = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms exponent_4_decomposition
#print axioms exponent_4_dominating_power
#print axioms exponent_4_bound
#print axioms exponent_4_complete
#print axioms exponent_4_packet

native_runge_power exponent_5 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], 5
theorem exponent_5_packet : exponent_5 = {(-1,1), (0,1)} := by decide +kernel
#print axioms exponent_5_decomposition
#print axioms exponent_5_dominating_power
#print axioms exponent_5_bound
#print axioms exponent_5_complete
#print axioms exponent_5_packet

native_runge_power exponent_6 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 6
theorem exponent_6_packet : exponent_6 = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms exponent_6_decomposition
#print axioms exponent_6_dominating_power
#print axioms exponent_6_bound
#print axioms exponent_6_complete
#print axioms exponent_6_packet

native_runge_power exponent_7 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 7
theorem exponent_7_packet : exponent_7 = {(-1,1), (0,1)} := by decide +kernel
#print axioms exponent_7_decomposition
#print axioms exponent_7_dominating_power
#print axioms exponent_7_bound
#print axioms exponent_7_complete
#print axioms exponent_7_packet

native_runge_power exponent_8 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 8
theorem exponent_8_packet : exponent_8 = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms exponent_8_decomposition
#print axioms exponent_8_dominating_power
#print axioms exponent_8_bound
#print axioms exponent_8_complete
#print axioms exponent_8_packet

native_runge_power exponent_9 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 9
theorem exponent_9_packet : exponent_9 = {(-1,1), (0,1)} := by decide +kernel
#print axioms exponent_9_decomposition
#print axioms exponent_9_dominating_power
#print axioms exponent_9_bound
#print axioms exponent_9_complete
#print axioms exponent_9_packet

native_runge_power exponent_10 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 10
theorem exponent_10_packet : exponent_10 = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms exponent_10_decomposition
#print axioms exponent_10_dominating_power
#print axioms exponent_10_bound
#print axioms exponent_10_complete
#print axioms exponent_10_packet

native_runge_power cubic for [1, 1, 0, 1], 3
theorem cubic_packet : cubic = {(-1,-1), (0,1)} := by decide +kernel
#print axioms cubic_decomposition
#print axioms cubic_dominating_power
#print axioms cubic_bound
#print axioms cubic_complete
#print axioms cubic_packet

native_runge_power negative_cubic for [1, 1, 0, -1], 3
theorem negative_cubic_packet : negative_cubic = {(-1,1), (0,1), (1,1)} := by decide +kernel
#print axioms negative_cubic_decomposition
#print axioms negative_cubic_dominating_power
#print axioms negative_cubic_bound
#print axioms negative_cubic_complete
#print axioms negative_cubic_packet

native_runge_power negative_sextic for [1, 1, 0, 0, 0, 0, -1], 3
theorem negative_sextic_packet : negative_sextic = {(-1,-1), (0,1), (1,1)} := by decide +kernel
#print axioms negative_sextic_decomposition
#print axioms negative_sextic_dominating_power
#print axioms negative_sextic_bound
#print axioms negative_sextic_complete
#print axioms negative_sextic_packet

native_runge_power nonmonic_cube for [1, 0, 0, 0, 0, 0, 8], 3
theorem nonmonic_cube_packet : nonmonic_cube = {(0,1)} := by decide +kernel
#print axioms nonmonic_cube_decomposition
#print axioms nonmonic_cube_dominating_power
#print axioms nonmonic_cube_bound
#print axioms nonmonic_cube_complete
#print axioms nonmonic_cube_packet

native_runge_power dense_cube for [2, -4, 8, -8, 6, -3, 1], 3
theorem dense_cube_packet : dense_cube = {} := by decide +kernel
#print axioms dense_cube_decomposition
#print axioms dense_cube_dominating_power
#print axioms dense_cube_bound
#print axioms dense_cube_complete
#print axioms dense_cube_packet

native_runge_power dense_fourth for [1, -3, 9, -16, 19, -15, 10, -4, 1], 4
theorem dense_fourth_packet : dense_fourth = {(0,-1), (0,1)} := by decide +kernel
#print axioms dense_fourth_decomposition
#print axioms dense_fourth_dominating_power
#print axioms dense_fourth_bound
#print axioms dense_fourth_complete
#print axioms dense_fourth_packet

native_runge_power dense_fifth for [1, 0, -1, 0, 0, 1, 5, 11, 10, 5, 1], 5
theorem dense_fifth_packet : dense_fifth = {(-1,-1), (0,1)} := by decide +kernel
#print axioms dense_fifth_decomposition
#print axioms dense_fifth_dominating_power
#print axioms dense_fifth_bound
#print axioms dense_fifth_complete
#print axioms dense_fifth_packet

native_runge_power residual_root for [-10, 1, 0, 0, 0, 0, 1], 3
theorem residual_root_packet : residual_root = {(1,-2), (10,100)} := by decide +kernel
#print axioms residual_root_decomposition
#print axioms residual_root_dominating_power
#print axioms residual_root_bound
#print axioms residual_root_complete
#print axioms residual_root_packet

native_runge_power zero_fibre for [0, 1, 0, 0, 0, 0, 1], 3
theorem zero_fibre_packet : zero_fibre = {(-1,0), (0,0)} := by decide +kernel
#print axioms zero_fibre_decomposition
#print axioms zero_fibre_dominating_power
#print axioms zero_fibre_bound
#print axioms zero_fibre_complete
#print axioms zero_fibre_packet

native_runge_power negative_residual for [-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], 5
theorem negative_residual_packet : negative_residual = {(-1,-1), (0,-1), (1,1)} := by decide +kernel
#print axioms negative_residual_decomposition
#print axioms negative_residual_dominating_power
#print axioms negative_residual_bound
#print axioms negative_residual_complete
#print axioms negative_residual_packet

native_runge_power fractional_finite for [0,0,1,1], 3
theorem fractional_finite_packet : fractional_finite = {(-1,0),(0,0)} := by decide +kernel
#print axioms fractional_finite_decomposition
#print axioms fractional_finite_dominating_power
#print axioms fractional_finite_bound
#print axioms fractional_finite_complete
#print axioms fractional_finite_packet

native_runge_power_certificate fractional_cube for [1,0,0,0,0,1,1], 3
native_runge_power_certificate huge_cube for [1000000000000000000000000000001,1,0,0,0,0,1], 3
native_runge_power exact_cube for [1,3,3,1], 3
native_runge_power exact_fourth for [1,4,6,4,1], 4
native_runge_power exact_negative_fifth for [1,-5,10,-10,5,-1], 5
#print axioms fractional_cube_decomposition
#print axioms fractional_cube_dominating_power
#print axioms fractional_cube_bound
#print axioms fractional_cube_complete
#print axioms huge_cube_decomposition
#print axioms huge_cube_dominating_power
#print axioms huge_cube_bound
#print axioms huge_cube_complete
#print axioms exact_cube_decomposition
#print axioms exact_cube_complete
#print axioms exact_fourth_decomposition
#print axioms exact_fourth_complete
#print axioms exact_negative_fifth_decomposition
#print axioms exact_negative_fifth_complete

-- A genuinely large coordinate survives in the exact zero-residual fibre.
example : (10,100) ∈ residual_root := by decide +kernel
-- Odd powers retain one sign; negative even powers have no roots.
example : PerfectPower.NativePowerRoots.roots 3 (-27) = {-3} := by decide +kernel
example : PerfectPower.NativePowerRoots.roots 4 (-16) = ∅ := by decide +kernel
example : PerfectPower.NativePowerRoots.roots 10 0 = {0} := by decide +kernel
example : PerfectPower.NativePowerRoots.root 1 100000000000000000000 = 100000000000000000000 := by decide +kernel
theorem huge_root : PerfectPower.NativePowerRoots.roots 7 (1000000000000^7) = {1000000000000} := by decide +kernel
#print axioms huge_root
example : PerfectPower.NativePowerRoots.root 7 (1000000000000^7-1) = 999999999999 := by decide +kernel

-- The gap theorem includes opposite signs, not just positive roots.
example : (3 : ℤ)^(3-1) ≤ |(-3)^3-3^3| := by norm_num
example (x y : ℤ) (h : y^3=PerfectPower.NativePolynomialSquare.eval [1,3,3,1] x) : y=x+1 := by
  have hc := (exact_cube_complete x y).mp h
  have ho : ¬Even 3 := by decide +kernel
  rcases hc with hc | hc
  · simpa [PerfectPower.NativePolynomialSquare.eval,add_comm] using hc
  · exact False.elim (ho hc.2)
example : exponent_3 = {(-1,1),(0,1)} := by
  fail_if_success have : exponent_3 = ∅ := by decide +kernel
  exact exponent_3_packet
example : PerfectPower.NativePowerRoots.roots 3 (-27) = {-3} := by
  fail_if_success have : PerfectPower.NativePowerRoots.roots 3 (-27) = {-3,3} := by decide +kernel
  decide +kernel

/-- error: the exponent must be at least two -/
#guard_msgs in
native_runge_power zero_exponent for [1,0,1], 0
/-- error: the exponent must be at least two -/
#guard_msgs in
native_runge_power one_exponent for [1,0,1], 1
/-- error: the polynomial degree must be divisible by the exponent -/
#guard_msgs in
native_runge_power wrong_degree for [1,0,0,0,0,1], 3
/-- error: the leading coefficient is not an integer d-th power -/
#guard_msgs in
native_runge_power wrong_lead for [1,0,0,2], 3
/-- error: the leading coefficient is not an integer d-th power -/
#guard_msgs in
native_runge_power negative_even_lead for [1,0,0,0,-1], 4
/-- error: a nonconstant polynomial is required -/
#guard_msgs in
native_runge_power constant for [1], 3
/-- error: a nonconstant polynomial is required -/
#guard_msgs in
native_runge_power zero for [0,0], 3
/-- error: the complete interval exceeds 10001 coordinates; use native_runge_power_certificate -/
#guard_msgs in
native_runge_power over_budget for [10001,1,0,0,0,0,1], 3

end NativeRungePowerAudit
