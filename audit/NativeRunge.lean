import PerfectPower.Tactic.RungePolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace NativeRungeAudit
#print axioms PerfectPower.RungePolynomial.degree_domination
#print axioms PerfectPower.RungePolynomial.bound_or_residual_zero
#print axioms PerfectPower.RungePolynomial.coordinate_bound
#print axioms PerfectPower.RungePolynomial.complete
#print axioms PerfectPower.RungePolynomial.square_family

native_runge quadratic for [1, 1, 1]
theorem quadratic_packet : quadratic = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms quadratic_decomposition
#print axioms quadratic_bound
#print axioms quadratic_complete
#print axioms quadratic_packet

native_runge quartic for [1, 1, 0, 0, 1]
theorem quartic_packet : quartic = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms quartic_decomposition
#print axioms quartic_bound
#print axioms quartic_complete
#print axioms quartic_packet

native_runge sextic for [1, 1, 0, 0, 0, 0, 1]
theorem sextic_packet : sextic = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms sextic_decomposition
#print axioms sextic_bound
#print axioms sextic_complete
#print axioms sextic_packet

native_runge octic for [1, 1, 0, 0, 0, 0, 0, 0, 1]
theorem octic_packet : octic = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms octic_decomposition
#print axioms octic_bound
#print axioms octic_complete
#print axioms octic_packet

native_runge decic for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
theorem decic_packet : decic = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms decic_decomposition
#print axioms decic_bound
#print axioms decic_complete
#print axioms decic_packet

native_runge degree14 for [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]
theorem degree14_packet : degree14 = {(-1,-4), (-1,4), (1,-4), (1,4)} := by decide +kernel
#print axioms degree14_decomposition
#print axioms degree14_bound
#print axioms degree14_complete
#print axioms degree14_packet

native_runge degree20 for [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
theorem degree20_packet : degree20 = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms degree20_decomposition
#print axioms degree20_bound
#print axioms degree20_complete
#print axioms degree20_packet

native_runge nonmonic for [1, 0, 0, 0, 0, 0, 4]
theorem nonmonic_packet : nonmonic = {(0,-1), (0,1)} := by decide +kernel
#print axioms nonmonic_decomposition
#print axioms nonmonic_bound
#print axioms nonmonic_complete
#print axioms nonmonic_packet

native_runge fractional for [0, 0, 0, 0, 1, 0, 1]
theorem fractional_packet : fractional = {(0,0)} := by decide +kernel
#print axioms fractional_decomposition
#print axioms fractional_bound
#print axioms fractional_complete
#print axioms fractional_packet

native_runge quartic_fractional for [0, 0, 0, 1, 1]
theorem quartic_fractional_packet : quartic_fractional = {(-1,0), (0,0)} := by decide +kernel
#print axioms quartic_fractional_decomposition
#print axioms quartic_fractional_bound
#print axioms quartic_fractional_complete
#print axioms quartic_fractional_packet

native_runge residual_root for [-10, 1, 0, 0, 0, 0, 1]
theorem residual_root_packet : residual_root = {(10,-1000), (10,1000)} := by decide +kernel
#print axioms residual_root_decomposition
#print axioms residual_root_bound
#print axioms residual_root_complete
#print axioms residual_root_packet

native_runge negative for [-1, 1, 0, 0, 0, 0, 1]
theorem negative_packet : negative = {(1,-1), (1,1)} := by decide +kernel
#print axioms negative_decomposition
#print axioms negative_bound
#print axioms negative_complete
#print axioms negative_packet

native_runge zero_fibre for [0, 1, 0, 0, 0, 0, 1]
theorem zero_fibre_packet : zero_fibre = {(-1,0), (0,0)} := by decide +kernel
#print axioms zero_fibre_decomposition
#print axioms zero_fibre_bound
#print axioms zero_fibre_complete
#print axioms zero_fibre_packet

native_runge trailing_zero for [1, 1, 0, 0, 0, 0, 1, 0, 0]
theorem trailing_zero_packet : trailing_zero = {(-1,-1), (-1,1), (0,-1), (0,1)} := by decide +kernel
#print axioms trailing_zero_decomposition
#print axioms trailing_zero_bound
#print axioms trailing_zero_complete
#print axioms trailing_zero_packet

native_runge dense_octic for [2, 0, 4, -3, 6, -2, 4, 0, 1]
theorem dense_octic_packet : dense_octic = {} := by decide +kernel
#print axioms dense_octic_decomposition
#print axioms dense_octic_bound
#print axioms dense_octic_complete
#print axioms dense_octic_packet

native_runge dense_decic for [1, 3, 2, -2, 2, 8, 6, -4, 1, 4, 4]
theorem dense_decic_packet : dense_decic = {(0,-1), (0,1), (1,-5), (1,5)} := by decide +kernel
#print axioms dense_decic_decomposition
#print axioms dense_decic_bound
#print axioms dense_decic_complete
#print axioms dense_decic_packet

native_runge_certificate dense_fractional for [1,0,0,0,0,1,1]
native_runge_certificate huge_bound for [1000000000000000000000000000001,1,0,0,0,0,1]
native_runge exact_square for [1,2,1,2,2,0,1]
native_runge exact_nonmonic for [0,0,0,0,0,0,4]
#print axioms dense_fractional_decomposition
#print axioms dense_fractional_bound
#print axioms dense_fractional_complete
#print axioms huge_bound_decomposition
#print axioms huge_bound_bound
#print axioms huge_bound_complete
#print axioms exact_square_decomposition
#print axioms exact_square_complete
#print axioms exact_nonmonic_decomposition
#print axioms exact_nonmonic_complete

-- The original equation rejects the extra scaled points of the square completion.
example : (1,1) ∉ fractional := by decide +kernel
example : (10,1000) ∈ residual_root := by decide +kernel
example : (-1,0) ∈ zero_fibre := by decide +kernel
example : (2000000 : ℤ)^2=PerfectPower.NativePolynomialSquare.eval [0,0,0,0,0,0,4] 100 := by
  norm_num [PerfectPower.NativePolynomialSquare.eval]

-- False packets and identities cannot be certified by the trusted kernel.
example : sextic = {(-1,-1),(-1,1),(0,-1),(0,1)} := by
  fail_if_success have : sextic = ∅ := by decide +kernel
  exact sextic_packet
example (x : ℤ) : PerfectPower.NativePolynomialSquare.eval [1,1,0,0,0,0,1] x =
    (x^3)^2+x+1 := by
  fail_if_success have : PerfectPower.NativePolynomialSquare.eval [1,1,0,0,0,0,1] x =
      (x^3)^2+x := by norm_num [PerfectPower.NativePolynomialSquare.eval]; ring
  norm_num [PerfectPower.NativePolynomialSquare.eval]
  ring

/-- error: odd degree is outside this Runge recognizer -/
#guard_msgs in
native_runge odd_degree for [1,0,0,1]
/-- error: the leading coefficient is not an integer square -/
#guard_msgs in
native_runge nonsquare_lead for [1,0,2]
/-- error: a positive square leading coefficient is required -/
#guard_msgs in
native_runge negative_lead for [1,0,-1]
/-- error: a nonconstant polynomial of positive even degree is required -/
#guard_msgs in
native_runge constant for [1]
/-- error: a nonconstant polynomial of positive even degree is required -/
#guard_msgs in
native_runge zero for [0,0,0]
/-- error: the complete interval exceeds 10001 coordinates; use native_runge_certificate for the decomposition and bound -/
#guard_msgs in
native_runge over_budget for [10001,1,0,0,0,0,1]

end NativeRungeAudit
