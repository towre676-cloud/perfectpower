import PerfectPower.Tactic.NativePolynomialPower

set_option maxRecDepth 100000

namespace PerfectPower.NativePolynomialAudit
open NativePolynomialSquare

native_polynomial_square nonmonic_cubic for [0, 0, 0, 2], 1
native_polynomial_square sextic_eight for [0, 0, 0, 1], 8
native_polynomial_square sextic_minus_one for [0, 0, 0, 1], -1
native_polynomial_square degree_fourteen for [0, 0, 0, 0, 0, 0, 0, -3], 7
native_polynomial_square shifted_cubic for [-1, -1, 1, 1], 1
native_polynomial_square empty_nonmonic for [0, 0, -2], -1
native_polynomial_square million_shift for [1000000, 1], 1
native_polynomial_square repeated_roots for [4, -4, 1], 1
native_polynomial_square negative_shift for [-1000000, -1], 1

example : nonmonic_cubic = {(0, -1), (0, 1)} := by decide +kernel
example : sextic_eight = {(-1, -3), (-1, 3), (1, -3), (1, 3)} := by decide +kernel
example : sextic_minus_one = {(-1, 0), (1, 0)} := by decide +kernel
example : degree_fourteen = {(-1, -4), (-1, 4), (1, -4), (1, 4)} := by decide +kernel
example : shifted_cubic = {(-1, -1), (-1, 1), (1, -1), (1, 1)} := by decide +kernel
example : empty_nonmonic = ∅ := by decide +kernel
example : million_shift = {(-1000000, -1), (-1000000, 1)} := by decide +kernel
example : repeated_roots = {(2, -1), (2, 1)} := by decide +kernel
example : negative_shift = {(-1000000, -1), (-1000000, 1)} := by decide +kernel

/-- The generated result also proves the equation in standard expanded notation. -/
theorem expanded_nonmonic (x y : ℤ) : y^2 = 4*x^6+1 ↔ (x,y) ∈ nonmonic_cubic := by
  have h := nonmonic_cubic_complete x y
  simp only [eval] at h
  convert h using 1
  ring_nf

/-- error: at least two coefficients are required for a nonconstant polynomial -/
#guard_msgs in
native_polynomial_square reject_constant for [3], 1

/-- error: the final coefficient must be nonzero; remove trailing zeros -/
#guard_msgs in
native_polynomial_square reject_leading_zero for [1, 2, 0], 1

/-- error: k = 0 is an infinite square family; no finite list is emitted -/
#guard_msgs in
native_polynomial_square reject_infinite for [0, 1], 0

example (x y : ℤ) : y^2 = (eval [0,0,0,2] x)^2+1 ↔ (x,y) ∈ nonmonic_cubic := by
  fail_if_success decide_polynomial_square [0,0,0,2], 1 => (∅ : Finset (ℤ × ℤ))
  decide_polynomial_square [0,0,0,2], 1 => nonmonic_cubic

#print axioms eval_abs_ge_one
#print axioms eval_bound
#print axioms complete
#print axioms polynomial_complete
#print axioms nonmonic_cubic_complete
#print axioms sextic_eight_complete
#print axioms sextic_minus_one_complete
#print axioms degree_fourteen_complete
#print axioms shifted_cubic_complete
#print axioms empty_nonmonic_complete
#print axioms expanded_nonmonic
#print axioms PerfectPower.FastDivisors.mem_divisors
#print axioms PerfectPower.FastDivisors.sqrt_eq
#print axioms PerfectPower.NativePolynomialRoots.complete
#print axioms PerfectPower.NativeDivisorSquare.complete
#print axioms PerfectPower.NativeDivisorSquare.rectangle_eq
#print axioms million_shift_complete
end PerfectPower.NativePolynomialAudit
