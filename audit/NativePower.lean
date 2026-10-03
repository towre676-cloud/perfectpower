import PerfectPower.Tactic.NativePower
import PerfectPower.FunctionFieldPower

namespace PerfectPower.NativePowerExamples

native_near_square quartic_one for 0, 0, 1
native_near_square shifted_four for 1, 0, 4
native_near_square quartic_minus_one for 0, 0, -1
native_near_square quartic_eight for 0, 0, 8
native_near_square empty_shift for 0, -2, 1
native_near_square large_shift for 23, -117, 8

theorem quartic_one_list : quartic_one = {(0,1),(0,-1)} := by decide +kernel
theorem shifted_four_list : shifted_four = {(0,2),(0,-2),(-1,2),(-1,-2)} := by decide +kernel
theorem quartic_minus_one_list : quartic_minus_one = {(-1,0),(1,0)} := by decide +kernel
theorem quartic_eight_list : quartic_eight = {(-1,3),(-1,-3),(1,3),(1,-3)} := by decide +kernel
theorem empty_shift_list : empty_shift = ∅ := by decide +kernel

#print axioms quartic_one_complete
#print axioms shifted_four_complete
#print axioms quartic_minus_one_complete
#print axioms quartic_eight_complete
#print axioms empty_shift_complete
#print axioms large_shift_complete
#print axioms NativeNearSquare.explicit_bounds
#print axioms NativeNearSquare.complete
#print axioms FunctionFieldPower.complete
#print axioms FunctionFieldPower.frobenius_family
#print axioms FunctionFieldPower.Seven.quartic_complete
#print axioms FunctionFieldPower.Seven.quartic_list

/-- error: k = 0 is an infinite square family; no finite list is emitted -/
#guard_msgs in
native_near_square rejected_zero for 0, 0, 0

example (x y : ℤ) : NativeNearSquare.equation 0 0 1 x y ↔ (x,y) ∈ quartic_one := by
  fail_if_success decide_perfect_power 0, 0, 1 => (∅ : Finset (ℤ × ℤ))
  decide_perfect_power 0, 0, 1 => quartic_one

end PerfectPower.NativePowerExamples
