import PerfectPower.Tactic.RungePolynomial
import PerfectPower.Tactic.RungePower
native_runge square_route for [1,1,0,0,0,0,1]
native_runge_power power_route for [1,1,0,0,0,0,1], 2
theorem same_square_packet : square_route=power_route := by decide +kernel
#print axioms same_square_packet
example : PerfectPower.NativePowerRoots.roots 2 121 = PerfectPower.LinearPerturbation.squareRoots 121 := by decide +kernel
