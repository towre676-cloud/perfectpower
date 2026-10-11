import PerfectPower.MichorGeometry
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PerfectPower.CheckedDifferential.Dcedfe814d7d0958deda2e1a2e4c7b2d4783ca6bd8e4ed99bfbda640f81b99444
theorem log_gradient_0_denominator (x y : ℝ) : 2*(((1 : ℝ)))*(((1 : ℝ)*(y)^4)) = (((1 : ℝ)))*(((2 : ℝ)*(y)^4)) := by ring
#print axioms log_gradient_0_denominator
theorem log_gradient_0_numerator (x y : ℝ) : 2*((0 : ℝ))*(((1 : ℝ)*(y)^4))-(((1 : ℝ)))*((0 : ℝ)) = ((0 : ℝ))*(((2 : ℝ)*(y)^4)) := by ring
#print axioms log_gradient_0_numerator
theorem log_gradient_0 (x y : ℝ) : ((0 : ℝ))*(2*(((1 : ℝ)))*(((1 : ℝ)*(y)^4)))=(((1 : ℝ)))*(2*((0 : ℝ))*(((1 : ℝ)*(y)^4))-(((1 : ℝ)))*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (2*((0 : ℝ))*(((1 : ℝ)*(y)^4))-(((1 : ℝ)))*((0 : ℝ))) (2*(((1 : ℝ)))*(((1 : ℝ)*(y)^4))) ((0 : ℝ)) (((1 : ℝ))) (((2 : ℝ)*(y)^4))
    (log_gradient_0_denominator x y) (log_gradient_0_numerator x y)
theorem log_hessian_0_0_denominator (x y : ℝ) : (((1 : ℝ)))^2 = (((1 : ℝ)))*(((1 : ℝ))) := by ring
#print axioms log_hessian_0_0_denominator
theorem log_hessian_0_0_numerator (x y : ℝ) : ((0 : ℝ))*(((1 : ℝ)))-((0 : ℝ))*((0 : ℝ)) = ((0 : ℝ))*(((1 : ℝ))) := by ring
#print axioms log_hessian_0_0_numerator
theorem log_hessian_0_0 (x y : ℝ) : ((0 : ℝ))*((((1 : ℝ)))^2)=(((1 : ℝ)))*(((0 : ℝ))*(((1 : ℝ)))-((0 : ℝ))*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (((0 : ℝ))*(((1 : ℝ)))-((0 : ℝ))*((0 : ℝ))) ((((1 : ℝ)))^2) ((0 : ℝ)) (((1 : ℝ))) (((1 : ℝ)))
    (log_hessian_0_0_denominator x y) (log_hessian_0_0_numerator x y)
theorem log_hessian_0_1_denominator (x y : ℝ) : (((1 : ℝ)))^2 = (((1 : ℝ)))*(((1 : ℝ))) := log_hessian_0_0_denominator x y
#print axioms log_hessian_0_1_denominator
theorem log_hessian_0_1_numerator (x y : ℝ) : ((0 : ℝ))*(((1 : ℝ)))-((0 : ℝ))*((0 : ℝ)) = ((0 : ℝ))*(((1 : ℝ))) := log_hessian_0_0_numerator x y
#print axioms log_hessian_0_1_numerator
theorem log_hessian_0_1 (x y : ℝ) : ((0 : ℝ))*((((1 : ℝ)))^2)=(((1 : ℝ)))*(((0 : ℝ))*(((1 : ℝ)))-((0 : ℝ))*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (((0 : ℝ))*(((1 : ℝ)))-((0 : ℝ))*((0 : ℝ))) ((((1 : ℝ)))^2) ((0 : ℝ)) (((1 : ℝ))) (((1 : ℝ)))
    (log_hessian_0_1_denominator x y) (log_hessian_0_1_numerator x y)
theorem log_gradient_1_denominator (x y : ℝ) : 2*(((1 : ℝ)))*(((1 : ℝ)*(y)^4)) = (((1 : ℝ)*(y)^1))*(((2 : ℝ)*(y)^3)) := by ring
#print axioms log_gradient_1_denominator
theorem log_gradient_1_numerator (x y : ℝ) : 2*((0 : ℝ))*(((1 : ℝ)*(y)^4))-(((1 : ℝ)))*(((4 : ℝ)*(y)^3)) = (((-2 : ℝ)))*(((2 : ℝ)*(y)^3)) := by ring
#print axioms log_gradient_1_numerator
theorem log_gradient_1 (x y : ℝ) : (((-2 : ℝ)))*(2*(((1 : ℝ)))*(((1 : ℝ)*(y)^4)))=(((1 : ℝ)*(y)^1))*(2*((0 : ℝ))*(((1 : ℝ)*(y)^4))-(((1 : ℝ)))*(((4 : ℝ)*(y)^3))) :=
  PerfectPower.MichorGeometry.factor_clears (2*((0 : ℝ))*(((1 : ℝ)*(y)^4))-(((1 : ℝ)))*(((4 : ℝ)*(y)^3))) (2*(((1 : ℝ)))*(((1 : ℝ)*(y)^4))) (((-2 : ℝ))) (((1 : ℝ)*(y)^1)) (((2 : ℝ)*(y)^3))
    (log_gradient_1_denominator x y) (log_gradient_1_numerator x y)
theorem log_hessian_1_0_denominator (x y : ℝ) : (((1 : ℝ)*(y)^1))^2 = (((1 : ℝ)))*(((1 : ℝ)*(y)^2)) := by ring
#print axioms log_hessian_1_0_denominator
theorem log_hessian_1_0_numerator (x y : ℝ) : ((0 : ℝ))*(((1 : ℝ)*(y)^1))-(((-2 : ℝ)))*((0 : ℝ)) = ((0 : ℝ))*(((1 : ℝ)*(y)^2)) := by ring
#print axioms log_hessian_1_0_numerator
theorem log_hessian_1_0 (x y : ℝ) : ((0 : ℝ))*((((1 : ℝ)*(y)^1))^2)=(((1 : ℝ)))*(((0 : ℝ))*(((1 : ℝ)*(y)^1))-(((-2 : ℝ)))*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (((0 : ℝ))*(((1 : ℝ)*(y)^1))-(((-2 : ℝ)))*((0 : ℝ))) ((((1 : ℝ)*(y)^1))^2) ((0 : ℝ)) (((1 : ℝ))) (((1 : ℝ)*(y)^2))
    (log_hessian_1_0_denominator x y) (log_hessian_1_0_numerator x y)
theorem log_hessian_1_1_denominator (x y : ℝ) : (((1 : ℝ)*(y)^1))^2 = (((1 : ℝ)*(y)^2))*(((1 : ℝ))) := by ring
#print axioms log_hessian_1_1_denominator
theorem log_hessian_1_1_numerator (x y : ℝ) : ((0 : ℝ))*(((1 : ℝ)*(y)^1))-(((-2 : ℝ)))*(((1 : ℝ))) = (((2 : ℝ)))*(((1 : ℝ))) := by ring
#print axioms log_hessian_1_1_numerator
theorem log_hessian_1_1 (x y : ℝ) : (((2 : ℝ)))*((((1 : ℝ)*(y)^1))^2)=(((1 : ℝ)*(y)^2))*(((0 : ℝ))*(((1 : ℝ)*(y)^1))-(((-2 : ℝ)))*(((1 : ℝ)))) :=
  PerfectPower.MichorGeometry.factor_clears (((0 : ℝ))*(((1 : ℝ)*(y)^1))-(((-2 : ℝ)))*(((1 : ℝ)))) ((((1 : ℝ)*(y)^1))^2) (((2 : ℝ))) (((1 : ℝ)*(y)^2)) (((1 : ℝ)))
    (log_hessian_1_1_denominator x y) (log_hessian_1_1_numerator x y)
theorem connection_0_0_0_denominator (x y : ℝ) : 2*(((1 : ℝ))) = (((1 : ℝ)))*(((2 : ℝ))) := by ring
#print axioms connection_0_0_0_denominator
theorem connection_0_0_0_numerator (x y : ℝ) : 1*((0 : ℝ)) = ((0 : ℝ))*(((2 : ℝ))) := by ring
#print axioms connection_0_0_0_numerator
theorem connection_0_0_0 (x y : ℝ) : ((0 : ℝ))*(2*(((1 : ℝ))))=(((1 : ℝ)))*(1*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (1*((0 : ℝ))) (2*(((1 : ℝ)))) ((0 : ℝ)) (((1 : ℝ))) (((2 : ℝ)))
    (connection_0_0_0_denominator x y) (connection_0_0_0_numerator x y)
theorem connection_0_0_1_denominator (x y : ℝ) : 2*(((1 : ℝ)*(y)^1)) = (((1 : ℝ)*(y)^1))*(((2 : ℝ))) := by ring
#print axioms connection_0_0_1_denominator
theorem connection_0_0_1_numerator (x y : ℝ) : 1*(((-2 : ℝ))) = (((-1 : ℝ)))*(((2 : ℝ))) := by ring
#print axioms connection_0_0_1_numerator
theorem connection_0_0_1 (x y : ℝ) : (((-1 : ℝ)))*(2*(((1 : ℝ)*(y)^1)))=(((1 : ℝ)*(y)^1))*(1*(((-2 : ℝ)))) :=
  PerfectPower.MichorGeometry.factor_clears (1*(((-2 : ℝ)))) (2*(((1 : ℝ)*(y)^1))) (((-1 : ℝ))) (((1 : ℝ)*(y)^1)) (((2 : ℝ)))
    (connection_0_0_1_denominator x y) (connection_0_0_1_numerator x y)
theorem connection_0_1_0_denominator (x y : ℝ) : 2*(((1 : ℝ)*(y)^1)) = (((1 : ℝ)*(y)^1))*(((2 : ℝ))) := connection_0_0_1_denominator x y
#print axioms connection_0_1_0_denominator
theorem connection_0_1_0_numerator (x y : ℝ) : 1*(((-2 : ℝ))) = (((-1 : ℝ)))*(((2 : ℝ))) := connection_0_0_1_numerator x y
#print axioms connection_0_1_0_numerator
theorem connection_0_1_0 (x y : ℝ) : (((-1 : ℝ)))*(2*(((1 : ℝ)*(y)^1)))=(((1 : ℝ)*(y)^1))*(1*(((-2 : ℝ)))) :=
  PerfectPower.MichorGeometry.factor_clears (1*(((-2 : ℝ)))) (2*(((1 : ℝ)*(y)^1))) (((-1 : ℝ))) (((1 : ℝ)*(y)^1)) (((2 : ℝ)))
    (connection_0_1_0_denominator x y) (connection_0_1_0_numerator x y)
theorem connection_0_1_1_denominator (x y : ℝ) : 2*(((1 : ℝ))) = (((1 : ℝ)))*(((2 : ℝ))) := connection_0_0_0_denominator x y
#print axioms connection_0_1_1_denominator
theorem connection_0_1_1_numerator (x y : ℝ) : -1*((0 : ℝ)) = ((0 : ℝ))*(((2 : ℝ))) := by ring
#print axioms connection_0_1_1_numerator
theorem connection_0_1_1 (x y : ℝ) : ((0 : ℝ))*(2*(((1 : ℝ))))=(((1 : ℝ)))*(-1*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (-1*((0 : ℝ))) (2*(((1 : ℝ)))) ((0 : ℝ)) (((1 : ℝ))) (((2 : ℝ)))
    (connection_0_1_1_denominator x y) (connection_0_1_1_numerator x y)
theorem connection_1_0_0_denominator (x y : ℝ) : 2*(((1 : ℝ)*(y)^1)) = (((1 : ℝ)*(y)^1))*(((2 : ℝ))) := connection_0_0_1_denominator x y
#print axioms connection_1_0_0_denominator
theorem connection_1_0_0_numerator (x y : ℝ) : -1*(((-2 : ℝ))) = (((1 : ℝ)))*(((2 : ℝ))) := by ring
#print axioms connection_1_0_0_numerator
theorem connection_1_0_0 (x y : ℝ) : (((1 : ℝ)))*(2*(((1 : ℝ)*(y)^1)))=(((1 : ℝ)*(y)^1))*(-1*(((-2 : ℝ)))) :=
  PerfectPower.MichorGeometry.factor_clears (-1*(((-2 : ℝ)))) (2*(((1 : ℝ)*(y)^1))) (((1 : ℝ))) (((1 : ℝ)*(y)^1)) (((2 : ℝ)))
    (connection_1_0_0_denominator x y) (connection_1_0_0_numerator x y)
theorem connection_1_0_1_denominator (x y : ℝ) : 2*(((1 : ℝ))) = (((1 : ℝ)))*(((2 : ℝ))) := connection_0_0_0_denominator x y
#print axioms connection_1_0_1_denominator
theorem connection_1_0_1_numerator (x y : ℝ) : 1*((0 : ℝ)) = ((0 : ℝ))*(((2 : ℝ))) := connection_0_0_0_numerator x y
#print axioms connection_1_0_1_numerator
theorem connection_1_0_1 (x y : ℝ) : ((0 : ℝ))*(2*(((1 : ℝ))))=(((1 : ℝ)))*(1*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (1*((0 : ℝ))) (2*(((1 : ℝ)))) ((0 : ℝ)) (((1 : ℝ))) (((2 : ℝ)))
    (connection_1_0_1_denominator x y) (connection_1_0_1_numerator x y)
theorem connection_1_1_0_denominator (x y : ℝ) : 2*(((1 : ℝ))) = (((1 : ℝ)))*(((2 : ℝ))) := connection_0_0_0_denominator x y
#print axioms connection_1_1_0_denominator
theorem connection_1_1_0_numerator (x y : ℝ) : 1*((0 : ℝ)) = ((0 : ℝ))*(((2 : ℝ))) := connection_0_0_0_numerator x y
#print axioms connection_1_1_0_numerator
theorem connection_1_1_0 (x y : ℝ) : ((0 : ℝ))*(2*(((1 : ℝ))))=(((1 : ℝ)))*(1*((0 : ℝ))) :=
  PerfectPower.MichorGeometry.factor_clears (1*((0 : ℝ))) (2*(((1 : ℝ)))) ((0 : ℝ)) (((1 : ℝ))) (((2 : ℝ)))
    (connection_1_1_0_denominator x y) (connection_1_1_0_numerator x y)
theorem connection_1_1_1_denominator (x y : ℝ) : 2*(((1 : ℝ)*(y)^1)) = (((1 : ℝ)*(y)^1))*(((2 : ℝ))) := connection_0_0_1_denominator x y
#print axioms connection_1_1_1_denominator
theorem connection_1_1_1_numerator (x y : ℝ) : 1*(((-2 : ℝ))) = (((-1 : ℝ)))*(((2 : ℝ))) := connection_0_0_1_numerator x y
#print axioms connection_1_1_1_numerator
theorem connection_1_1_1 (x y : ℝ) : (((-1 : ℝ)))*(2*(((1 : ℝ)*(y)^1)))=(((1 : ℝ)*(y)^1))*(1*(((-2 : ℝ)))) :=
  PerfectPower.MichorGeometry.factor_clears (1*(((-2 : ℝ)))) (2*(((1 : ℝ)*(y)^1))) (((-1 : ℝ))) (((1 : ℝ)*(y)^1)) (((2 : ℝ)))
    (connection_1_1_1_denominator x y) (connection_1_1_1_numerator x y)
theorem curvature_x_denominator (x y : ℝ) : ((1 : ℝ)*(y)^2) = (((1 : ℝ)))*(((1 : ℝ)*(y)^2)) := by ring
#print axioms curvature_x_denominator
theorem curvature_y_denominator (x y : ℝ) : ((1 : ℝ)*(y)^2) = (((1 : ℝ)*(y)^2))*(((1 : ℝ))) := by ring
#print axioms curvature_y_denominator
theorem curvature_times_density_denominator (x y : ℝ) : 2*(((1 : ℝ)*(y)^2)) = (((1 : ℝ)*(y)^2))*(((2 : ℝ))) := by ring
#print axioms curvature_times_density_denominator
theorem curvature_times_density_numerator (x y : ℝ) : -(((0 : ℝ))*(((1 : ℝ)*(y)^2))+(((2 : ℝ)))*(((1 : ℝ)))) = (((-1 : ℝ)))*(((2 : ℝ))) := by ring
#print axioms curvature_times_density_numerator
theorem curvature_times_density (x y : ℝ) : (((-1 : ℝ)))*(2*(((1 : ℝ)*(y)^2)))=(((1 : ℝ)*(y)^2))*(-(((0 : ℝ))*(((1 : ℝ)*(y)^2))+(((2 : ℝ)))*(((1 : ℝ))))) :=
  PerfectPower.MichorGeometry.factor_clears (-(((0 : ℝ))*(((1 : ℝ)*(y)^2))+(((2 : ℝ)))*(((1 : ℝ))))) (2*(((1 : ℝ)*(y)^2))) (((-1 : ℝ))) (((1 : ℝ)*(y)^2)) (((2 : ℝ)))
    (curvature_times_density_denominator x y) (curvature_times_density_numerator x y)
#print axioms log_gradient_0
#print axioms log_gradient_1
#print axioms connection_0_0_0
#print axioms curvature_times_density
end PerfectPower.CheckedDifferential.Dcedfe814d7d0958deda2e1a2e4c7b2d4783ca6bd8e4ed99bfbda640f81b99444
