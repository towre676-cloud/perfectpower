import PerfectPower.MichorGeometry
namespace PerfectPower.CheckedDifferential.B50cc41bc02200a1463933c51592c90626c434fff6fdb81b205168a23f7b16d40
open PerfectPower.MichorGeometry
theorem source_density_equals (x y : ℝ) : (((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((2 : ℝ)*(x)^2)))/Real.sqrt ((((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((1 : ℝ)*(y)^4))) + (((2 : ℝ)*(x)^2) + (((2 : ℝ)*(x)^2*(y)^2) + ((1 : ℝ)*(x)^4))))=planeDensity x y := by
  have hd : 0 ≤ 1+x*x+y*y := by nlinarith [sq_nonneg x,sq_nonneg y]
  have hp : ((((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((1 : ℝ)*(y)^4))) + (((2 : ℝ)*(x)^2) + (((2 : ℝ)*(x)^2*(y)^2) + ((1 : ℝ)*(x)^4))))=(1+x*x+y*y)^2 := by ring
  rw [hp,Real.sqrt_sq hd]
  unfold planeDensity
  congr 1 <;> ring
theorem density_all_points (x y : ℝ) :
    (1:ℝ)^2 ≤ (((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((2 : ℝ)*(x)^2)))/Real.sqrt ((((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((1 : ℝ)*(y)^4))) + (((2 : ℝ)*(x)^2) + (((2 : ℝ)*(x)^2*(y)^2) + ((1 : ℝ)*(x)^4)))) ∧ (((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((2 : ℝ)*(x)^2)))/Real.sqrt ((((1 : ℝ)) + (((2 : ℝ)*(y)^2) + ((1 : ℝ)*(y)^4))) + (((2 : ℝ)*(x)^2) + (((2 : ℝ)*(x)^2*(y)^2) + ((1 : ℝ)*(x)^4)))) ≤ (3/2:ℝ)^2 := by
  rw [source_density_equals]
  exact plane_rational_scale_bounds x y
#print axioms source_density_equals
#print axioms density_all_points
end PerfectPower.CheckedDifferential.B50cc41bc02200a1463933c51592c90626c434fff6fdb81b205168a23f7b16d40
