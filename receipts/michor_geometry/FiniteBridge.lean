import PerfectPower.MichorGeometry
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PerfectPower.CheckedDifferential.Baf150a87b9cbfb00c089f6623609c94cb1d9b1816b648c93cda5b9ac75400d4e
open PerfectPower.MichorGeometry
theorem density_entire_rectangle (x y : ℝ) (hx0 : (2 : ℝ) ≤ x) (hx1 : x ≤ ((9 : ℝ)/4))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ)/4)) :
    ((1 : ℝ)/4)^2 < (((1 : ℝ)) + (((1 : ℝ)*(y)^2) + ((1 : ℝ)*(x)^2)))/Real.sqrt (((((1 : ℝ)*(y)^2) + (((-2 : ℝ)*(y)^6) + ((1 : ℝ)*(y)^10))) + (((1 : ℝ)*(x)^2) + (((10 : ℝ)*(x)^2*(y)^4) + ((5 : ℝ)*(x)^2*(y)^8)))) + ((((10 : ℝ)*(x)^4*(y)^2) + (((10 : ℝ)*(x)^4*(y)^6) + ((-2 : ℝ)*(x)^6))) + (((10 : ℝ)*(x)^6*(y)^4) + (((5 : ℝ)*(x)^8*(y)^2) + ((1 : ℝ)*(x)^10))))) ∧ (((1 : ℝ)) + (((1 : ℝ)*(y)^2) + ((1 : ℝ)*(x)^2)))/Real.sqrt (((((1 : ℝ)*(y)^2) + (((-2 : ℝ)*(y)^6) + ((1 : ℝ)*(y)^10))) + (((1 : ℝ)*(x)^2) + (((10 : ℝ)*(x)^2*(y)^4) + ((5 : ℝ)*(x)^2*(y)^8)))) + ((((10 : ℝ)*(x)^4*(y)^2) + (((10 : ℝ)*(x)^4*(y)^6) + ((-2 : ℝ)*(x)^6))) + (((10 : ℝ)*(x)^6*(y)^4) + (((5 : ℝ)*(x)^8*(y)^2) + ((1 : ℝ)*(x)^10))))) < (1 : ℝ)^2 := by
  let z : ℂ := ⟨x,y⟩
  have hz : ‖z‖^2=x*x+y*y := complex_chart_norm x y
  have hn : (((1 : ℝ)) + (((1 : ℝ)*(y)^2) + ((1 : ℝ)*(x)^2)))=1+‖z‖^2 := by rw [hz]; ring
  have hd : (((((1 : ℝ)*(y)^2) + (((-2 : ℝ)*(y)^6) + ((1 : ℝ)*(y)^10))) + (((1 : ℝ)*(x)^2) + (((10 : ℝ)*(x)^2*(y)^4) + ((5 : ℝ)*(x)^2*(y)^8)))) + ((((10 : ℝ)*(x)^4*(y)^2) + (((10 : ℝ)*(x)^4*(y)^6) + ((-2 : ℝ)*(x)^6))) + (((10 : ℝ)*(x)^6*(y)^4) + (((5 : ℝ)*(x)^8*(y)^2) + ((1 : ℝ)*(x)^10)))))=‖z^5-z‖^2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply,z,pow_succ,Complex.mul_re,Complex.mul_im]
    <;> ring
  rw [hd,Real.sqrt_sq (norm_nonneg _),hn]
  have hxL := mul_nonneg (by linarith : 0 ≤ x-2) (by linarith : 0 ≤ x+2)
  have hxU := mul_nonneg (by linarith : 0 ≤ (9/4:ℝ)-x) (by linarith : 0 ≤ (9/4:ℝ)+x)
  have hyU := mul_nonneg (by linarith : 0 ≤ (1/4:ℝ)-y) (by linarith : 0 ≤ (1/4:ℝ)+y)
  have h0 : 2 ≤ ‖z‖ := by nlinarith [sq_nonneg y,norm_nonneg z]
  have h1 : ‖z‖ ≤ (23/10:ℝ) := by nlinarith [norm_nonneg z]
  simpa only [one_pow] using finite_norm_density z h0 h1
#print axioms density_entire_rectangle
end PerfectPower.CheckedDifferential.Baf150a87b9cbfb00c089f6623609c94cb1d9b1816b648c93cda5b9ac75400d4e
