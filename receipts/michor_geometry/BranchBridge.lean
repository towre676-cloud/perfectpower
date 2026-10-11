import PerfectPower.MichorGeometry
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PerfectPower.CheckedDifferential.Bc789f0ba345f96a7b0854ddf8138d5b88d5c4f938cd838775cc4afe21ce38437
open PerfectPower.MichorGeometry
theorem density_entire_rectangle (x y : ℝ) (hx0 : ((-1 : ℝ)/4) ≤ x) (hx1 : x ≤ ((1 : ℝ)/4))
    (hy0 : ((-1 : ℝ)/4) ≤ y) (hy1 : y ≤ ((1 : ℝ)/4)) :
    (1 : ℝ)^2 < ((((4 : ℝ)) + ((4 : ℝ)*(y)^4)) + (((8 : ℝ)*(x)^2*(y)^2) + ((4 : ℝ)*(x)^4)))/Real.sqrt (((((1 : ℝ)) + (((-2 : ℝ)*(y)^8) + ((1 : ℝ)*(y)^16))) + ((((56 : ℝ)*(x)^2*(y)^6) + ((8 : ℝ)*(x)^2*(y)^14)) + (((-140 : ℝ)*(x)^4*(y)^4) + ((28 : ℝ)*(x)^4*(y)^12)))) + (((((56 : ℝ)*(x)^6*(y)^2) + ((56 : ℝ)*(x)^6*(y)^10)) + (((-2 : ℝ)*(x)^8) + ((70 : ℝ)*(x)^8*(y)^8))) + ((((56 : ℝ)*(x)^10*(y)^6) + ((28 : ℝ)*(x)^12*(y)^4)) + (((8 : ℝ)*(x)^14*(y)^2) + ((1 : ℝ)*(x)^16))))) ∧ ((((4 : ℝ)) + ((4 : ℝ)*(y)^4)) + (((8 : ℝ)*(x)^2*(y)^2) + ((4 : ℝ)*(x)^4)))/Real.sqrt (((((1 : ℝ)) + (((-2 : ℝ)*(y)^8) + ((1 : ℝ)*(y)^16))) + ((((56 : ℝ)*(x)^2*(y)^6) + ((8 : ℝ)*(x)^2*(y)^14)) + (((-140 : ℝ)*(x)^4*(y)^4) + ((28 : ℝ)*(x)^4*(y)^12)))) + (((((56 : ℝ)*(x)^6*(y)^2) + ((56 : ℝ)*(x)^6*(y)^10)) + (((-2 : ℝ)*(x)^8) + ((70 : ℝ)*(x)^8*(y)^8))) + ((((56 : ℝ)*(x)^10*(y)^6) + ((28 : ℝ)*(x)^12*(y)^4)) + (((8 : ℝ)*(x)^14*(y)^2) + ((1 : ℝ)*(x)^16))))) < (3 : ℝ)^2 := by
  let z : ℂ := ⟨x,y⟩
  have hz : ‖z‖^2=x*x+y*y := complex_chart_norm x y
  have hn : ((((4 : ℝ)) + ((4 : ℝ)*(y)^4)) + (((8 : ℝ)*(x)^2*(y)^2) + ((4 : ℝ)*(x)^4)))=4*(1+‖z‖^4) := by rw [show ‖z‖^4=(‖z‖^2)^2 by ring,hz]; ring
  have hd : (((((1 : ℝ)) + (((-2 : ℝ)*(y)^8) + ((1 : ℝ)*(y)^16))) + ((((56 : ℝ)*(x)^2*(y)^6) + ((8 : ℝ)*(x)^2*(y)^14)) + (((-140 : ℝ)*(x)^4*(y)^4) + ((28 : ℝ)*(x)^4*(y)^12)))) + (((((56 : ℝ)*(x)^6*(y)^2) + ((56 : ℝ)*(x)^6*(y)^10)) + (((-2 : ℝ)*(x)^8) + ((70 : ℝ)*(x)^8*(y)^8))) + ((((56 : ℝ)*(x)^10*(y)^6) + ((28 : ℝ)*(x)^12*(y)^4)) + (((8 : ℝ)*(x)^14*(y)^2) + ((1 : ℝ)*(x)^16)))))=‖z^8-1‖^2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply,z,pow_succ,Complex.mul_re,Complex.mul_im]
    <;> ring
  rw [hd,Real.sqrt_sq (norm_nonneg _),hn]
  have hxU := mul_nonneg (by linarith : 0 ≤ (1/4:ℝ)-x) (by linarith : 0 ≤ (1/4:ℝ)+x)
  have hyU := mul_nonneg (by linarith : 0 ≤ (1/4:ℝ)-y) (by linarith : 0 ≤ (1/4:ℝ)+y)
  have h1 : ‖z‖ ≤ (1/2:ℝ) := by nlinarith [norm_nonneg z]
  convert branch_norm_density z h1 using 1 <;> norm_num
#print axioms density_entire_rectangle
end PerfectPower.CheckedDifferential.Bc789f0ba345f96a7b0854ddf8138d5b88d5c4f938cd838775cc4afe21ce38437
