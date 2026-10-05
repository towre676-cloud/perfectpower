import PerfectPower.BernsteinBoxes
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
namespace PerfectPower.MetricBoxExamples
open PerfectPower.BernsteinBoxes
theorem square_cube_side_node_0 (x y : ℝ) (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hy0 : (-10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ y) (hy1 : y ≤ (10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) : 0 < ((1 : ℝ) + (2 : ℝ)*(x)^1 + (1 : ℝ)*(x)^2 + (-1 : ℝ)*(x)^3) := by
  let coeff : Fin 4 → Fin 1 → ℚ := ![![(1 : ℚ)], ![(5 : ℚ)], ![(8 : ℚ)], ![(3 : ℚ)]]
  have hc : ∀ i j, 0 < coeff i j := by
    decide +kernel
  have hid : ∀ s t : ℝ,
      (fun x y : ℝ => ((1 : ℝ) + (2 : ℝ)*(x)^1 + (1 : ℝ)*(x)^2 + (-1 : ℝ)*(x)^3)) ((0 : ℝ)+((1 : ℝ))*s)
        ((-10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)+((20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ))*t) = tensor 3 0 coeff s t := by
    intro s t
    norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring
  exact rectangle_positive (fun x y : ℝ => ((1 : ℝ) + (2 : ℝ)*(x)^1 + (1 : ℝ)*(x)^2 + (-1 : ℝ)*(x)^3))
    (0 : ℝ) (1 : ℝ) (-10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) (10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) (by norm_num) (by norm_num)
    3 0 coeff hc (by intro s t; convert hid s t using 1 <;> ring) x y hx0 hx1 hy0 hy1

abbrev square_cube_side := square_cube_side_node_0

theorem square_cube_side_no_common_zero (x y : ℝ) (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hy0 : (-10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ y) (hy1 : y ≤ (10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) : ¬(((1 : ℝ)*(y)^2 + (-1 : ℝ)*(x)^3)=0 ∧ ((-1 : ℝ) + (1 : ℝ)*(y)^1 + (-1 : ℝ)*(x)^1)=0) := by
  rintro ⟨h0,h1⟩
  have hp := square_cube_side x y hx0 hx1 hy0 hy1
  have hid : ((1 : ℝ) + (2 : ℝ)*(x)^1 + (1 : ℝ)*(x)^2 + (-1 : ℝ)*(x)^3)=((1 : ℝ)*((1 : ℝ))*((1 : ℝ)*(y)^2 + (-1 : ℝ)*(x)^3) + (1 : ℝ)*((-1 : ℝ) + (-1 : ℝ)*(y)^1 + (-1 : ℝ)*(x)^1)*((-1 : ℝ) + (1 : ℝ)*(y)^1 + (-1 : ℝ)*(x)^1)) := by ring
  rw [hid] at hp
  rw [h0, h1] at hp
  norm_num at hp

#print axioms square_cube_side_node_0
#print axioms square_cube_side_no_common_zero
end PerfectPower.MetricBoxExamples
