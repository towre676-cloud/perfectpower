import PerfectPower.BernsteinBoxes
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
namespace PerfectPower.MetricBoxExamples
open PerfectPower.BernsteinBoxes
theorem adaptive_quadratic_node_6 (x y : ℝ) (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ (1 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  let coeff : Fin 3 → Fin 3 → ℚ := ![![((1 : ℚ)/4), ((1 : ℚ)/2), ((5 : ℚ)/4)], ![((1 : ℚ)/2), (1 : ℚ), ((5 : ℚ)/2)], ![((5 : ℚ)/4), ((5 : ℚ)/2), ((9 : ℚ)/4)]]
  have hc : ∀ i j, 0 < coeff i j := by
    decide +kernel
  have hid : ∀ s t : ℝ,
      (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2)) ((0 : ℝ)+((1 : ℝ))*s)
        ((0 : ℝ)+((1 : ℝ))*t) = tensor 2 2 coeff s t := by
    intro s t
    norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring
  exact rectangle_positive (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2))
    (0 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    2 2 coeff hc (by intro s t; convert hid s t using 1 <;> ring) x y hx0 hx1 hy0 hy1

theorem adaptive_quadratic_node_5 (x y : ℝ) (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hy0 : (-1 : ℝ) ≤ y) (hy1 : y ≤ (0 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  let coeff : Fin 3 → Fin 3 → ℚ := ![![((5 : ℚ)/4), ((1 : ℚ)/2), ((1 : ℚ)/4)], ![((5 : ℚ)/2), (1 : ℚ), ((1 : ℚ)/2)], ![((9 : ℚ)/4), ((5 : ℚ)/2), ((5 : ℚ)/4)]]
  have hc : ∀ i j, 0 < coeff i j := by
    decide +kernel
  have hid : ∀ s t : ℝ,
      (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2)) ((0 : ℝ)+((1 : ℝ))*s)
        ((-1 : ℝ)+((1 : ℝ))*t) = tensor 2 2 coeff s t := by
    intro s t
    norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring
  exact rectangle_positive (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2))
    (0 : ℝ) (1 : ℝ) (-1 : ℝ) (0 : ℝ) (by norm_num) (by norm_num)
    2 2 coeff hc (by intro s t; convert hid s t using 1 <;> ring) x y hx0 hx1 hy0 hy1

theorem adaptive_quadratic_node_4 (x y : ℝ) (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hy0 : (-1 : ℝ) ≤ y) (hy1 : y ≤ (1 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  by_cases hmid : y ≤ (0 : ℝ)
  · exact adaptive_quadratic_node_5 x y hx0 hx1 hy0 hmid
  · exact adaptive_quadratic_node_6 x y hx0 hx1 (by linarith) hy1

theorem adaptive_quadratic_node_3 (x y : ℝ) (hx0 : (-1 : ℝ) ≤ x) (hx1 : x ≤ (0 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ (1 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  let coeff : Fin 3 → Fin 3 → ℚ := ![![((5 : ℚ)/4), ((5 : ℚ)/2), ((9 : ℚ)/4)], ![((1 : ℚ)/2), (1 : ℚ), ((5 : ℚ)/2)], ![((1 : ℚ)/4), ((1 : ℚ)/2), ((5 : ℚ)/4)]]
  have hc : ∀ i j, 0 < coeff i j := by
    decide +kernel
  have hid : ∀ s t : ℝ,
      (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2)) ((-1 : ℝ)+((1 : ℝ))*s)
        ((0 : ℝ)+((1 : ℝ))*t) = tensor 2 2 coeff s t := by
    intro s t
    norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring
  exact rectangle_positive (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2))
    (-1 : ℝ) (0 : ℝ) (0 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    2 2 coeff hc (by intro s t; convert hid s t using 1 <;> ring) x y hx0 hx1 hy0 hy1

theorem adaptive_quadratic_node_2 (x y : ℝ) (hx0 : (-1 : ℝ) ≤ x) (hx1 : x ≤ (0 : ℝ))
    (hy0 : (-1 : ℝ) ≤ y) (hy1 : y ≤ (0 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  let coeff : Fin 3 → Fin 3 → ℚ := ![![((9 : ℚ)/4), ((5 : ℚ)/2), ((5 : ℚ)/4)], ![((5 : ℚ)/2), (1 : ℚ), ((1 : ℚ)/2)], ![((5 : ℚ)/4), ((1 : ℚ)/2), ((1 : ℚ)/4)]]
  have hc : ∀ i j, 0 < coeff i j := by
    decide +kernel
  have hid : ∀ s t : ℝ,
      (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2)) ((-1 : ℝ)+((1 : ℝ))*s)
        ((-1 : ℝ)+((1 : ℝ))*t) = tensor 2 2 coeff s t := by
    intro s t
    norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring
  exact rectangle_positive (fun x y : ℝ => (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2))
    (-1 : ℝ) (0 : ℝ) (-1 : ℝ) (0 : ℝ) (by norm_num) (by norm_num)
    2 2 coeff hc (by intro s t; convert hid s t using 1 <;> ring) x y hx0 hx1 hy0 hy1

theorem adaptive_quadratic_node_1 (x y : ℝ) (hx0 : (-1 : ℝ) ≤ x) (hx1 : x ≤ (0 : ℝ))
    (hy0 : (-1 : ℝ) ≤ y) (hy1 : y ≤ (1 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  by_cases hmid : y ≤ (0 : ℝ)
  · exact adaptive_quadratic_node_2 x y hx0 hx1 hy0 hmid
  · exact adaptive_quadratic_node_3 x y hx0 hx1 (by linarith) hy1

theorem adaptive_quadratic_node_0 (x y : ℝ) (hx0 : (-1 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hy0 : (-1 : ℝ) ≤ y) (hy1 : y ≤ (1 : ℝ)) : 0 < (((1 : ℝ)/4) + (1 : ℝ)*(y)^2 + (1 : ℝ)*(x)^2) := by
  by_cases hmid : x ≤ (0 : ℝ)
  · exact adaptive_quadratic_node_1 x y hx0 hmid hy0 hy1
  · exact adaptive_quadratic_node_4 x y (by linarith) hx1 hy0 hy1

abbrev adaptive_quadratic := adaptive_quadratic_node_0

#print axioms adaptive_quadratic_node_6
#print axioms adaptive_quadratic_node_5
#print axioms adaptive_quadratic_node_4
#print axioms adaptive_quadratic_node_3
#print axioms adaptive_quadratic_node_2
#print axioms adaptive_quadratic_node_1
#print axioms adaptive_quadratic_node_0
end PerfectPower.MetricBoxExamples
