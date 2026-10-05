import PerfectPower.BernsteinBoxes
import PerfectPower.RationalVoronoiPacket
import PerfectPower.UniformHyperellipticMetric
#print axioms PerfectPower.BernsteinBoxes.basis_nonnegative
#print axioms PerfectPower.BernsteinBoxes.basis_positive_somewhere
#print axioms PerfectPower.BernsteinBoxes.tensor_positive
#print axioms PerfectPower.BernsteinBoxes.rectangle_positive
#print axioms PerfectPower.BernsteinBoxes.joint_exclusion
#print axioms PerfectPower.BernsteinBoxes.density_comparison
#print axioms PerfectPower.BernsteinBoxes.branch_equation
#print axioms PerfectPower.BernsteinBoxes.reciprocal_odd
#print axioms PerfectPower.BernsteinBoxes.tangent_comparison
#print axioms PerfectPower.BernsteinBoxes.sqrt_scaled
#print axioms PerfectPower.BernsteinBoxes.speed_comparison
#print axioms PerfectPower.BernsteinBoxes.path_length_comparison
#print axioms PerfectPower.BernsteinBoxes.reciprocal_family
#print axioms PerfectPower.BernsteinBoxes.branch_family
#print axioms PerfectPower.BernsteinBoxes.basis_positive
#print axioms PerfectPower.BernsteinBoxes.tensor_positive_support
#print axioms PerfectPower.BernsteinBoxes.tensor_zero_iff
#print axioms PerfectPower.RationalVoronoiPacket.accepted_fields
#print axioms PerfectPower.RationalVoronoiPacket.accepted_leaves
#print axioms PerfectPower.RationalVoronoiPacket.accepted_coverage
#print axioms PerfectPower.RationalVoronoiPacket.accepted_mesh
#print axioms PerfectPower.RationalVoronoiPacket.checked_gradient
#print axioms PerfectPower.UniformHyperellipticMetric.small_power
#print axioms PerfectPower.UniformHyperellipticMetric.disk_bounds
#print axioms PerfectPower.UniformHyperellipticMetric.uniform_small_disk

namespace PerfectPower.MetricBoxExamples

theorem square_cube_same_real (x y : ℝ) :
    y^2=x^3 ∧ y=x ↔ (x=0 ∧ y=0) ∨ (x=1 ∧ y=1) := by
  constructor
  · rintro ⟨hpow,hline⟩
    rw [hline] at hpow
    have hz : x^2*(1-x)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with h0 | h1
    · have hx : x=0 := (sq_eq_zero_iff).mp h0
      exact Or.inl ⟨hx,hline.trans hx⟩
    · have hx : x=1 := by linarith
      exact Or.inr ⟨hx,hline.trans hx⟩
  · rintro (⟨hx,hy⟩ | ⟨hx,hy⟩) <;> simp [hx,hy]

theorem square_cube_same_integer (x y : ℤ) :
    y^2=x^3 ∧ y=x ↔ (x=0 ∧ y=0) ∨ (x=1 ∧ y=1) := by
  exact_mod_cast square_cube_same_real (x:ℝ) (y:ℝ)

theorem huge_genus (t : ℂ) (h : ‖t‖^2 ≤ 1/8) :
    (99/100:ℝ)^2*4 < UniformHyperellipticMetric.density (10^100) t ∧
      UniformHyperellipticMetric.density (10^100) t < (103/100:ℝ)^2*4 := by
  exact UniformHyperellipticMetric.uniform_small_disk _ (by norm_num) t h

#print axioms square_cube_same_real
#print axioms square_cube_same_integer
#print axioms huge_genus
end PerfectPower.MetricBoxExamples
