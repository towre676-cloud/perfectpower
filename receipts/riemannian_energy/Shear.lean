import PerfectPower.RiemannianEnergy
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
open PerfectPower.RiemannianEnergy
namespace Shear
def g : Metric ℚ := ⟨((3 : ℚ)/(1 : ℚ)),((7 : ℚ)/(1 : ℚ)),((18 : ℚ)/(1 : ℚ))⟩
def vertices : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),(((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))),(((3 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ)))]
def durations : List ℚ := [((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))]
def steps : List (Step ℚ) := ((vertices.zip vertices.tail).zip durations).map
  (fun e => ((e.1.2.1-e.1.1.1,e.1.2.2-e.1.1.2),e.2))
def velocity : ℚ × ℚ := (((1 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(3 : ℚ)))
theorem source_shape : vertices.length = durations.length+1 := by decide +kernel
theorem source_positive : g.Positive := by decide +kernel
theorem source_times : ∀ e ∈ steps, 0 < e.2 := by decide +kernel
theorem source_duration : totalTime steps = ((3 : ℚ)/(1 : ℚ)) := by decide +kernel
theorem source_total_positive : 0 < totalTime steps := by decide +kernel
theorem source_endpoint_x : totalX steps = vertices.getLast!.1-vertices.head!.1 := by decide +kernel
theorem source_endpoint_y : totalY steps = vertices.getLast!.2-vertices.head!.2 := by decide +kernel
theorem source_dx : totalX steps = totalTime steps*velocity.1 := by decide +kernel
theorem source_dy : totalY steps = totalTime steps*velocity.2 := by decide +kernel
theorem source_energy : action g steps/2 = ((74 : ℚ)/(1 : ℚ)) := by decide +kernel
theorem source_gap : gap g velocity steps/2 = ((147 : ℚ)/(2 : ℚ)) := by decide +kernel
theorem source_excess : action g steps = totalTime steps*g.q velocity+gap g velocity steps :=
  energy_excess g velocity steps source_times source_dx source_dy
theorem all_timed_paths (s : List (Step ℚ))
    (ht : ∀ e ∈ s, 0 < e.2) (hT : totalTime s = totalTime steps)
    (hx : totalX s = totalX steps) (hy : totalY s = totalY steps) :
    totalTime steps*g.q velocity/2 ≤ action g s/2 := by
  have dx : totalX s = totalTime s*velocity.1 := by rw [hx,hT,source_dx]
  have dy : totalY s = totalTime s*velocity.2 := by rw [hy,hT,source_dy]
  have h := energy_lower_bound g source_positive velocity s ht dx dy
  simpa only [hT] using h
def target : Metric ℚ := ⟨((3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))⟩
theorem target_positive : target.Positive := by decide +kernel
def linear : LinearMap2 ℚ := ⟨((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))⟩
def translation : ℚ × ℚ := (((3 : ℚ)/(7 : ℚ)),((11 : ℚ)/(1 : ℚ)))
def imageVertices := vertices.map (fun v =>
  ((linear.apply v).1+translation.1,(linear.apply v).2+translation.2))
def imageSteps : List (Step ℚ) := ((imageVertices.zip imageVertices.tail).zip durations).map
  (fun e => ((e.1.2.1-e.1.1.1,e.1.2.2-e.1.1.2),e.2))
theorem source_pullback : g = pullback target linear := by decide +kernel
theorem source_invertible : linear.p*linear.s-linear.q*linear.r ≠ 0 := by decide +kernel
theorem source_bilinear (u v : ℚ × ℚ) : g.bilinear u v = target.bilinear (linear.apply u) (linear.apply v) := by
  rw [source_pullback]; exact pullback_bilinear target linear u v
theorem source_bijective : Function.Bijective linear.apply := linear_bijective linear source_invertible
theorem source_image : imageSteps = mapSteps linear steps := by decide +kernel
theorem source_transport : action g steps = action target imageSteps := by
  rw [source_pullback,source_image]
  exact action_transport target linear steps
#print axioms source_transport
#print axioms source_bilinear
#print axioms source_bijective
#print axioms all_timed_paths
#print axioms source_excess
end Shear
