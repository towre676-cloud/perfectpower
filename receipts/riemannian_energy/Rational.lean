import PerfectPower.RiemannianEnergy
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
open PerfectPower.RiemannianEnergy
namespace Rational
def g : Metric ℚ := ⟨((1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)),((1000001 : ℚ)/(1000000 : ℚ))⟩
def vertices : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),(((1 : ℚ)/(3 : ℚ)),((-2 : ℚ)/(5 : ℚ)))]
def durations : List ℚ := [((7 : ℚ)/(11 : ℚ))]
def steps : List (Step ℚ) := ((vertices.zip vertices.tail).zip durations).map
  (fun e => ((e.1.2.1-e.1.1.1,e.1.2.2-e.1.1.2),e.2))
def velocity : ℚ × ℚ := (((11 : ℚ)/(21 : ℚ)),((-22 : ℚ)/(35 : ℚ)))
theorem source_shape : vertices.length = durations.length+1 := by decide +kernel
theorem source_positive : g.Positive := by decide +kernel
theorem source_times : ∀ e ∈ steps, 0 < e.2 := by decide +kernel
theorem source_duration : totalTime steps = ((7 : ℚ)/(11 : ℚ)) := by decide +kernel
theorem source_total_positive : 0 < totalTime steps := by decide +kernel
theorem source_endpoint_x : totalX steps = vertices.getLast!.1-vertices.head!.1 := by decide +kernel
theorem source_endpoint_y : totalY steps = vertices.getLast!.2-vertices.head!.2 := by decide +kernel
theorem source_dx : totalX steps = totalTime steps*velocity.1 := by decide +kernel
theorem source_dy : totalY steps = totalTime steps*velocity.2 := by decide +kernel
theorem source_energy : action g steps/2 = ((2750099 : ℚ)/(787500000 : ℚ)) := by decide +kernel
theorem source_gap : gap g velocity steps/2 = ((0 : ℚ)/(1 : ℚ)) := by decide +kernel
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
theorem source_attained : action g steps/2 = totalTime steps*g.q velocity/2 := by decide +kernel
theorem source_minimal (s : List (Step ℚ))
    (ht : ∀ e ∈ s, 0 < e.2) (hT : totalTime s = totalTime steps)
    (hx : totalX s = totalX steps) (hy : totalY s = totalY steps) :
    action g steps/2 ≤ action g s/2 := by
  rw [source_attained]; exact all_timed_paths s ht hT hx hy
#print axioms source_minimal
#print axioms all_timed_paths
#print axioms source_excess
end Rational
