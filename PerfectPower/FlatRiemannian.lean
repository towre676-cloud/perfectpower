import PerfectPower.RiemannianEnergy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace PerfectPower.FlatRiemannian
open RiemannianEnergy
noncomputable section

def line (p v : ℝ × ℝ) (t : ℝ) := (p.1+t*v.1,p.2+t*v.2)

theorem line_derivative (p v : ℝ × ℝ) (t : ℝ) : HasDerivAt (line p v) v t := by
  have hx := (hasDerivAt_const t p.1).add ((hasDerivAt_id t).mul_const v.1)
  have hy := (hasDerivAt_const t p.2).add ((hasDerivAt_id t).mul_const v.2)
  simpa [line] using hx.prodMk hy

theorem line_smooth (p v : ℝ × ℝ) : ContDiff ℝ ⊤ (line p v) := by
  unfold line; fun_prop

theorem line_acceleration (p v : ℝ × ℝ) (t : ℝ) : deriv (deriv (line p v)) t = (0,0) := by
  have hd : deriv (line p v) = fun _ => v := funext (fun t => (line_derivative p v t).deriv)
  rw [hd]
  exact (hasDerivAt_const t v).deriv

/-- All globally twice differentiable flat geodesics are affine lines.
Differentiability assumptions prevent Lean's totalized derivative from masking
an irregular curve by returning zero. -/
theorem flat_geodesic_unique (γ : ℝ → ℝ × ℝ) (hγ : Differentiable ℝ γ)
    (hv : Differentiable ℝ (deriv γ)) (ha : ∀ t, deriv (deriv γ) t = 0) :
    ∀ t, γ t = line (γ 0) (deriv γ 0) t := by
  have hconst : ∀ t, deriv γ t = deriv γ 0 := fun t => is_const_of_deriv_eq_zero hv ha t 0
  let δ : ℝ → ℝ × ℝ := fun t => γ t - line (0,0) (deriv γ 0) t
  have hd : Differentiable ℝ δ := hγ.sub (fun t => (line_derivative (0,0) (deriv γ 0) t).differentiableAt)
  have hz : ∀ t, deriv δ t = 0 := by
    intro t
    exact (by simpa [δ,hconst t] using ((hγ t).hasDerivAt.sub (line_derivative (0,0) (deriv γ 0) t)).deriv)
  intro t
  have he := is_const_of_deriv_eq_zero hd hz t 0
  dsimp [δ,line] at he ⊢
  apply Prod.ext
  · have h := congrArg Prod.fst he
    change (γ t).1-(0+t*(deriv γ 0).1) = (γ 0).1-(0+0*(deriv γ 0).1) at h
    change (γ t).1 = (γ 0).1+t*(deriv γ 0).1
    linarith
  · have h := congrArg Prod.snd he
    change (γ t).2-(0+t*(deriv γ 0).2) = (γ 0).2-(0+0*(deriv γ 0).2) at h
    change (γ t).2 = (γ 0).2+t*(deriv γ 0).2
    linarith

/-- Actual integral energy of a linear segment, with positive prescribed duration. -/
def segmentEnergy (g : Metric ℝ) (v : ℝ × ℝ) (t : ℝ) :=
  ∫ _ in (0 : ℝ)..t, g.q (v.1/t,v.2/t)/2

theorem segment_energy (g : Metric ℝ) (v : ℝ × ℝ) (t : ℝ) (ht : t ≠ 0) :
    segmentEnergy g v t = g.q v/t/2 := by
  rw [segmentEnergy,intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,Metric.q]
  field_simp
  ring

def pathEnergy (g : Metric ℝ) (s : List (Step ℝ)) :=
  (s.map (fun e => segmentEnergy g e.1 e.2)).sum

theorem path_energy (g : Metric ℝ) (s : List (Step ℝ)) (ht : ∀ e ∈ s, 0 < e.2) :
    pathEnergy g s = action g s/2 := by
  induction s with
  | nil => simp [pathEnergy,action]
  | cons e es ih =>
    change segmentEnergy g e.1 e.2+pathEnergy g es = (g.q e.1/e.2+action g es)/2
    rw [segment_energy g e.1 e.2 (ne_of_gt (ht e (by simp))),
      ih (fun x hx => ht x (by simp [hx]))]
    ring

theorem analytic_energy_bound (g : Metric ℝ) (hg : g.Positive) (u : ℝ × ℝ)
    (s : List (Step ℝ)) (ht : ∀ e ∈ s, 0 < e.2)
    (hx : totalX s = totalTime s*u.1) (hy : totalY s = totalTime s*u.2) :
    totalTime s*g.q u/2 ≤ pathEnergy g s := by
  rw [path_energy g s ht]
  exact energy_lower_bound g hg u s ht hx hy

#print axioms analytic_energy_bound
#print axioms flat_geodesic_unique
#print axioms line_smooth
end
end PerfectPower.FlatRiemannian
