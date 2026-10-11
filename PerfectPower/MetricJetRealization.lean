import PerfectPower.FlatRiemannian
namespace PerfectPower.MetricJetRealization
open RiemannianEnergy
open scoped Topology
noncomputable section

def field (g dx dy : Metric ℝ) (p : ℝ × ℝ) : Metric ℝ :=
  ⟨g.a+dx.a*p.1+dy.a*p.2,g.b+dx.b*p.1+dy.b*p.2,g.c+dx.c*p.1+dy.c*p.2⟩

theorem field_at_origin (g dx dy : Metric ℝ) : field g dx dy (0,0) = g := by
  cases g; simp [field]

theorem field_smooth_a (g dx dy : Metric ℝ) : ContDiff ℝ ⊤ (fun p => (field g dx dy p).a) := by
  unfold field; fun_prop
theorem field_smooth_b (g dx dy : Metric ℝ) : ContDiff ℝ ⊤ (fun p => (field g dx dy p).b) := by
  unfold field; fun_prop
theorem field_smooth_c (g dx dy : Metric ℝ) : ContDiff ℝ ⊤ (fun p => (field g dx dy p).c) := by
  unfold field; fun_prop

theorem locally_positive (g dx dy : Metric ℝ) (hg : g.Positive) :
    ∀ᶠ p in 𝓝 ((0,0) : ℝ × ℝ), (field g dx dy p).Positive := by
  have ha : Continuous (fun p => (field g dx dy p).a) := (field_smooth_a g dx dy).continuous
  have hd : Continuous (fun p => (field g dx dy p).det) := by
    unfold Metric.det field; fun_prop
  have h1 : ∀ᶠ p in 𝓝 ((0,0) : ℝ × ℝ), 0 < (field g dx dy p).a :=
    ha.continuousAt.eventually (eventually_gt_nhds (by simpa only [field_at_origin] using hg.1))
  have h2 : ∀ᶠ p in 𝓝 ((0,0) : ℝ × ℝ), 0 < (field g dx dy p).det :=
    hd.continuousAt.eventually (eventually_gt_nhds (by simpa only [field_at_origin] using hg.2))
  exact h1.and h2

theorem x_derivatives (g dx dy : Metric ℝ) :
    HasDerivAt (fun x : ℝ => (field g dx dy (x,0)).a) dx.a 0 ∧
    HasDerivAt (fun x : ℝ => (field g dx dy (x,0)).b) dx.b 0 ∧
    HasDerivAt (fun x : ℝ => (field g dx dy (x,0)).c) dx.c 0 := by
  have h (a b c : ℝ) : HasDerivAt (fun x : ℝ => a+b*x+c*0) b 0 := by
    simpa [mul_comm] using (hasDerivAt_const 0 a).add ((hasDerivAt_id 0).mul_const b)
  exact ⟨h _ _ _,h _ _ _,h _ _ _⟩

theorem y_derivatives (g dx dy : Metric ℝ) :
    HasDerivAt (fun y : ℝ => (field g dx dy (0,y)).a) dy.a 0 ∧
    HasDerivAt (fun y : ℝ => (field g dx dy (0,y)).b) dy.b 0 ∧
    HasDerivAt (fun y : ℝ => (field g dx dy (0,y)).c) dy.c 0 := by
  have h (a b c : ℝ) : HasDerivAt (fun y : ℝ => a+b*0+c*y) c 0 := by
    simpa [mul_comm] using (hasDerivAt_const 0 a).add ((hasDerivAt_id 0).mul_const c)
  exact ⟨h _ _ _,h _ _ _,h _ _ _⟩

/-- Every admitted symmetric first jet has a smooth, locally positive metric
realization. This is a local existence statement, not uniqueness or a globally
positive affine extension. -/
theorem local_jet_realization (g dx dy : Metric ℝ) (hg : g.Positive) :
    field g dx dy (0,0) = g ∧
    (∀ᶠ p in 𝓝 ((0,0) : ℝ × ℝ), (field g dx dy p).Positive) ∧
    ContDiff ℝ ⊤ (fun p => (field g dx dy p).a) ∧
    ContDiff ℝ ⊤ (fun p => (field g dx dy p).b) ∧
    ContDiff ℝ ⊤ (fun p => (field g dx dy p).c) :=
  ⟨field_at_origin g dx dy,locally_positive g dx dy hg,
    field_smooth_a g dx dy,field_smooth_b g dx dy,field_smooth_c g dx dy⟩

#print axioms local_jet_realization
#print axioms x_derivatives
#print axioms y_derivatives
end
end PerfectPower.MetricJetRealization
