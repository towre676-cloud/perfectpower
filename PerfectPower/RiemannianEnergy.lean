import Mathlib.Tactic

/-! Exact constant-metric energy and coordinate first-jet algebra.
The ordered-field theorems specialize to both ℚ and ℝ. No smooth-manifold,
ODE, integral, obstacle shortest-path or physical dynamics claim is made. -/
namespace PerfectPower.RiemannianEnergy
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure Metric (K : Type*) where
  a : K
  b : K
  c : K
  deriving DecidableEq

def Metric.det (g : Metric K) := g.a * g.c - g.b ^ 2
def Metric.Positive (g : Metric K) : Prop := 0 < g.a ∧ 0 < g.det
instance (g : Metric K) : Decidable g.Positive := by
  unfold Metric.Positive
  infer_instance

def Metric.q (g : Metric K) (v : K × K) :=
  g.a * v.1 ^ 2 + 2 * g.b * v.1 * v.2 + g.c * v.2 ^ 2

def Metric.bilinear (g : Metric K) (u v : K × K) :=
  g.a*u.1*v.1+g.b*(u.1*v.2+u.2*v.1)+g.c*u.2*v.2

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem square_decomposition (g : Metric K) (v : K × K) :
    g.a * g.q v = (g.a * v.1 + g.b * v.2)^2 + g.det * v.2^2 := by
  unfold Metric.q Metric.det
  ring

theorem q_nonneg (g : Metric K) (h : g.Positive) (v : K × K) : 0 ≤ g.q v := by
  have hs := square_decomposition g v
  have h1 := sq_nonneg (g.a * v.1 + g.b * v.2)
  have h2 := mul_nonneg (le_of_lt h.2) (sq_nonneg v.2)
  nlinarith [h.1]

theorem q_zero_iff (g : Metric K) (h : g.Positive) (v : K × K) :
    g.q v = 0 ↔ v = (0,0) := by
  constructor
  · intro hz
    have hs := square_decomposition g v
    have h1 := sq_nonneg (g.a * v.1 + g.b * v.2)
    have hy : v.2 = 0 := by
      by_contra hn
      have hp := mul_pos h.2 (sq_pos_of_ne_zero hn)
      rw [hz] at hs
      simp only [mul_zero] at hs
      linarith only [hs,h1,hp]
    have hx : v.1 = 0 := by
      rw [hy] at hs
      simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hs
      have : g.a * v.1 = 0 := by
        rw [hz] at hs
        nlinarith
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt h.1)
    exact Prod.ext hx hy
  · rintro rfl
    simp [Metric.q]

abbrev Step (K : Type*) := (K × K) × K

def totalX (s : List (Step K)) : K := (s.map (fun e => e.1.1)).sum
def totalY (s : List (Step K)) : K := (s.map (fun e => e.1.2)).sum
def totalTime (s : List (Step K)) : K := (s.map Prod.snd).sum
def action (g : Metric K) (s : List (Step K)) : K :=
  (s.map (fun e => g.q e.1 / e.2)).sum
def gap (g : Metric K) (u : K × K) (s : List (Step K)) : K :=
  (s.map (fun e => g.q (e.1.1-e.2*u.1,e.1.2-e.2*u.2) / e.2)).sum

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem single_gap (g : Metric K) (u v : K × K) (t : K) (ht : t ≠ 0) :
    g.q (v.1-t*u.1,v.2-t*u.2)/t = g.q v/t -
      2*(g.a*v.1*u.1+g.b*(v.1*u.2+v.2*u.1)+g.c*v.2*u.2)+t*g.q u := by
  unfold Metric.q
  field_simp
  ring

theorem variance_identity (g : Metric K) (u : K × K) (s : List (Step K))
    (ht : ∀ e ∈ s, e.2 ≠ 0) :
    gap g u s = action g s -
      2*(g.a*totalX s*u.1+g.b*(totalX s*u.2+totalY s*u.1)+g.c*totalY s*u.2)+
      totalTime s*g.q u := by
  induction s with
  | nil => simp [gap,action,totalX,totalY,totalTime]
  | cons e s ih =>
    have he := single_gap g u e.1 e.2 (ht e (by simp))
    have hi := ih (fun x hx => ht x (by simp [hx]))
    simp only [gap,action,totalX,totalY,totalTime,List.map_cons,List.sum_cons] at *
    rw [he, hi]
    ring

theorem gap_nonneg (g : Metric K) (hg : g.Positive) (u : K × K)
    (s : List (Step K)) (ht : ∀ e ∈ s, 0 < e.2) : 0 ≤ gap g u s := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact div_nonneg (q_nonneg g hg _) (le_of_lt (ht e he))

/-- Exact sharp excess over constant-velocity action; all finite timed walks. -/
theorem energy_excess (g : Metric K) (u : K × K) (s : List (Step K))
    (ht : ∀ e ∈ s, 0 < e.2)
    (hx : totalX s = totalTime s*u.1) (hy : totalY s = totalTime s*u.2) :
    action g s = totalTime s*g.q u + gap g u s := by
  have hv := variance_identity g u s (fun e he => ne_of_gt (ht e he))
  rw [hx,hy] at hv
  unfold Metric.q at *
  linear_combination -hv

/-- Equality is rigid: every displacement equals duration times mean velocity. -/
theorem gap_zero_iff (g : Metric K) (hg : g.Positive) (u : K × K)
    (s : List (Step K)) (ht : ∀ e ∈ s, 0 < e.2) :
    gap g u s = 0 ↔ ∀ e ∈ s, e.1.1 = e.2*u.1 ∧ e.1.2 = e.2*u.2 := by
  induction s with
  | nil => simp [gap]
  | cons e s ih =>
    have he := ht e (by simp)
    have hs : ∀ x ∈ s, 0 < x.2 := fun x hx => ht x (by simp [hx])
    have hn := q_nonneg g hg (e.1.1-e.2*u.1,e.1.2-e.2*u.2)
    have hn' := div_nonneg hn (le_of_lt he)
    have htail := gap_nonneg g hg u s hs
    have eqstep : g.q (e.1.1-e.2*u.1,e.1.2-e.2*u.2)/e.2 = 0 ↔
        e.1.1 = e.2*u.1 ∧ e.1.2 = e.2*u.2 := by
      rw [div_eq_zero_iff, q_zero_iff g hg]
      simp only [Prod.mk.injEq, sub_eq_zero, ne_of_gt he, or_false]
    simp only [gap, List.map_cons, List.sum_cons] at *
    constructor
    · intro hz
      have hz1 : g.q (e.1.1-e.2*u.1,e.1.2-e.2*u.2)/e.2 = 0 := by linarith
      have hz2 : (s.map (fun e => g.q (e.1.1-e.2*u.1,e.1.2-e.2*u.2)/e.2)).sum = 0 := by linarith
      have hfirst := eqstep.mp hz1
      have hrest := (ih hs).mp hz2
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfirst
      · exact hrest x hx
    · intro hall
      have hz1 := eqstep.mpr (hall e (by simp))
      have hz2 := (ih hs).mpr (fun x hx => hall x (by simp [hx]))
      rw [hz1,hz2]
      simp

/-- The conventional energy has a factor 1/2. -/
theorem energy_lower_bound (g : Metric K) (hg : g.Positive) (u : K × K)
    (s : List (Step K)) (ht : ∀ e ∈ s, 0 < e.2)
    (hx : totalX s = totalTime s*u.1) (hy : totalY s = totalTime s*u.2) :
    totalTime s*g.q u/2 ≤ action g s/2 := by
  have := energy_excess g u s ht hx hy
  have := gap_nonneg g hg u s ht
  linarith

structure LinearMap2 (K : Type*) where
  p : K
  q : K
  r : K
  s : K

def LinearMap2.apply (a : LinearMap2 K) (v : K × K) :=
  (a.p*v.1+a.q*v.2,a.r*v.1+a.s*v.2)
def pullback (h : Metric K) (a : LinearMap2 K) : Metric K :=
  ⟨h.a*a.p^2+2*h.b*a.p*a.r+h.c*a.r^2,
   h.a*a.p*a.q+h.b*(a.p*a.s+a.q*a.r)+h.c*a.r*a.s,
   h.a*a.q^2+2*h.b*a.q*a.s+h.c*a.s^2⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pullback_quadratic (h : Metric K) (a : LinearMap2 K) (v : K × K) :
    (pullback h a).q v = h.q (a.apply v) := by
  simp only [pullback,Metric.q,LinearMap2.apply]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pullback_bilinear (h : Metric K) (a : LinearMap2 K) (u v : K × K) :
    (pullback h a).bilinear u v = h.bilinear (a.apply u) (a.apply v) := by
  simp only [pullback,Metric.bilinear,LinearMap2.apply]
  ring

def LinearMap2.inverse (a : LinearMap2 K) : LinearMap2 K :=
  ⟨a.s/(a.p*a.s-a.q*a.r),-a.q/(a.p*a.s-a.q*a.r),
   -a.r/(a.p*a.s-a.q*a.r),a.p/(a.p*a.s-a.q*a.r)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem inverse_apply (a : LinearMap2 K) (ha : a.p*a.s-a.q*a.r ≠ 0) (v : K × K) :
    a.inverse.apply (a.apply v) = v := by
  apply Prod.ext <;> simp only [LinearMap2.inverse,LinearMap2.apply]
  · field_simp [ha]; ring
  · field_simp [ha]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem apply_inverse (a : LinearMap2 K) (ha : a.p*a.s-a.q*a.r ≠ 0) (v : K × K) :
    a.apply (a.inverse.apply v) = v := by
  apply Prod.ext <;> simp only [LinearMap2.inverse,LinearMap2.apply]
  · field_simp [ha]; ring
  · field_simp [ha]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem linear_bijective (a : LinearMap2 K) (ha : a.p*a.s-a.q*a.r ≠ 0) :
    Function.Bijective a.apply := by
  constructor
  · intro v w hh
    have h := congrArg a.inverse.apply hh
    simpa only [inverse_apply a ha] using h
  · intro v
    exact ⟨a.inverse.apply v,apply_inverse a ha v⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pullback_determinant (h : Metric K) (a : LinearMap2 K) :
    (pullback h a).det = h.det*(a.p*a.s-a.q*a.r)^2 := by
  simp only [pullback,Metric.det]
  ring

theorem pullback_positive (h : Metric K) (hh : h.Positive) (a : LinearMap2 K)
    (ha : a.p*a.s-a.q*a.r ≠ 0) : (pullback h a).Positive := by
  have hv : (a.p,a.r) ≠ (0,0) := by
    intro hz
    have hp := congrArg Prod.fst hz
    have hr := congrArg Prod.snd hz
    simp only [Prod.fst,Prod.snd] at hp hr
    simp [hp,hr] at ha
  have hn := q_nonneg h hh (a.p,a.r)
  have hne : h.q (a.p,a.r) ≠ 0 := fun hz => hv ((q_zero_iff h hh _).mp hz)
  constructor
  · change 0 < h.q (a.p,a.r)
    exact lt_of_le_of_ne hn (Ne.symm hne)
  · rw [pullback_determinant]
    exact mul_pos hh.2 (sq_pos_of_ne_zero ha)

def mapSteps (a : LinearMap2 K) (s : List (Step K)) :=
  s.map (fun e => (a.apply e.1,e.2))
omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem action_transport (h : Metric K) (a : LinearMap2 K) (s : List (Step K)) :
    action (pullback h a) s = action h (mapSteps a s) := by
  simp only [action,mapSteps,List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  exact congrArg (fun x => x/e.2) (pullback_quadratic h a e.1)

/-- Lowered coordinate coefficients; D i j k denotes ∂ᵢ gⱼₖ. -/
def koszul {I : Type*} (D : I → I → I → K) (i j k : I) :=
  (D i j k + D j i k - D k i j)/2

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem koszul_torsion {I : Type*} (D : I → I → I → K)
    (hs : ∀ i j k, D i j k = D i k j) (i j k : I) :
    koszul D i j k = koszul D j i k := by
  unfold koszul
  rw [hs k i j]
  ring

theorem koszul_compatible {I : Type*} (D : I → I → I → K)
    (hs : ∀ i j k, D i j k = D i k j) (i j k : I) :
    koszul D i j k + koszul D i k j = D i j k := by
  unfold koszul
  rw [hs i k j]
  ring

/-- Generic uniqueness of torsion-free metric-compatible lowered first jets. -/
theorem koszul_unique {I : Type*} (D A : I → I → I → K)
    (torsion : ∀ i j k, A i j k = A j i k)
    (compat : ∀ i j k, A i j k + A i k j = D i j k) (i j k : I) :
    A i j k = koszul D i j k := by
  have h1 := compat i j k
  have h2 := compat j i k
  have h3 := compat k i j
  rw [← torsion i j k] at h2
  rw [← torsion i k j,← torsion j k i] at h3
  unfold koszul
  linarith

#print axioms gap_zero_iff
#print axioms pullback_positive
#print axioms energy_lower_bound
#print axioms linear_bijective
#print axioms pullback_bilinear
#print axioms action_transport
#print axioms q_zero_iff
#print axioms koszul_unique
end PerfectPower.RiemannianEnergy
