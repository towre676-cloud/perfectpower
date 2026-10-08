import Mathlib.Tactic

/-! Algebraic reduction-of-coupling identities for the declared one-loop model.
These are polynomial theorems, not a formalization of Feynman diagrams or CKM.
-/
namespace PerfectPower.FlavorRG
open scoped BigOperators

/-- Every quadratic beta tensor preserves a certified ray under rescaling. -/
theorem quadratic_ray {ι : Type*} [Fintype ι] (B : ι → ι → ι → ℝ)
    (r : ι → ℝ) (hr : ∀ k, ∑ i, ∑ j, B k i j*r i*r j=r k)
    (t : ℝ) (k : ι) :
    (∑ i, ∑ j, B k i j*(t*r i)*(t*r j)) = t^2*r k := by
  calc
    _ = t^2*(∑ i, ∑ j, B k i j*r i*r j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = t^2*r k := by rw [hr]

/-- A nonzero one-loop hypercharge coupling cannot be a fixed point. -/
theorem hypercharge_beta_positive (g : ℝ) (hg : 0<g) : 0<(27/2:ℝ)*g^3 := by positivity

theorem hypercharge_fixed_point (g : ℝ) (h : (27/2:ℝ)*g^3=0) : g=0 := by
  have hp : g^3=0 := by nlinarith
  exact pow_eq_zero hp

/-- Positive non-Abelian and Abelian couplings cannot share this one-loop ray. -/
theorem no_common_gauge_ray (gs gy : ℝ) (hs : 0<gs) (hy : 0<gy) :
    (-3:ℝ)*gs^2 ≠ (27/2:ℝ)*gy^2 := by
  have hss : 0<gs^2 := sq_pos_of_pos hs
  have hys : 0<gy^2 := sq_pos_of_pos hy
  nlinarith

/-- In the QCD/adjoint-Yukawa restriction, reduction fixes y²/g₃²=5/8. -/
theorem adjoint_yukawa_ratio (r : ℝ) : (8*r-8 = -3) ↔ r=5/8 := by constructor <;> intro h <;> linarith

/-- Two independent non-Abelian anchors determine the unified value and scale. -/
theorem unified_solution_unique (x2 x3 b2 b3 U L V M : ℝ) (hb : b2≠b3)
    (h2 : x2=U+b2*L) (h3 : x3=U+b3*L)
    (k2 : x2=V+b2*M) (k3 : x3=V+b3*M) : U=V ∧ L=M := by
  have hz : (b2-b3)*(L-M)=0 := by nlinarith
  have he : L=M := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hb))
  constructor
  · rw [he] at h2
    linarith [h2,k2]
  · exact he

/-- The declared minimal action cannot unify SU2 and SU3 above ordered anchors. -/
theorem minimal_unification_below (x2 x3 U L : ℝ) (hx : x3<x2)
    (h2 : x2=U+(-19/6:ℝ)*L) (h3 : x3=U+(-3:ℝ)*L) : L<0 := by linarith

/-- The radial pure-scalar beta coefficient is a positive quadratic form. -/
theorem radial_completed_square (a b c d f : ℝ) :
    128*a^2+32*a*b+(192/25)*b^2+16*c^2+(5/18)*d^2+(27/20)*f^2 =
    128*(a+b/8)^2+(142/25)*b^2+16*c^2+(5/18)*d^2+(27/20)*f^2 := by ring

/-- SU(3) radial positivity already forbids a nonzero pure-scalar fixed point. -/
theorem su3_radial_fixed_zero (a c d h : ℝ)
    (hz : 128*a^2+16*c^2+(5/18)*d^2+(27/20)*h^2=0) :
    a=0 ∧ c=0 ∧ d=0 ∧ h=0 := by
  have ha := sq_nonneg a
  have hc := sq_nonneg c
  have hd := sq_nonneg d
  have hh := sq_nonneg h
  have za : a^2=0 := by nlinarith
  have zc : c^2=0 := by nlinarith
  have zd : d^2=0 := by nlinarith
  have zh : h^2=0 := by nlinarith
  exact ⟨pow_eq_zero za,pow_eq_zero zc,pow_eq_zero zd,pow_eq_zero zh⟩

/-- Literal four-operator beta restriction, independently replayed from the tensor. -/
def ScalarRay (a c d h : ℝ) : Prop :=
  128*a^2+16*c^2+(5/18)*d^2+(27/20)*h^2=a ∧
  160*a*c+16*c^2+(25/18)*d^2+(27/4)*h^2=c ∧
  32*a*d+32*c*d+(6/5)*d^2+(108/25)*d*h+(4536/125)*h^2=d ∧
  32*a*h+32*c*h+(4/9)*d^2+(224/15)*d*h+(436/25)*h^2=h

theorem radial_ray : ScalarRay (1/128) 0 0 0 := by norm_num [ScalarRay]
theorem difference_ray : ScalarRay (1/144) (-1/144) 0 0 := by norm_num [ScalarRay]
theorem joint_radial_ray : ScalarRay (1/192) (1/96) 0 0 := by norm_num [ScalarRay]
theorem trace_ray_one : ScalarRay (1/256) (5/512) (3/160) (1/64) := by norm_num [ScalarRay]
theorem trace_ray_two : ScalarRay (1/576) (7/1152) (1/40) (1/48) := by norm_num [ScalarRay]

/-- The nonradial fixed rays cancel the independent A²B² alignment force. -/
theorem trace_force_cancels :
    (3/160:ℝ)-(6/5)*(1/64)=0 ∧ (1/40:ℝ)-(6/5)*(1/48)=0 := by norm_num

/-- Squared spectral moments determine each mixing probability with distinct spectra. -/
theorem two_by_two_moment_inverse (a1 a2 b1 b2 x11 x12 x21 x22 : ℝ) :
    (a1-a2)*(b1-b2)*x11 =
      (a1*b1*x11+a1*b2*x12+a2*b1*x21+a2*b2*x22)
      -a2*(b1*x11+b2*x12+b1*x21+b2*x22)
      -b2*(a1*x11+a1*x12+a2*x21+a2*x22)
      +a2*b2*(x11+x12+x21+x22) := by ring

end PerfectPower.FlavorRG
