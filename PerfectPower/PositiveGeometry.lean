import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Algebraic targets of the positive-geometry handoff. Analytic interpretations
and packing admissibility are deliberately separate from these identities. -/
noncomputable section

namespace PerfectPower.PositiveGeometry

def descartes (a b c d : ℤ) : Prop := (a+b+c+d)^2 = 2*(a^2+b^2+c^2+d^2)
def reflect (a b c d : ℤ) : ℤ := 2*(b+c+d)-a

theorem descartes_reflection_involution (a b c d : ℤ) :
    reflect (reflect a b c d) b c d = a := by unfold reflect; ring

theorem descartes_reflection_preserves (a b c d : ℤ) (h : descartes a b c d) :
    descartes (reflect a b c d) b c d := by
  unfold descartes reflect at *
  linear_combination h

def curvature (u v s : ℤ) (n : ℕ) : ℤ :=
  u + (v-u-s)*(n:ℤ) + s*(n:ℤ)^2

def orbit (u v s : ℤ) : ℕ → ℤ
  | 0 => u
  | 1 => v
  | n+2 => 2*orbit u v s (n+1)-orbit u v s n+2*s

theorem curvature_recurrence (u v s : ℤ) (n : ℕ) :
    curvature u v s (n+2) = 2*curvature u v s (n+1)-curvature u v s n+2*s := by
  unfold curvature
  push_cast
  ring

theorem descartes_quadratic_orbit (u v s : ℤ) (n : ℕ) :
    orbit u v s n = curvature u v s n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [orbit, curvature]
  | one => simp [orbit, curvature]; ring
  | more n hn hn1 => rw [orbit, hn, hn1, curvature_recurrence]

theorem seed_curvature (n : ℕ) : orbit 2 3 1 n = (n:ℤ)^2+2 := by
  rw [descartes_quadratic_orbit]
  simp [curvature]
  ring

example : descartes (-1) 2 2 3 := by norm_num [descartes]
example : orbit 2 3 1 5 = 3^3 := by rw [seed_curvature]; norm_num

def intervalForm (a b x : ℚ) : ℚ := (b-a)/((x-a)*(b-x))

theorem interval_canonical_additivity (a b c x : ℚ)
    (ha : x-a ≠ 0) (hb : b-x ≠ 0) (hc : c-x ≠ 0) :
    intervalForm a b x = intervalForm a c x + intervalForm c b x := by
  unfold intervalForm
  have hxc : x-c ≠ 0 := by intro h; apply hc; linarith
  field_simp
  ring

/-- Fix the wedge order `du ∧ dt`, with Jacobian determinant t. -/
theorem pentagon_collision_residue (u t : ℚ)
    (hu : u ≠ 0) (hu1 : 1-u ≠ 0) (ht : t ≠ 0) (ht1 : 1-t ≠ 0) :
    t / ((t*u)*(t-t*u)*(1-t)) = 1/(u*(1-u)*t*(1-t)) := by
  have hgap : t-t*u ≠ 0 := by
    have he : t-t*u=t*(1-u) := by ring
    rw [he]; exact mul_ne_zero ht hu1
  field_simp
  ring

def thetaMatrix (a b c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a+b+c, -a+b-c*Complex.I; -a+b+c*Complex.I, a+b+c]

theorem theta_determinant (a b c : ℂ) :
    (thetaMatrix a b c).det = 4*a*b+2*a*c+2*b*c := by
  rw [Matrix.det_fin_two]
  simp only [thetaMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const]
  ring_nf
  simp [Complex.I_sq]

def thetaQ (a b c : ℚ) : ℚ := 4*a*b+2*a*c+2*b*c

theorem theta_canonical_jacobian (a b c : ℚ) :
    ((-2*b*c*(4*b+2*c))*(-2*a*c*(4*a+2*c)) -
      (2*c*thetaQ a b c-2*b*c*(4*a+2*c))*(2*c*thetaQ a b c-2*a*c*(4*b+2*c))) =
      16*a*b*c^2*thetaQ a b c := by unfold thetaQ; ring

theorem theta_canonical_pullback (a b c : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : thetaQ a b c ≠ 0) :
    (16*a*b*c^2*thetaQ a b c / (thetaQ a b c)^4) /
      ((2*b*c/thetaQ a b c)*(2*a*c/thetaQ a b c)*(4*a*b/thetaQ a b c)) =
      1/(a*b) := by field_simp; ring

/-- Gauss–Bonnet for a supplied triangulated quotient metric. -/
theorem descartes_polyhedral_defect (V E F corners : ℚ)
    (hc : corners = 3*F) (he : 3*F = 2*E) :
    2*V-corners/3 = 2*(V-E+F) := by linarith

end PerfectPower.PositiveGeometry
