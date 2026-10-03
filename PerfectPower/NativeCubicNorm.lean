import PerfectPower.NativeCubic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-! Determinant norm and oriented index form for the native binary-cubic ring. -/
namespace PerfectPower.NativeCubic
open Matrix

def basis (j : Fin 3) : Triple :=
  if j=0 then (1,0,0) else if j=1 then (0,1,0) else (0,0,1)
def Mx (a b c d : ℤ) (x : Triple) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j =>
    let v := mul a b c d x (basis j)
    if i=0 then v.1 else if i=1 then v.2.1 else v.2.2
def norm (a b c d : ℤ) (x : Triple) : ℤ := (Mx a b c d x).det

theorem Mx_mul (a b c d : ℤ) (x y : Triple) :
    Mx a b c d (mul a b c d x y) = Mx a b c d x * Mx a b c d y := by
  obtain ⟨x0,x1,x2⟩ := x
  obtain ⟨y0,y1,y2⟩ := y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mx,basis,mul,Matrix.mul_apply,Fin.sum_univ_three] <;> ring

theorem norm_mul (a b c d : ℤ) (x y : Triple) :
    norm a b c d (mul a b c d x y) = norm a b c d x * norm a b c d y := by
  simp only [norm,Mx_mul,Matrix.det_mul]

theorem norm_scalar (a b c d t : ℤ) : norm a b c d (t,0,0) = t^3 := by
  unfold norm
  rw [Matrix.det_fin_three]
  simp [Mx,basis,mul]
  ring

theorem index_form (a b c d u v : ℤ) :
    ( !![1,0,(mul a b c d (0,u,v) (0,u,v)).1;
         0,u,(mul a b c d (0,u,v) (0,u,v)).2.1;
         0,v,(mul a b c d (0,u,v) (0,u,v)).2.2] : Matrix (Fin 3) (Fin 3) ℤ).det =
      -(a*u^3+b*u^2*v+c*u*v^2+d*v^3) := by
  rw [Matrix.det_fin_three]
  simp [mul]
  ring

theorem norm_encoded (a b c d u v : ℤ) :
    norm a b c d (a*u,v,0) = a^2*(a*u^3+b*u^2*v+c*u*v^2+d*v^3) := by
  unfold norm
  rw [Matrix.det_fin_three]
  simp [Mx,basis,mul]
  ring
end PerfectPower.NativeCubic
