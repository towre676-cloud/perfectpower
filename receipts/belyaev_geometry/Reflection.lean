import PerfectPower.GeometryFoundations
namespace PerfectPower.CheckedGeometry.P148460bc42225a9ad2612c8785ee1decb139ee7055fe825986202d652f2ecfc5
open PerfectPower.GeometryFoundations
theorem matrix_conditions :
    (63 : Int)*(63)+(84)*(84)=(105)*(105) ∧
    (63)*(84)+(84)*(-63)=0 ∧
    (84)*(84)+(-63)*(-63)=(105)*(105) := by decide
theorem determinant_condition : (63 : Int)*(-63)-(84)*(84)=(-1)*(105)*(105) := by decide
def imageX (x y : Int) : Int := (63)*x+(84)*y+(245)
def imageY (x y : Int) : Int := (84)*x+(-63)*y+(-30)
theorem distance_all_inputs (x y u v : Int) :
    norm2 (imageX x y-imageX u v) (imageY x y-imageY u v)=
    (105)*(105)*norm2 (x-u) (y-v) := by
  have hx : imageX x y-imageX u v=(63)*(x-u)+(84)*(y-v) := by
    simp [imageX,Int.mul_sub]; omega
  have hy : imageY x y-imageY u v=(84)*(x-u)+(-63)*(y-v) := by
    simp [imageY,Int.mul_sub]; omega
  rw [hx,hy]
  exact orthogonal_scaled_norm (63) (84) (84) (-63) (105) matrix_conditions.1 matrix_conditions.2.1 matrix_conditions.2.2 (x-u) (y-v)
theorem orientation_all_vectors (x y u v : Int) :
    ((63)*x+(84)*y)*((84)*u+(-63)*v)-((84)*x+(-63)*y)*((63)*u+(84)*v)=
    ((-1)*(105)*(105))*(x*v-y*u) := by
  rw [matrix_determinant,determinant_condition]
#print axioms distance_all_inputs
#print axioms orientation_all_vectors
end PerfectPower.CheckedGeometry.P148460bc42225a9ad2612c8785ee1decb139ee7055fe825986202d652f2ecfc5
