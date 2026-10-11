import Std

/-! Algebraic foundations for exact Euclidean rational transformations.
Integer matrices represent rational matrices after clearing denominators. -/
namespace PerfectPower.GeometryFoundations

def norm2 (x y : Int) : Int := x*x+y*y

theorem matrix_norm (a b c e x y : Int) :
    norm2 (a*x+b*y) (c*x+e*y) =
    (a*a+c*c)*(x*x)+(a*b+c*e)*(x*y)+(a*b+c*e)*(x*y)+(b*b+e*e)*(y*y) := by
  simp only [norm2,Int.add_mul,Int.mul_add]
  simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
  omega

theorem orthogonal_scaled_norm (a b c e d : Int)
    (h1 : a*a+c*c=d*d) (h2 : a*b+c*e=0) (h3 : b*b+e*e=d*d)
    (x y : Int) : norm2 (a*x+b*y) (c*x+e*y)=d*d*norm2 x y := by
  rw [matrix_norm,h1,h2,h3]
  simp [norm2,Int.mul_add]

theorem matrix_determinant (a b c e x y u v : Int) :
    (a*x+b*y)*(c*u+e*v)-(c*x+e*y)*(a*u+b*v)=
    (a*e-b*c)*(x*v-y*u) := by
  simp only [Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub]
  simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
  omega

theorem midpoint_between (a c : Int) (h : a < c) :
    2*a<a+c ∧ a+c<2*c := by omega

theorem signed_area_triangle (ax ay bx by_ cx cy : Int) :
    (ax*by_-ay*bx)+(bx*cy-by_*cx)+(cx*ay-cy*ax)=
    (bx-ax)*(cy-ay)-(by_-ay)*(cx-ax) := by
  simp only [Int.sub_mul,Int.mul_sub]
  simp only [Int.mul_comm]
  omega

#print axioms orthogonal_scaled_norm
#print axioms matrix_determinant
#print axioms midpoint_between
#print axioms signed_area_triangle
end PerfectPower.GeometryFoundations
