import PerfectPower.EllipticDivision

namespace PerfectPower.TriplingCoordinates
variable {F : Type*} [Field F]

def psi (a b x : F) := 3*x^4+6*a*x^2+12*b*x-a^2
def sixth (a b x : F) :=
  x^6+5*a*x^4+20*b*x^3-5*a^2*x^2-4*a*b*x-8*b^2-a^3
def phi (a b x : F) := x*(psi a b x)^2-8*(x^3+a*x+b)*sixth a b x

theorem psi_displacement (a b x : F) :
    12*x*(x^3+a*x+b)-(3*x^2+a)^2 = psi a b x := by
  unfold psi; ring

/-- The compact producer and expanded replay numerator are the same polynomial. -/
theorem expanded_phi (a b x : F) : phi a b x =
    x^9-12*a*x^7-96*b*x^6+30*a^2*x^5-24*a*b*x^4+
    (36*a^3+48*b^2)*x^3+48*a^2*b*x^2+
    (9*a^4+96*a*b^2)*x+8*a^3*b+64*b^3 := by
  unfold phi psi sixth; ring

/-- Denominator-free secant-after-tangent identity. -/
theorem tripling_numerator (a b x : F) :
    ((3*x^2+a)*psi a b x-16*(x^3+a*x+b)^2)^2-
      (3*x^2+a)^2*(psi a b x)^2+
      4*(x^3+a*x+b)*x*(psi a b x)^2 =
      4*(x^3+a*x+b)*phi a b x := by
  unfold phi psi sixth; ring

/-- The nonexceptional rational coordinate is exactly the degree-nine fibre equation.
The kernel/branch cases are deliberately not assigned an affine quotient. -/
theorem tripling_x_iff (a b x u : F) (h : psi a b x ≠ 0) :
    phi a b x / (psi a b x)^2 = u ↔
      phi a b x-u*(psi a b x)^2=0 := by
  rw [div_eq_iff (pow_ne_zero 2 h), sub_eq_zero]

end PerfectPower.TriplingCoordinates
