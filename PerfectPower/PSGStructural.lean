import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/- Exact structural algebra recovered from PSG. Python execution, packet
   decoding and infinite analytic conclusions are not asserted here. -/
namespace PerfectPower.PSGStructural
variable {K : Type*} [CommRing K]

theorem quadratic_norm_identity (A B D t : K) :
    A^2-D*B^2=(A-t*B)*(A+t*B)+B^2*(t^2-D) := by ring

theorem quadratic_elimination_identity (A B C D t : K) :
    A^2-D*B^2=(A-t*B)*(A+t*B+(t^2-D)*C)+
      (B^2-(A-t*B)*C)*(t^2-D) := by ring

theorem quadratic_elimination_sound (A B C D t : K)
    (hp : A+t*B+(t^2-D)*C=0) (ht : t^2-D=0) : A^2-D*B^2=0 := by
  rw [quadratic_elimination_identity, hp, ht]
  ring

theorem exceptional_source (A C D t : K) (ht : t^2-D=0) :
    A+t*0+(t^2-D)*C=A := by rw [ht]; ring

theorem source_at_reconstruction (A B C D t : K)
    (hlinear : A+t*B=0) (ht : t^2-D=0) :
    A+t*B+(t^2-D)*C=0 := by rw [hlinear, ht]; ring

theorem cofactor_product (H J k l XH XJ : K)
    (hH : XH=k*H) (hJ : XJ=l*J) :
    XH*J+H*XJ=(k+l)*(H*J) := by rw [hH,hJ]; ring

theorem redundant_pair (F G A B : K) (hF : F=0) (hG : G=0) :
    A*F+B*G=0 := by rw [hF,hG]; ring

theorem affine_norm_transport (a b c d u v x y D : K) :
    (a*x+b*y+u)^2-D*(c*x+d*y+v)^2=
    (a^2-D*c^2)*x^2+2*(a*b-D*c*d)*x*y+(b^2-D*d^2)*y^2+
    2*(a*u-D*c*v)*x+2*(b*u-D*d*v)*y+(u^2-D*v^2) := by ring

section Field
variable {F : Type*} [Field F]

theorem regular_linear_unique (A B t u : F) (hB : B≠0)
    (ht : A+t*B=0) (hu : A+u*B=0) : t=u := by
  have h : (t-u)*B=0 := by linear_combination ht-hu
  have hs : t-u=0 := (mul_eq_zero.mp h).resolve_right hB
  exact sub_eq_zero.mp hs

theorem norm_regular_square (A B D : F) (hB : B≠0)
    (hn : A^2-D*B^2=0) : (-A/B)^2=D := by
  field_simp [hB]
  linear_combination hn

theorem regular_reconstruction (A B : F) (hB : B≠0) : A+(-A/B)*B=0 := by
  field_simp [hB]
end Field
end PerfectPower.PSGStructural
