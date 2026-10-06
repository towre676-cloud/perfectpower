import PerfectPower.EllipticPointDivision

namespace PerfectPower.EllipticPointLaw
open WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : Affine F)

def coordinates : W.Point → Option (F × F)
  | .zero => none
  | @Point.some _ _ _ x y _ => some (x,y)

open scoped Classical in
/-- Generalized Weierstrass coordinate algorithm, including vertical and infinity cases. -/
noncomputable def coordinateAdd : Option (F × F) → Option (F × F) → Option (F × F)
  | none, Q => Q
  | P, none => P
  | some (x,y), some (u,v) =>
    if x=u ∧ y=-v-W.a₁*u-W.a₃ then none else
      let s := if x=u then
        (3*x^2+2*W.a₂*x+W.a₄-W.a₁*y)/(2*y+W.a₁*x+W.a₃)
        else (y-v)/(x-u)
      let z := s^2+W.a₁*s-W.a₂-x-u
      some (z, -(s*(z-x)+y)-W.a₁*z-W.a₃)

/-- The typed coordinate algorithm refines addition on Mathlib's actual point group. -/
theorem add_refinement (P Q : W.Point) :
    coordinates W (P+Q)=coordinateAdd W (coordinates W P) (coordinates W Q) := by
  classical
  cases P with
  | zero => cases Q <;> rfl
  | @some x y h =>
    cases Q with
    | zero => rfl
    | @some u v k =>
      by_cases hv : x=u ∧ y=W.negY u v
      · rw [Point.add_of_Y_eq hv.1 hv.2]
        simp only [coordinates, coordinateAdd, negY] at *
        rw [if_pos hv]
      · rw [Point.add_some hv]
        simp only [coordinates, coordinateAdd]
        have hv' : ¬(x=u ∧ y=-v-W.a₁*u-W.a₃) := hv
        rw [if_neg hv']
        have hs : W.slope x u y v =
            if x=u then (3*x^2+2*W.a₂*x+W.a₄-W.a₁*y)/(2*y+W.a₁*x+W.a₃)
            else (y-v)/(x-u) := by
          by_cases hx : x=u
          · have hy : y≠W.negY u v := fun hy => hv ⟨hx,hy⟩
            rw [slope_of_Y_ne hx hy, if_pos hx]
            congr 1
            simp only [negY]
            ring
          · rw [slope_of_X_ne hx, if_neg hx]
        simp only [addX, addY, negAddY, negY, hs]

/-- Little-endian binary scalar interpretation, including the empty zero packet. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b::bs => (if b then 1 else 0)+2*binaryValue bs

noncomputable def coordinateBinary (P : Option (F × F)) : List Bool → Option (F × F)
  | [] => none
  | b::bs => coordinateAdd W (if b then P else none)
      (coordinateAdd W (coordinateBinary P bs) (coordinateBinary P bs))

theorem binary_refinement (P : W.Point) (bits : List Bool) :
    coordinates W (binaryValue bits • P)=coordinateBinary W (coordinates W P) bits := by
  induction bits with
  | nil => simp [binaryValue, coordinateBinary, coordinates]
  | cons b bs ih =>
    cases b <;>
      simp [binaryValue, coordinateBinary, add_nsmul, mul_nsmul, two_nsmul,
        add_refinement, ih, coordinateAdd]

end PerfectPower.EllipticPointLaw
