import PerfectPower.Brainpool384
import PerfectPower.CurveReadout
import Mathlib.Data.ZMod.Basic

/-! Concrete Brainpool-384 equation and export transport in the residue ring.
Primality and implementation timing are not premises or conclusions of these results. -/
namespace PerfectPower.BrainpoolReadout
open Brainpool384
abbrev R := ZMod p.toNat

def W : R := 0x653667e5e2ff559db64702e4b51213d4d9b05653323d87347081dca72f5055b074727623d9832e67eaf3b49f6c077e8

theorem inverse_scale : W * (Z : R) = 1 := by decide +kernel

theorem coefficients : (A : R)*(Z : R)^4 = -3 ∧ (B : R)*(Z : R)^6 = (Bt : R) := by
  decide +kernel

theorem equation_iff (x y : R) :
    ((Z : R)^3*y)^2 - ((Z : R)^2*x)^3 + 3*((Z : R)^2*x) - (Bt : R) = 0 ↔
      y^2-x^3-(A : R)*x-(B : R)=0 := by
  have h := CurveReadout.equation_iff (A : R) (B : R) (Z : R) W x y inverse_scale
  rw [coefficients.1, coefficients.2] at h
  simpa only [neg_mul, sub_neg_eq_add] using h

theorem generator_export : W^2*(Gtx : R) = (Gx : R) ∧ W^3*(Gty : R) = (Gy : R) := by
  have h := CurveReadout.export_coordinates (Z : R) W (Gx : R) (Gy : R) inverse_scale
  have hx : (Z : R)^2*(Gx : R) = (Gtx : R) := by decide +kernel
  have hy : (Z : R)^3*(Gy : R) = (Gty : R) := by decide +kernel
  rwa [hx,hy] at h
end PerfectPower.BrainpoolReadout
