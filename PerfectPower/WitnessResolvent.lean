import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
noncomputable section
namespace PerfectPower.WitnessResolvent
section Orbit
variable {S : Type*} [Ring S]

def orbit (a : S) : PowerSeries S := PowerSeries.mk (fun n => a ^ n)

/-- The actual all-power formal series satisfies the resolvent equation. -/
theorem orbit_resolvent (a : S) :
    (1 - PowerSeries.X * PowerSeries.C S a) * orbit a = 1 := by
  rw [sub_mul,one_mul,mul_assoc]
  ext n
  cases n with
  | zero => simp [orbit,PowerSeries.coeff_mk]
  | succ n =>
      simp [orbit,PowerSeries.coeff_mk,PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul,pow_succ']

/-- The resolvent also has a right inverse; no commutativity or spectrum is needed. -/
theorem orbit_right_resolvent (a : S) :
    orbit a * (1 - PowerSeries.C S a * PowerSeries.X) = 1 := by
  rw [mul_sub,mul_one,← mul_assoc]
  ext n
  cases n with
  | zero => simp [orbit,PowerSeries.coeff_mk]
  | succ n =>
      simp [orbit,PowerSeries.coeff_mk,PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_mul_C,pow_succ]

end Orbit

variable {R : Type*} [CommRing R]

/-- A checked numerator identity and constant-one denominator determine every coefficient. -/
theorem unique_series (D V F G : PowerSeries R)
    (constant : PowerSeries.constantCoeff R D=1)
    (left : D*F=V) (right : D*G=V) : F=G := by
  have unit : IsUnit D := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constant]; exact isUnit_one)
  exact unit.mul_left_cancel (left.trans right.symm)

/-- Cross multiplication of checked rational representations proves all-index equality. -/
theorem cross_equal (D E P Q F G : PowerSeries R)
    (hd : PowerSeries.constantCoeff R D=1)
    (he : PowerSeries.constantCoeff R E=1)
    (hf : D*F=P) (hg : E*G=Q) (cross : P*E=Q*D) : F=G := by
  have unitD : IsUnit D := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hd]; exact isUnit_one)
  have unitE : IsUnit E := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [he]; exact isUnit_one)
  apply (unitD.mul unitE).mul_left_cancel
  calc (D*E)*F = (D*F)*E := by ring
       _ = P*E := by rw [hf]
       _ = Q*D := cross
       _ = (E*G)*D := by rw [hg]
       _ = (D*E)*G := by ring

/-- A formal-series equality transports every observable coefficient. -/
theorem all_coefficients (F G : PowerSeries R) (h : F=G) (n : ℕ) :
    PowerSeries.coeff R n F=PowerSeries.coeff R n G := by rw [h]

end PerfectPower.WitnessResolvent
