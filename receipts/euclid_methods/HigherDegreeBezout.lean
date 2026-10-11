import PerfectPower.EuclidMethods
namespace PerfectPower.CheckedEuclid.P3a2b8a07515f85b96770f313864ad1b17fab77de35265367a021a55e4c69883e
open PerfectPower.EuclidMethods
def A : List Int := [-2,0,1]
def B : List Int := [3,1]
def U : List Int := [1]
def V : List Int := [3,-1]
theorem coefficient_identity : addPoly (mulPoly U A) (mulPoly V B) = [7,0,0] := by decide
theorem identity_all_inputs (n : Int) : horner U n*horner A n+horner V n*horner B n=(7) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add, horner_mul, horner_mul] at h
  simpa [horner] using h
theorem common_divisor_bound (n d : Int) (hA : d ∣ horner A n) (hB : d ∣ horner B n) : d ∣ (7) :=
  common_divisor_bezout (horner A n) (horner B n) (horner U n) (horner V n) (7) d hA hB (identity_all_inputs n)
#print axioms identity_all_inputs
#print axioms common_divisor_bound
end PerfectPower.CheckedEuclid.P3a2b8a07515f85b96770f313864ad1b17fab77de35265367a021a55e4c69883e
