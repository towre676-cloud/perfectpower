import PerfectPower.EuclidMethods
namespace PerfectPower.CheckedEuclid.P58accbee9dedac583477c52159f450b659e55ad33b4231a2bd05fa946149a3ff
open PerfectPower.EuclidMethods
def A : List Int := [0,1]
def B : List Int := [1,2]
def U : List Int := [-2]
def V : List Int := [1]
theorem coefficient_identity : addPoly (mulPoly U A) (mulPoly V B) = [1,0] := by decide
theorem identity_all_inputs (n : Int) : horner U n*horner A n+horner V n*horner B n=(1) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add, horner_mul, horner_mul] at h
  simpa [horner] using h
theorem common_divisor_bound (n d : Int) (hA : d ∣ horner A n) (hB : d ∣ horner B n) : d ∣ (1) :=
  common_divisor_bezout (horner A n) (horner B n) (horner U n) (horner V n) (1) d hA hB (identity_all_inputs n)
#print axioms identity_all_inputs
#print axioms common_divisor_bound
end PerfectPower.CheckedEuclid.P58accbee9dedac583477c52159f450b659e55ad33b4231a2bd05fa946149a3ff
