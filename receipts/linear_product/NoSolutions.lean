import PerfectPower.LinearProductChart
namespace PerfectPower.CheckedLinearProduct.Pb92a0fa464bd6d1c6bc9196e9d0dcdb1a72527b659f31f8f2ea46cc9560442a5
open PerfectPower.EuclidMethods PerfectPower.LinearProductChart
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def F : List Int := [6,20,16]
def X : List Int := [20,32]
theorem coefficient_identity : addPoly (mulPoly X X) (scalePoly (-((2*(4 : Int))*(2*(4)))) F) = [16,0,0] := by decide
theorem transform (n : Int) :
    (2*(16)*n+(20))*(2*(16)*n+(20))-(2*(4))*(2*(4))*horner F n=(16) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add,horner_mul,horner_scale] at h
  simpa [X,horner,Int.mul_comm,Int.add_comm,Int.mul_neg,Int.neg_mul,Int.sub_eq_add_neg] using h
def solutions : List (Int × Int) := []
def chart_points : List (Int × Int) := []
theorem computed_chart : points (horner F) (16) (20) (4) (16) = chart_points := by decide
theorem lists_agree : chart_points ⊆ solutions ∧ solutions ⊆ chart_points := by decide
theorem all_integer_solutions (n y : Int) :
    y*y=(2*n+(1))*(8*n+(6)) ↔ (n,y) ∈ solutions := by
  have h := complete (horner F) (16) (20) (4) (16) (by decide) (by decide) (by decide) transform n y
  rw [computed_chart] at h
  have he : horner F n=(2*n+(1))*(8*n+(6)) := by
    have hh := horner_mul ([1,2] : List Int) [6,8] n
    simpa [mulPoly,addPoly,scalePoly,horner,F,Int.mul_comm,Int.add_comm] using hh
  rw [he] at h
  exact h.trans ⟨fun hp => lists_agree.1 hp, fun hp => lists_agree.2 hp⟩
#print axioms transform
#print axioms all_integer_solutions
end PerfectPower.CheckedLinearProduct.Pb92a0fa464bd6d1c6bc9196e9d0dcdb1a72527b659f31f8f2ea46cc9560442a5
