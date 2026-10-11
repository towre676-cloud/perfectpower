import PerfectPower.LinearProductChart
namespace PerfectPower.CheckedLinearProduct.P3878f66f384945d25d35e36fdada68555b26f4ed89d4e7c8d9306619ac6e3ad9
open PerfectPower.EuclidMethods PerfectPower.LinearProductChart
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def F : List Int := [3,21,36]
def X : List Int := [21,72]
theorem coefficient_identity : addPoly (mulPoly X X) (scalePoly (-((2*(6 : Int))*(2*(6)))) F) = [9,0,0] := by decide
theorem transform (n : Int) :
    (2*(36)*n+(21))*(2*(36)*n+(21))-(2*(6))*(2*(6))*horner F n=(9) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add,horner_mul,horner_scale] at h
  simpa [X,horner,Int.mul_comm,Int.add_comm,Int.mul_neg,Int.neg_mul,Int.sub_eq_add_neg] using h
def solutions : List (Int × Int) := []
def chart_points : List (Int × Int) := []
theorem computed_chart : points (horner F) (36) (21) (6) (9) = chart_points := by decide
theorem lists_agree : chart_points ⊆ solutions ∧ solutions ⊆ chart_points := by decide
theorem all_integer_solutions (n y : Int) :
    y*y=(4*n+(1))*(9*n+(3)) ↔ (n,y) ∈ solutions := by
  have h := complete (horner F) (36) (21) (6) (9) (by decide) (by decide) (by decide) transform n y
  rw [computed_chart] at h
  have he : horner F n=(4*n+(1))*(9*n+(3)) := by
    have hh := horner_mul ([1,4] : List Int) [3,9] n
    simpa [mulPoly,addPoly,scalePoly,horner,F,Int.mul_comm,Int.add_comm] using hh
  rw [he] at h
  exact h.trans ⟨fun hp => lists_agree.1 hp, fun hp => lists_agree.2 hp⟩
#print axioms transform
#print axioms all_integer_solutions
end PerfectPower.CheckedLinearProduct.P3878f66f384945d25d35e36fdada68555b26f4ed89d4e7c8d9306619ac6e3ad9
