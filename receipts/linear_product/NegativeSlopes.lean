import PerfectPower.LinearProductChart
namespace PerfectPower.CheckedLinearProduct.Pe3e60a590ab3e7b2e876d34aeac6994f0fa4a78b2fea7621953d133b48babb57
open PerfectPower.EuclidMethods PerfectPower.LinearProductChart
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def F : List Int := [0,-6,1]
def X : List Int := [-6,2]
theorem coefficient_identity : addPoly (mulPoly X X) (scalePoly (-((2*(1 : Int))*(2*(1)))) F) = [36,0,0] := by decide
theorem transform (n : Int) :
    (2*(1)*n+(-6))*(2*(1)*n+(-6))-(2*(1))*(2*(1))*horner F n=(36) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add,horner_mul,horner_scale] at h
  simpa [X,horner,Int.mul_comm,Int.add_comm,Int.mul_neg,Int.neg_mul,Int.sub_eq_add_neg] using h
def solutions : List (Int × Int) := [(-2,-4),(-2,4),(0,0),(6,0),(8,-4),(8,4)]
def chart_points : List (Int × Int) := [(-2,4),(0,0),(-2,-4),(8,4),(6,0),(8,-4)]
theorem computed_chart : points (horner F) (1) (-6) (1) (36) = chart_points := by decide
theorem lists_agree : chart_points ⊆ solutions ∧ solutions ⊆ chart_points := by decide
theorem all_integer_solutions (n y : Int) :
    y*y=(-1*n+(0))*(-1*n+(6)) ↔ (n,y) ∈ solutions := by
  have h := complete (horner F) (1) (-6) (1) (36) (by decide) (by decide) (by decide) transform n y
  rw [computed_chart] at h
  have he : horner F n=(-1*n+(0))*(-1*n+(6)) := by
    have hh := horner_mul ([0,-1] : List Int) [6,-1] n
    simpa [mulPoly,addPoly,scalePoly,horner,F,Int.mul_comm,Int.add_comm] using hh
  rw [he] at h
  exact h.trans ⟨fun hp => lists_agree.1 hp, fun hp => lists_agree.2 hp⟩
#print axioms transform
#print axioms all_integer_solutions
end PerfectPower.CheckedLinearProduct.Pe3e60a590ab3e7b2e876d34aeac6994f0fa4a78b2fea7621953d133b48babb57
