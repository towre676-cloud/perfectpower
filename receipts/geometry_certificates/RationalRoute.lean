import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedGraph.P293eef6184299c4529842bdc8a38fc7037e3fec46a91b45a13cb04da823563c6
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
def edges : List Edge := [(0,1,(2 : Int)), (1,0,(2 : Int))]
def potentials : List Int := [(0 : Int), (2 : Int)]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
theorem retained_path : Walk edges 0 1 (2) := by
  show Walk edges 0 1 (2+0)
  exact Walk.cons (edges := edges) (u := 0) (v := 1) (t := 1) (w := (2)) (c := (0)) (by decide) (Walk.nil 1)
theorem dual_equality : (2 : Int) = potential 1 - potential 0 := by decide
theorem no_cheaper_walk {other : Int} (walk : Walk edges 0 1 other) : (2 : Int) ≤ other :=
  optimal_walk edges potential edge_bounds dual_equality walk
#print axioms retained_path
#print axioms no_cheaper_walk
end PerfectPower.CheckedGraph.P293eef6184299c4529842bdc8a38fc7037e3fec46a91b45a13cb04da823563c6
