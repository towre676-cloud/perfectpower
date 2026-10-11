import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedGraph.P34271842c53b8da39e1ed20ebf6abdd165770f5943e73d175e262107eaedda1e
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
def edges : List Edge := []
def potentials : List Int := [(0 : Int)]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
theorem retained_path : Walk edges 0 0 (0) := by
  show Walk edges 0 0 (0)
  exact Walk.nil 0
theorem dual_equality : (0 : Int) = potential 0 - potential 0 := by decide
theorem no_cheaper_walk {other : Int} (walk : Walk edges 0 0 other) : (0 : Int) ≤ other :=
  optimal_walk edges potential edge_bounds dual_equality walk
#print axioms retained_path
#print axioms no_cheaper_walk
end PerfectPower.CheckedGraph.P34271842c53b8da39e1ed20ebf6abdd165770f5943e73d175e262107eaedda1e
