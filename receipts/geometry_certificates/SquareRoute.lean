import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedGraph.Pc6009fcd7407ba1ed35c388c56148422cc5a41fd0da158dc99d10cce746582ad
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
def edges : List Edge := [(0,2,(2 : Int)), (0,5,(2 : Int)), (1,3,(2 : Int)), (1,4,(2 : Int)), (2,3,(2 : Int)), (2,5,(2 : Int)), (3,4,(2 : Int)), (4,5,(2 : Int)), (2,0,(2 : Int)), (5,0,(2 : Int)), (3,1,(2 : Int)), (4,1,(2 : Int)), (3,2,(2 : Int)), (5,2,(2 : Int)), (4,3,(2 : Int)), (5,4,(2 : Int))]
def potentials : List Int := [(0 : Int), (6 : Int), (2 : Int), (4 : Int), (4 : Int), (2 : Int)]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
theorem retained_path : Walk edges 0 1 (6) := by
  show Walk edges 0 1 (2+2+2+0)
  exact Walk.cons (edges := edges) (u := 0) (v := 2) (t := 1) (w := (2)) (c := (4)) (by decide) (Walk.cons (edges := edges) (u := 2) (v := 3) (t := 1) (w := (2)) (c := (2)) (by decide) (Walk.cons (edges := edges) (u := 3) (v := 1) (t := 1) (w := (2)) (c := (0)) (by decide) (Walk.nil 1)))
theorem dual_equality : (6 : Int) = potential 1 - potential 0 := by decide
theorem no_cheaper_walk {other : Int} (walk : Walk edges 0 1 other) : (6 : Int) ≤ other :=
  optimal_walk edges potential edge_bounds dual_equality walk
#print axioms retained_path
#print axioms no_cheaper_walk
end PerfectPower.CheckedGraph.Pc6009fcd7407ba1ed35c388c56148422cc5a41fd0da158dc99d10cce746582ad
