import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedGraph.Pbaf2b59f9b254c2c54cd880d725f9f0fd0b06dd5d57f916056084ac79fd96ffc
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
def edges : List Edge := [(1,3,(3 : Int)), (1,4,(5 : Int)), (1,7,(5 : Int)), (1,8,(3 : Int)), (2,5,(2 : Int)), (2,6,(4 : Int)), (2,9,(2 : Int)), (3,4,(2 : Int)), (3,7,(4 : Int)), (3,8,(2 : Int)), (4,5,(6 : Int)), (4,7,(6 : Int)), (4,8,(4 : Int)), (4,11,(4 : Int)), (4,13,(2 : Int)), (5,6,(6 : Int)), (5,9,(4 : Int)), (5,11,(2 : Int)), (5,13,(4 : Int)), (6,7,(6 : Int)), (6,9,(2 : Int)), (6,10,(2 : Int)), (6,12,(4 : Int)), (7,8,(2 : Int)), (7,10,(4 : Int)), (7,12,(2 : Int)), (10,12,(2 : Int)), (11,13,(2 : Int)), (3,1,(3 : Int)), (4,1,(5 : Int)), (7,1,(5 : Int)), (8,1,(3 : Int)), (5,2,(2 : Int)), (6,2,(4 : Int)), (9,2,(2 : Int)), (4,3,(2 : Int)), (7,3,(4 : Int)), (8,3,(2 : Int)), (5,4,(6 : Int)), (7,4,(6 : Int)), (8,4,(4 : Int)), (11,4,(4 : Int)), (13,4,(2 : Int)), (6,5,(6 : Int)), (9,5,(4 : Int)), (11,5,(2 : Int)), (13,5,(4 : Int)), (7,6,(6 : Int)), (9,6,(2 : Int)), (10,6,(2 : Int)), (12,6,(4 : Int)), (8,7,(2 : Int)), (10,7,(4 : Int)), (12,7,(2 : Int)), (12,10,(2 : Int)), (13,11,(2 : Int))]
def potentials : List Int := [(0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
def reachable (u : Nat) : Prop := u ∈ ([0] : List Nat)
instance (u : Nat) : Decidable (reachable u) := by unfold reachable; infer_instance
theorem closed : ∀ e ∈ edges, reachable e.1 → reachable e.2.1 := by decide
theorem source_inside : reachable 0 := by decide
theorem target_outside : ¬reachable 1 := by decide
theorem no_route : ∀ c, ¬Walk edges 0 1 c :=
  no_walk_outside edges reachable closed source_inside target_outside
#print axioms no_route
end PerfectPower.CheckedGraph.Pbaf2b59f9b254c2c54cd880d725f9f0fd0b06dd5d57f916056084ac79fd96ffc
