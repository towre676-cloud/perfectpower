import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedMesh.Mba85758569954ffd225040d86a87d5fac2f8998b86114e2be6d3962cffe27cf4
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
def vertices : List Point := [((0 : Int),(0 : Int)), ((0 : Int),(4 : Int)), ((2 : Int),(2 : Int)), ((4 : Int),(0 : Int)), ((4 : Int),(4 : Int))]
def polygon : List Point := [((0 : Int),(0 : Int)), ((4 : Int),(0 : Int)), ((4 : Int),(4 : Int)), ((0 : Int),(4 : Int))]
def triangles : List (List Point) := [[((0 : Int),(0 : Int)), ((4 : Int),(0 : Int)), ((2 : Int),(2 : Int))], [((4 : Int),(0 : Int)), ((4 : Int),(4 : Int)), ((2 : Int),(2 : Int))], [((4 : Int),(4 : Int)), ((0 : Int),(4 : Int)), ((2 : Int),(2 : Int))], [((0 : Int),(4 : Int)), ((0 : Int),(0 : Int)), ((2 : Int),(2 : Int))]]
theorem vertices_ordered : ∀ e ∈ vertices.zip vertices.tail,
    e.1.1 < e.2.1 ∨ (e.1.1 = e.2.1 ∧ e.1.2 < e.2.2) := by decide
theorem triangle_0_positive : (0 : Int) < side ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)) := by decide
theorem triangle_1_positive : (0 : Int) < side ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)) := by decide
theorem triangle_2_positive : (0 : Int) < side ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ((2 : Int),(2 : Int)) := by decide
theorem triangle_3_positive : (0 : Int) < side ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ((2 : Int),(2 : Int)) := by decide
theorem separation_0_1 : separated [((0 : Int),(0 : Int)), ((4 : Int),(0 : Int)), ((2 : Int),(2 : Int))] [((4 : Int),(0 : Int)), ((4 : Int),(4 : Int)), ((2 : Int),(2 : Int))] ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)) (1) := by decide
theorem separation_0_2 : separated [((0 : Int),(0 : Int)), ((4 : Int),(0 : Int)), ((2 : Int),(2 : Int))] [((4 : Int),(4 : Int)), ((0 : Int),(4 : Int)), ((2 : Int),(2 : Int))] ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)) (1) := by decide
theorem separation_0_3 : separated [((0 : Int),(0 : Int)), ((4 : Int),(0 : Int)), ((2 : Int),(2 : Int))] [((0 : Int),(4 : Int)), ((0 : Int),(0 : Int)), ((2 : Int),(2 : Int))] ((2 : Int),(2 : Int)) ((0 : Int),(0 : Int)) (1) := by decide
theorem separation_1_2 : separated [((4 : Int),(0 : Int)), ((4 : Int),(4 : Int)), ((2 : Int),(2 : Int))] [((4 : Int),(4 : Int)), ((0 : Int),(4 : Int)), ((2 : Int),(2 : Int))] ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)) (1) := by decide
theorem separation_1_3 : separated [((4 : Int),(0 : Int)), ((4 : Int),(4 : Int)), ((2 : Int),(2 : Int))] [((0 : Int),(4 : Int)), ((0 : Int),(0 : Int)), ((2 : Int),(2 : Int))] ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)) (1) := by decide
theorem separation_2_3 : separated [((4 : Int),(4 : Int)), ((0 : Int),(4 : Int)), ((2 : Int),(2 : Int))] [((0 : Int),(4 : Int)), ((0 : Int),(0 : Int)), ((2 : Int),(2 : Int))] ((0 : Int),(4 : Int)) ((2 : Int),(2 : Int)) (1) := by decide
theorem polygon_area : (side ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ((0 : Int),(0 : Int)))+(side ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ((0 : Int),(0 : Int)))+(side ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)))+(side ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ((0 : Int),(0 : Int)))=(32 : Int) := by decide
theorem area_total : (side ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)))+(side ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)))+(side ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ((2 : Int),(2 : Int)))+(side ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ((2 : Int),(2 : Int)))=(32 : Int) := by decide
theorem subdivision_membership : onSegment ((0 : Int),(0 : Int)) ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ∧ onSegment ((4 : Int),(0 : Int)) ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ∧ onSegment ((4 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ∧ onSegment ((4 : Int),(4 : Int)) ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ∧ onSegment ((0 : Int),(4 : Int)) ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ∧ onSegment ((4 : Int),(4 : Int)) ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ∧ onSegment ((0 : Int),(0 : Int)) ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ∧ onSegment ((0 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ∧ onSegment ((0 : Int),(0 : Int)) ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ∧ onSegment ((4 : Int),(0 : Int)) ((0 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((4 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((0 : Int),(0 : Int)) ((2 : Int),(2 : Int)) ((0 : Int),(0 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((2 : Int),(2 : Int)) ((0 : Int),(0 : Int)) ∧ onSegment ((4 : Int),(0 : Int)) ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ∧ onSegment ((4 : Int),(4 : Int)) ((4 : Int),(0 : Int)) ((4 : Int),(4 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((4 : Int),(4 : Int)) ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((2 : Int),(2 : Int)) ((4 : Int),(0 : Int)) ∧ onSegment ((4 : Int),(0 : Int)) ((2 : Int),(2 : Int)) ((4 : Int),(0 : Int)) ∧ onSegment ((0 : Int),(4 : Int)) ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ∧ onSegment ((4 : Int),(4 : Int)) ((4 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ∧ onSegment ((0 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((0 : Int),(4 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((2 : Int),(2 : Int)) ((4 : Int),(4 : Int)) ∧ onSegment ((4 : Int),(4 : Int)) ((2 : Int),(2 : Int)) ((4 : Int),(4 : Int)) ∧ onSegment ((0 : Int),(0 : Int)) ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ∧ onSegment ((0 : Int),(4 : Int)) ((0 : Int),(4 : Int)) ((0 : Int),(0 : Int)) ∧ onSegment ((0 : Int),(0 : Int)) ((0 : Int),(0 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((0 : Int),(0 : Int)) ((2 : Int),(2 : Int)) ∧ onSegment ((0 : Int),(4 : Int)) ((2 : Int),(2 : Int)) ((0 : Int),(4 : Int)) ∧ onSegment ((2 : Int),(2 : Int)) ((2 : Int),(2 : Int)) ((0 : Int),(4 : Int)) := by decide
def sourceEdges : List (Point × Point) := [(((0 : Int),(0 : Int)),((4 : Int),(0 : Int))), (((4 : Int),(0 : Int)),((4 : Int),(4 : Int))), (((4 : Int),(4 : Int)),((0 : Int),(4 : Int))), (((0 : Int),(4 : Int)),((0 : Int),(0 : Int)))]
def meshEdges : List (Point × Point) := [(((0 : Int),(0 : Int)),((4 : Int),(0 : Int))), (((4 : Int),(0 : Int)),((2 : Int),(2 : Int))), (((2 : Int),(2 : Int)),((0 : Int),(0 : Int))), (((4 : Int),(0 : Int)),((4 : Int),(4 : Int))), (((4 : Int),(4 : Int)),((2 : Int),(2 : Int))), (((2 : Int),(2 : Int)),((4 : Int),(0 : Int))), (((4 : Int),(4 : Int)),((0 : Int),(4 : Int))), (((0 : Int),(4 : Int)),((2 : Int),(2 : Int))), (((2 : Int),(2 : Int)),((4 : Int),(4 : Int))), (((0 : Int),(4 : Int)),((0 : Int),(0 : Int))), (((0 : Int),(0 : Int)),((2 : Int),(2 : Int))), (((2 : Int),(2 : Int)),((0 : Int),(4 : Int)))]
theorem edge_endpoints_admitted : ∀ e ∈ sourceEdges ++ meshEdges, e.1 ∈ vertices ∧ e.2 ∈ vertices := by decide
def sourceAtoms : List (Nat × Nat) := sourceEdges.flatMap (fun e => atomicLine vertices e.1 e.2)
def meshAtoms : List (Nat × Nat) := meshEdges.flatMap (fun e => atomicLine vertices e.1 e.2)
def atomicEdges : List (Nat × Nat) := (List.range 5).flatMap (fun u => (List.range 5).map (fun v => (u,v)))
theorem boundary_counts : ∀ e ∈ atomicEdges,
    signedMultiplicity meshAtoms e.1 e.2 = signedMultiplicity sourceAtoms e.1 e.2 := by decide
#print axioms boundary_counts
#print axioms area_total
#print axioms separation_0_1
#print axioms separation_0_2
#print axioms separation_0_3
#print axioms separation_1_2
#print axioms separation_1_3
#print axioms separation_2_3
end PerfectPower.CheckedMesh.Mba85758569954ffd225040d86a87d5fac2f8998b86114e2be6d3962cffe27cf4
