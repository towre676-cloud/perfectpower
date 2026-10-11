import PerfectPower.GeometrySourceTransport
namespace PerfectPower.CheckedGraph.Pcff841657f9206f2a85cd07653e6ed85e71f9d97c88c4353ce459ccc12337ed2
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
-- Source coordinates, not producer-selected vertex indices.
def sourceObstacles : List (List Point) := [[((0 : Int),(0 : Int)), ((6 : Int),(0 : Int)), ((6 : Int),(5 : Int)), ((4 : Int),(5 : Int)), ((4 : Int),(2 : Int)), ((2 : Int),(2 : Int)), ((2 : Int),(5 : Int)), ((0 : Int),(5 : Int))]]
def sourceStart : Point := ((3 : Int),(3 : Int))
def sourceEnd : Point := ((3 : Int),(6 : Int))
def nodes : List Point := ([sourceStart,sourceEnd] ++ sourceObstacles.flatten).eraseDups
def obstacles : List (List QPoint) := sourceObstacles.map (List.map qpoint)
theorem source_nodes : nodes = [((3 : Int),(3 : Int)), ((3 : Int),(6 : Int)), ((0 : Int),(0 : Int)), ((6 : Int),(0 : Int)), ((6 : Int),(5 : Int)), ((4 : Int),(5 : Int)), ((4 : Int),(2 : Int)), ((2 : Int),(2 : Int)), ((2 : Int),(5 : Int)), ((0 : Int),(5 : Int))] := by decide
def originalObstacles : List (List QPoint) := [[(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ)))]]
def originalNodes : List QPoint := [(((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ)))]
theorem original_source_nodes : originalNodes = ([(((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))),(((3 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ)))] ++ originalObstacles.flatten).eraseDups := by decide +kernel
theorem source_obstacle_scaling : obstacles = originalObstacles.map (List.map (scalePoint ((1 : ℚ)/(1 : ℚ)))) := by decide +kernel
theorem source_node_scaling : ∀ u ∈ List.range 10,
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (originalNodes[u]?.getD (0,0)) := by decide +kernel
def admitted : List (Nat × Nat) := [(0,1), (0,5), (0,6), (0,7), (0,8), (1,0), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (2,3), (2,9), (3,2), (3,4), (4,1), (4,3), (4,5), (4,8), (4,9), (5,0), (5,1), (5,4), (5,6), (5,7), (5,8), (5,9), (6,0), (6,1), (6,5), (6,7), (6,8), (7,0), (7,1), (7,5), (7,6), (7,8), (8,0), (8,1), (8,4), (8,5), (8,6), (8,7), (8,9), (9,1), (9,2), (9,4), (9,5), (9,8)]
def edges : List Edge := graph nodes admitted
theorem source_edges : edges.Perm [(0,1,(3 : Int)), (0,5,(3 : Int)), (0,6,(2 : Int)), (0,7,(2 : Int)), (0,8,(3 : Int)), (1,4,(4 : Int)), (1,5,(2 : Int)), (1,6,(5 : Int)), (1,7,(5 : Int)), (1,8,(2 : Int)), (1,9,(4 : Int)), (2,3,(6 : Int)), (2,9,(5 : Int)), (3,4,(5 : Int)), (4,5,(2 : Int)), (4,8,(4 : Int)), (4,9,(6 : Int)), (5,6,(3 : Int)), (5,7,(5 : Int)), (5,8,(2 : Int)), (5,9,(4 : Int)), (6,7,(2 : Int)), (6,8,(5 : Int)), (7,8,(3 : Int)), (8,9,(2 : Int)), (1,0,(3 : Int)), (5,0,(3 : Int)), (6,0,(2 : Int)), (7,0,(2 : Int)), (8,0,(3 : Int)), (4,1,(4 : Int)), (5,1,(2 : Int)), (6,1,(5 : Int)), (7,1,(5 : Int)), (8,1,(2 : Int)), (9,1,(4 : Int)), (3,2,(6 : Int)), (9,2,(5 : Int)), (4,3,(5 : Int)), (5,4,(2 : Int)), (8,4,(4 : Int)), (9,4,(6 : Int)), (6,5,(3 : Int)), (7,5,(5 : Int)), (8,5,(2 : Int)), (9,5,(4 : Int)), (7,6,(2 : Int)), (8,6,(5 : Int)), (8,7,(3 : Int)), (9,8,(2 : Int))] := by decide
def potentials : List Int := [(0 : Int), (3 : Int), (10 : Int), (10 : Int), (5 : Int), (3 : Int), (2 : Int), (2 : Int), (3 : Int), (5 : Int)]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
theorem retained_path : Walk edges 0 1 (3) := by
  show Walk edges 0 1 (3+0)
  exact Walk.cons (edges := edges) (u := 0) (v := 1) (t := 1) (w := (3)) (c := (0)) (by decide) (Walk.nil 1)
theorem dual_equality : (3 : Int) = potential 1 - potential 0 := by decide
theorem no_cheaper_walk {other : Int} (walk : Walk edges 0 1 other) : (3 : Int) ≤ other :=
  optimal_walk edges potential edge_bounds dual_equality walk
#print axioms retained_path
#print axioms no_cheaper_walk
theorem reconstructed_edges : edges = graph nodes admitted := rfl
def cells_0_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 1))) cells_0_1 := by decide +kernel
theorem pair_0_1 : ((0,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_1)
theorem blockage_0_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 2))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_2 : ((0,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_2)
theorem blockage_0_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 3))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_3 : ((0,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_3)
theorem blockage_0_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 4))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_4 : ((0,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_4)
def cells_0_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 5))) cells_0_5 := by decide +kernel
theorem pair_0_5 : ((0,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_5)
def cells_0_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 6))) cells_0_6 := by decide +kernel
theorem pair_0_6 : ((0,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_6)
def cells_0_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 7))) cells_0_7 := by decide +kernel
theorem pair_0_7 : ((0,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_7)
def cells_0_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 8))) cells_0_8 := by decide +kernel
theorem pair_0_8 : ((0,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_8)
theorem blockage_0_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 9))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_9 : ((0,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_9)
def cells_1_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 0))) cells_1_0 := by decide +kernel
theorem pair_1_0 : ((1,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_0)
theorem blockage_1_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_1_2 : ((1,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_1_2)
theorem blockage_1_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_1_3 : ((1,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_1_3)
def cells_1_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 4))) cells_1_4 := by decide +kernel
theorem pair_1_4 : ((1,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_4)
def cells_1_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 5))) cells_1_5 := by decide +kernel
theorem pair_1_5 : ((1,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_5)
def cells_1_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(4 : ℚ))), (((1 : ℚ)/(4 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 6))) cells_1_6 := by decide +kernel
theorem pair_1_6 : ((1,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_6)
def cells_1_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(4 : ℚ))), (((1 : ℚ)/(4 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 7))) cells_1_7 := by decide +kernel
theorem pair_1_7 : ((1,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_7)
def cells_1_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 8))) cells_1_8 := by decide +kernel
theorem pair_1_8 : ((1,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_8)
def cells_1_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 9))) cells_1_9 := by decide +kernel
theorem pair_1_9 : ((1,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_9)
theorem blockage_2_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_2_0 : ((2,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_2_0)
theorem blockage_2_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_2_1 : ((2,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_2_1)
def cells_2_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 3))) cells_2_3 := by decide +kernel
theorem pair_2_3 : ((2,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_3)
theorem blockage_2_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_2_4 : ((2,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_2_4)
theorem blockage_2_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(5 : ℚ)) = true := by decide +kernel
theorem pair_2_5 : ((2,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(5 : ℚ)) (by norm_num) (by norm_num) blockage_2_5)
theorem blockage_2_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_2_6 : ((2,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_2_6)
theorem blockage_2_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_2_7 : ((2,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_2_7)
theorem blockage_2_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(5 : ℚ)) = true := by decide +kernel
theorem pair_2_8 : ((2,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(5 : ℚ)) (by norm_num) (by norm_num) blockage_2_8)
def cells_2_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(5 : ℚ))), (((2 : ℚ)/(5 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 9))) cells_2_9 := by decide +kernel
theorem pair_2_9 : ((2,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_9)
theorem blockage_3_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_3_0 : ((3,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_3_0)
theorem blockage_3_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_3_1 : ((3,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_3_1)
def cells_3_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 2))) cells_3_2 := by decide +kernel
theorem pair_3_2 : ((3,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_2)
def cells_3_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(5 : ℚ))), (((2 : ℚ)/(5 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 4))) cells_3_4 := by decide +kernel
theorem pair_3_4 : ((3,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_4)
theorem blockage_3_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(5 : ℚ)) = true := by decide +kernel
theorem pair_3_5 : ((3,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(5 : ℚ)) (by norm_num) (by norm_num) blockage_3_5)
theorem blockage_3_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_3_6 : ((3,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_3_6)
theorem blockage_3_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_3_7 : ((3,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_3_7)
theorem blockage_3_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(5 : ℚ)) = true := by decide +kernel
theorem pair_3_8 : ((3,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(5 : ℚ)) (by norm_num) (by norm_num) blockage_3_8)
theorem blockage_3_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_3_9 : ((3,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_3_9)
theorem blockage_4_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_4_0 : ((4,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_4_0)
def cells_4_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 1))) cells_4_1 := by decide +kernel
theorem pair_4_1 : ((4,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_1)
theorem blockage_4_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_4_2 : ((4,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_4_2)
def cells_4_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((3 : ℚ)/(5 : ℚ))), (((3 : ℚ)/(5 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 3))) cells_4_3 := by decide +kernel
theorem pair_4_3 : ((4,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_3)
def cells_4_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 5))) cells_4_5 := by decide +kernel
theorem pair_4_5 : ((4,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_5)
theorem blockage_4_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_4_6 : ((4,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_4_6)
theorem blockage_4_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_4_7 : ((4,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_4_7)
def cells_4_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 8))) cells_4_8 := by decide +kernel
theorem pair_4_8 : ((4,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_8)
def cells_4_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 9))) cells_4_9 := by decide +kernel
theorem pair_4_9 : ((4,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_9)
def cells_5_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 0))) cells_5_0 := by decide +kernel
theorem pair_5_0 : ((5,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_0)
def cells_5_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 1))) cells_5_1 := by decide +kernel
theorem pair_5_1 : ((5,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_1)
theorem blockage_5_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 2))).eval ((11 : ℚ)/(20 : ℚ)) = true := by decide +kernel
theorem pair_5_2 : ((5,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((11 : ℚ)/(20 : ℚ)) (by norm_num) (by norm_num) blockage_5_2)
theorem blockage_5_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 3))).eval ((3 : ℚ)/(10 : ℚ)) = true := by decide +kernel
theorem pair_5_3 : ((5,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(10 : ℚ)) (by norm_num) (by norm_num) blockage_5_3)
def cells_5_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 4))) cells_5_4 := by decide +kernel
theorem pair_5_4 : ((5,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_4)
def cells_5_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 6))) cells_5_6 := by decide +kernel
theorem pair_5_6 : ((5,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_6)
def cells_5_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 7))) cells_5_7 := by decide +kernel
theorem pair_5_7 : ((5,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_7)
def cells_5_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 8))) cells_5_8 := by decide +kernel
theorem pair_5_8 : ((5,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_8)
def cells_5_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 9))) cells_5_9 := by decide +kernel
theorem pair_5_9 : ((5,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_9)
def cells_6_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 0))) cells_6_0 := by decide +kernel
theorem pair_6_0 : ((6,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_0)
def cells_6_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((3 : ℚ)/(4 : ℚ))), (((3 : ℚ)/(4 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 1))) cells_6_1 := by decide +kernel
theorem pair_6_1 : ((6,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_1)
theorem blockage_6_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_6_2 : ((6,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_6_2)
theorem blockage_6_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_6_3 : ((6,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_6_3)
theorem blockage_6_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_6_4 : ((6,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_6_4)
def cells_6_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 5))) cells_6_5 := by decide +kernel
theorem pair_6_5 : ((6,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_5)
def cells_6_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 7))) cells_6_7 := by decide +kernel
theorem pair_6_7 : ((6,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_7)
def cells_6_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 8))) cells_6_8 := by decide +kernel
theorem pair_6_8 : ((6,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_8)
theorem blockage_6_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 9))).eval ((3 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_6_9 : ((6,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_6_9)
def cells_7_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 0))) cells_7_0 := by decide +kernel
theorem pair_7_0 : ((7,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_0)
def cells_7_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((3 : ℚ)/(4 : ℚ))), (((3 : ℚ)/(4 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 1))) cells_7_1 := by decide +kernel
theorem pair_7_1 : ((7,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_1)
theorem blockage_7_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_7_2 : ((7,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_7_2)
theorem blockage_7_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_7_3 : ((7,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_7_3)
theorem blockage_7_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 4))).eval ((3 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_7_4 : ((7,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_7_4)
def cells_7_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 5))) cells_7_5 := by decide +kernel
theorem pair_7_5 : ((7,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_5)
def cells_7_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 6))) cells_7_6 := by decide +kernel
theorem pair_7_6 : ((7,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_6)
def cells_7_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 8))) cells_7_8 := by decide +kernel
theorem pair_7_8 : ((7,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_8)
theorem blockage_7_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_7_9 : ((7,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_7_9)
def cells_8_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 0))) cells_8_0 := by decide +kernel
theorem pair_8_0 : ((8,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_0)
def cells_8_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 1))) cells_8_1 := by decide +kernel
theorem pair_8_1 : ((8,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_1)
theorem blockage_8_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 2))).eval ((3 : ℚ)/(10 : ℚ)) = true := by decide +kernel
theorem pair_8_2 : ((8,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(10 : ℚ)) (by norm_num) (by norm_num) blockage_8_2)
theorem blockage_8_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 3))).eval ((11 : ℚ)/(20 : ℚ)) = true := by decide +kernel
theorem pair_8_3 : ((8,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((11 : ℚ)/(20 : ℚ)) (by norm_num) (by norm_num) blockage_8_3)
def cells_8_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 4))) cells_8_4 := by decide +kernel
theorem pair_8_4 : ((8,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_4)
def cells_8_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 5))) cells_8_5 := by decide +kernel
theorem pair_8_5 : ((8,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_5)
def cells_8_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 6))) cells_8_6 := by decide +kernel
theorem pair_8_6 : ((8,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_6)
def cells_8_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 7))) cells_8_7 := by decide +kernel
theorem pair_8_7 : ((8,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_7)
def cells_8_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 9))) cells_8_9 := by decide +kernel
theorem pair_8_9 : ((8,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_9)
theorem blockage_9_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_9_0 : ((9,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_9_0)
def cells_9_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 1))) cells_9_1 := by decide +kernel
theorem pair_9_1 : ((9,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_1)
def cells_9_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((3 : ℚ)/(5 : ℚ))), (((3 : ℚ)/(5 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 2))) cells_9_2 := by decide +kernel
theorem pair_9_2 : ((9,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_2)
theorem blockage_9_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_9_3 : ((9,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_9_3)
def cells_9_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 4))) cells_9_4 := by decide +kernel
theorem pair_9_4 : ((9,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_4)
def cells_9_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 5))) cells_9_5 := by decide +kernel
theorem pair_9_5 : ((9,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_5)
theorem blockage_9_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_9_6 : ((9,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_9_6)
theorem blockage_9_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_9_7 : ((9,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_9_7)
def cells_9_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 8))) cells_9_8 := by decide +kernel
theorem pair_9_8 : ((9,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_8)
theorem geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment obstacles (qpoint (vertex nodes u)) (qpoint (vertex nodes v))) := by
  intro u v hu hv hne
  rw [source_nodes] at hu hv
  simp only [List.length_cons, List.length_nil] at hu hv
  interval_cases u <;> interval_cases v
  · omega
  · exact pair_0_1
  · exact pair_0_2
  · exact pair_0_3
  · exact pair_0_4
  · exact pair_0_5
  · exact pair_0_6
  · exact pair_0_7
  · exact pair_0_8
  · exact pair_0_9
  · exact pair_1_0
  · omega
  · exact pair_1_2
  · exact pair_1_3
  · exact pair_1_4
  · exact pair_1_5
  · exact pair_1_6
  · exact pair_1_7
  · exact pair_1_8
  · exact pair_1_9
  · exact pair_2_0
  · exact pair_2_1
  · omega
  · exact pair_2_3
  · exact pair_2_4
  · exact pair_2_5
  · exact pair_2_6
  · exact pair_2_7
  · exact pair_2_8
  · exact pair_2_9
  · exact pair_3_0
  · exact pair_3_1
  · exact pair_3_2
  · omega
  · exact pair_3_4
  · exact pair_3_5
  · exact pair_3_6
  · exact pair_3_7
  · exact pair_3_8
  · exact pair_3_9
  · exact pair_4_0
  · exact pair_4_1
  · exact pair_4_2
  · exact pair_4_3
  · omega
  · exact pair_4_5
  · exact pair_4_6
  · exact pair_4_7
  · exact pair_4_8
  · exact pair_4_9
  · exact pair_5_0
  · exact pair_5_1
  · exact pair_5_2
  · exact pair_5_3
  · exact pair_5_4
  · omega
  · exact pair_5_6
  · exact pair_5_7
  · exact pair_5_8
  · exact pair_5_9
  · exact pair_6_0
  · exact pair_6_1
  · exact pair_6_2
  · exact pair_6_3
  · exact pair_6_4
  · exact pair_6_5
  · omega
  · exact pair_6_7
  · exact pair_6_8
  · exact pair_6_9
  · exact pair_7_0
  · exact pair_7_1
  · exact pair_7_2
  · exact pair_7_3
  · exact pair_7_4
  · exact pair_7_5
  · exact pair_7_6
  · omega
  · exact pair_7_8
  · exact pair_7_9
  · exact pair_8_0
  · exact pair_8_1
  · exact pair_8_2
  · exact pair_8_3
  · exact pair_8_4
  · exact pair_8_5
  · exact pair_8_6
  · exact pair_8_7
  · omega
  · exact pair_8_9
  · exact pair_9_0
  · exact pair_9_1
  · exact pair_9_2
  · exact pair_9_3
  · exact pair_9_4
  · exact pair_9_5
  · exact pair_9_6
  · exact pair_9_7
  · exact pair_9_8
  · omega
theorem original_geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment originalObstacles (originalNodes[u]?.getD (0,0)) (originalNodes[v]?.getD (0,0))) := by
  intro u v hu hv hne
  have hu' : u < 10 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hu
  have hv' : v < 10 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hv
  rw [geometric_complete u v hu hv hne,source_obstacle_scaling,
    source_node_scaling u (List.mem_range.mpr hu'),source_node_scaling v (List.mem_range.mpr hv')]
  exact free_segment_scale ((1 : ℚ)/(1 : ℚ)) (by norm_num) _ _ _
theorem original_nodes_length : nodes.length = originalNodes.length := by decide
theorem vertex_scaling : ∀ u, u < originalNodes.length →
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (rationalVertex originalNodes u) := by
  intro u hu
  have hn : u < 10 := by simpa only [originalNodes,List.length_cons,List.length_nil] using hu
  exact source_node_scaling u (List.mem_range.mpr hn)
#print axioms original_geometric_complete
theorem no_cheaper_geometric_walk {other : Int}
    (walk : GeometricWalk obstacles nodes 0 1 other) : (3 : Int) ≤ other := by
  apply geometric_optimal_walk obstacles nodes admitted geometric_complete potential
  · rw [← reconstructed_edges]; exact edge_bounds
  · exact dual_equality
  · exact walk
theorem no_cheaper_original_walk {other : ℚ}
    (walk : RationalGeometricWalk originalObstacles originalNodes 0 1 other) : ((3 : ℚ)/(1 : ℚ)) ≤ other := by
  apply rational_optimal_walk ((1 : ℚ)/(1 : ℚ)) (by norm_num) originalObstacles originalNodes nodes
    original_nodes_length vertex_scaling (best := (3 : Int))
  · norm_num
  · intro c walk
    rw [← source_obstacle_scaling] at walk
    exact no_cheaper_geometric_walk walk
  · exact walk
def sourcePath : List Nat := [0, 1]
theorem source_path_admitted : ∀ e ∈ sourcePath.zip sourcePath.tail,
    e.1 < nodes.length ∧ e.2 < nodes.length ∧ e.1 ≠ e.2 ∧ e ∈ admitted := by decide
theorem source_path_visible : ∀ e ∈ sourcePath.zip sourcePath.tail,
    FreeSegment originalObstacles (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2) := by
  intro e he
  have h := source_path_admitted e he
  exact (original_geometric_complete e.1 e.2 h.1 h.2.1 h.2.2.1).mp h.2.2.2
theorem source_path_cost : ((sourcePath.zip sourcePath.tail).map
    (fun e => qweight (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2))).sum = ((3 : ℚ)/(1 : ℚ)) := by decide +kernel
#print axioms no_cheaper_geometric_walk
#print axioms no_cheaper_original_walk
#print axioms source_path_visible
#print axioms geometric_complete

end PerfectPower.CheckedGraph.Pcff841657f9206f2a85cd07653e6ed85e71f9d97c88c4353ce459ccc12337ed2
