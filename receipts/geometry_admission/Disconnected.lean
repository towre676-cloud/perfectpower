import PerfectPower.GeometrySourceTransport
namespace PerfectPower.CheckedGraph.Pbaf2b59f9b254c2c54cd880d725f9f0fd0b06dd5d57f916056084ac79fd96ffc
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
-- Source coordinates, not producer-selected vertex indices.
def sourceObstacles : List (List Point) := [[((-3 : Int),(1 : Int)), ((3 : Int),(1 : Int)), ((3 : Int),(3 : Int)), ((-3 : Int),(3 : Int))], [((-3 : Int),(-3 : Int)), ((3 : Int),(-3 : Int)), ((3 : Int),(-1 : Int)), ((-3 : Int),(-1 : Int))], [((-3 : Int),(-3 : Int)), ((-1 : Int),(-3 : Int)), ((-1 : Int),(3 : Int)), ((-3 : Int),(3 : Int))], [((1 : Int),(-3 : Int)), ((3 : Int),(-3 : Int)), ((3 : Int),(3 : Int)), ((1 : Int),(3 : Int))]]
def sourceStart : Point := ((0 : Int),(0 : Int))
def sourceEnd : Point := ((5 : Int),(0 : Int))
def nodes : List Point := ([sourceStart,sourceEnd] ++ sourceObstacles.flatten).eraseDups
def obstacles : List (List QPoint) := sourceObstacles.map (List.map qpoint)
theorem source_nodes : nodes = [((0 : Int),(0 : Int)), ((5 : Int),(0 : Int)), ((-3 : Int),(1 : Int)), ((3 : Int),(1 : Int)), ((3 : Int),(3 : Int)), ((-3 : Int),(3 : Int)), ((-3 : Int),(-3 : Int)), ((3 : Int),(-3 : Int)), ((3 : Int),(-1 : Int)), ((-3 : Int),(-1 : Int)), ((-1 : Int),(-3 : Int)), ((-1 : Int),(3 : Int)), ((1 : Int),(-3 : Int)), ((1 : Int),(3 : Int))] := by decide
def originalObstacles : List (List QPoint) := [[(((-3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))], [(((-3 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ)))], [(((-3 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((-1 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((-1 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))], [(((1 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((1 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))]]
def originalNodes : List QPoint := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((5 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))), (((-3 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))), (((-1 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((-1 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((1 : ℚ)/(1 : ℚ)),((-3 : ℚ)/(1 : ℚ))), (((1 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))]
theorem original_source_nodes : originalNodes = ([(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),(((5 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))] ++ originalObstacles.flatten).eraseDups := by decide +kernel
theorem source_obstacle_scaling : obstacles = originalObstacles.map (List.map (scalePoint ((1 : ℚ)/(1 : ℚ)))) := by decide +kernel
theorem source_node_scaling : ∀ u ∈ List.range 14,
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (originalNodes[u]?.getD (0,0)) := by decide +kernel
def admitted : List (Nat × Nat) := [(1,3), (1,4), (1,7), (1,8), (2,5), (2,6), (2,9), (3,1), (3,4), (3,7), (3,8), (4,1), (4,3), (4,5), (4,7), (4,8), (4,11), (4,13), (5,2), (5,4), (5,6), (5,9), (5,11), (5,13), (6,2), (6,5), (6,7), (6,9), (6,10), (6,12), (7,1), (7,3), (7,4), (7,6), (7,8), (7,10), (7,12), (8,1), (8,3), (8,4), (8,7), (9,2), (9,5), (9,6), (10,6), (10,7), (10,12), (11,4), (11,5), (11,13), (12,6), (12,7), (12,10), (13,4), (13,5), (13,11)]
def edges : List Edge := graph nodes admitted
theorem source_edges : edges.Perm [(1,3,(3 : Int)), (1,4,(5 : Int)), (1,7,(5 : Int)), (1,8,(3 : Int)), (2,5,(2 : Int)), (2,6,(4 : Int)), (2,9,(2 : Int)), (3,4,(2 : Int)), (3,7,(4 : Int)), (3,8,(2 : Int)), (4,5,(6 : Int)), (4,7,(6 : Int)), (4,8,(4 : Int)), (4,11,(4 : Int)), (4,13,(2 : Int)), (5,6,(6 : Int)), (5,9,(4 : Int)), (5,11,(2 : Int)), (5,13,(4 : Int)), (6,7,(6 : Int)), (6,9,(2 : Int)), (6,10,(2 : Int)), (6,12,(4 : Int)), (7,8,(2 : Int)), (7,10,(4 : Int)), (7,12,(2 : Int)), (10,12,(2 : Int)), (11,13,(2 : Int)), (3,1,(3 : Int)), (4,1,(5 : Int)), (7,1,(5 : Int)), (8,1,(3 : Int)), (5,2,(2 : Int)), (6,2,(4 : Int)), (9,2,(2 : Int)), (4,3,(2 : Int)), (7,3,(4 : Int)), (8,3,(2 : Int)), (5,4,(6 : Int)), (7,4,(6 : Int)), (8,4,(4 : Int)), (11,4,(4 : Int)), (13,4,(2 : Int)), (6,5,(6 : Int)), (9,5,(4 : Int)), (11,5,(2 : Int)), (13,5,(4 : Int)), (7,6,(6 : Int)), (9,6,(2 : Int)), (10,6,(2 : Int)), (12,6,(4 : Int)), (8,7,(2 : Int)), (10,7,(4 : Int)), (12,7,(2 : Int)), (12,10,(2 : Int)), (13,11,(2 : Int))] := by decide
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
theorem reconstructed_edges : edges = graph nodes admitted := rfl
theorem blockage_0_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 1))).eval ((2 : ℚ)/(5 : ℚ)) = true := by decide +kernel
theorem pair_0_1 : ((0,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(5 : ℚ)) (by norm_num) (by norm_num) blockage_0_1)
theorem blockage_0_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 2))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_2 : ((0,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_2)
theorem blockage_0_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 3))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_3 : ((0,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_3)
theorem blockage_0_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 4))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_4 : ((0,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_4)
theorem blockage_0_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 5))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_5 : ((0,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_5)
theorem blockage_0_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 6))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_6 : ((0,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_6)
theorem blockage_0_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 7))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_7 : ((0,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_7)
theorem blockage_0_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 8))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_8 : ((0,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_8)
theorem blockage_0_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 9))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_9 : ((0,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_9)
theorem blockage_0_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 10))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_10 : ((0,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_10)
theorem blockage_0_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 11))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_11 : ((0,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_11)
theorem blockage_0_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 12))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_12 : ((0,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_12)
theorem blockage_0_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 13))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_0_13 : ((0,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_0_13)
theorem blockage_1_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 0))).eval ((3 : ℚ)/(5 : ℚ)) = true := by decide +kernel
theorem pair_1_0 : ((1,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(5 : ℚ)) (by norm_num) (by norm_num) blockage_1_0)
theorem blockage_1_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 2))).eval ((3 : ℚ)/(8 : ℚ)) = true := by decide +kernel
theorem pair_1_2 : ((1,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(8 : ℚ)) (by norm_num) (by norm_num) blockage_1_2)
def cells_1_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 3))) cells_1_3 := by decide +kernel
theorem pair_1_3 : ((1,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_3)
def cells_1_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 4))) cells_1_4 := by decide +kernel
theorem pair_1_4 : ((1,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_4)
theorem blockage_1_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 5))).eval ((7 : ℚ)/(24 : ℚ)) = true := by decide +kernel
theorem pair_1_5 : ((1,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((7 : ℚ)/(24 : ℚ)) (by norm_num) (by norm_num) blockage_1_5)
theorem blockage_1_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 6))).eval ((7 : ℚ)/(24 : ℚ)) = true := by decide +kernel
theorem pair_1_6 : ((1,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((7 : ℚ)/(24 : ℚ)) (by norm_num) (by norm_num) blockage_1_6)
def cells_1_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 7))) cells_1_7 := by decide +kernel
theorem pair_1_7 : ((1,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_7)
def cells_1_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 8))) cells_1_8 := by decide +kernel
theorem pair_1_8 : ((1,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_8)
theorem blockage_1_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 9))).eval ((3 : ℚ)/(8 : ℚ)) = true := by decide +kernel
theorem pair_1_9 : ((1,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(8 : ℚ)) (by norm_num) (by norm_num) blockage_1_9)
theorem blockage_1_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_1_10 : ((1,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_1_10)
theorem blockage_1_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_1_11 : ((1,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_1_11)
theorem blockage_1_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 12))).eval ((3 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_1_12 : ((1,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_1_12)
theorem blockage_1_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 13))).eval ((3 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_1_13 : ((1,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((3 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_1_13)
theorem blockage_2_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_2_0 : ((2,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_2_0)
theorem blockage_2_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(8 : ℚ)) = true := by decide +kernel
theorem pair_2_1 : ((2,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(8 : ℚ)) (by norm_num) (by norm_num) blockage_2_1)
theorem blockage_2_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_2_3 : ((2,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_2_3)
theorem blockage_2_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_2_4 : ((2,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_2_4)
def cells_2_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 5))) cells_2_5 := by decide +kernel
theorem pair_2_5 : ((2,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_5)
def cells_2_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 6))) cells_2_6 := by decide +kernel
theorem pair_2_6 : ((2,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_6)
theorem blockage_2_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_2_7 : ((2,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_2_7)
theorem blockage_2_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_2_8 : ((2,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_2_8)
def cells_2_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 9))) cells_2_9 := by decide +kernel
theorem pair_2_9 : ((2,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_9)
theorem blockage_2_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_2_10 : ((2,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_2_10)
theorem blockage_2_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_2_11 : ((2,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_2_11)
theorem blockage_2_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_2_12 : ((2,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_2_12)
theorem blockage_2_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_2_13 : ((2,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_2_13)
theorem blockage_3_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_3_0 : ((3,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_3_0)
def cells_3_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 1))) cells_3_1 := by decide +kernel
theorem pair_3_1 : ((3,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_1)
theorem blockage_3_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_3_2 : ((3,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_3_2)
def cells_3_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 4))) cells_3_4 := by decide +kernel
theorem pair_3_4 : ((3,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_4)
theorem blockage_3_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_3_5 : ((3,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_3_5)
theorem blockage_3_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_3_6 : ((3,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_3_6)
def cells_3_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 7))) cells_3_7 := by decide +kernel
theorem pair_3_7 : ((3,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_7)
def cells_3_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 8))) cells_3_8 := by decide +kernel
theorem pair_3_8 : ((3,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_8)
theorem blockage_3_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_3_9 : ((3,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_3_9)
theorem blockage_3_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_3_10 : ((3,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_3_10)
theorem blockage_3_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_3_11 : ((3,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_3_11)
theorem blockage_3_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_3_12 : ((3,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_3_12)
theorem blockage_3_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_3_13 : ((3,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_3_13)
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
def cells_4_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 3))) cells_4_3 := by decide +kernel
theorem pair_4_3 : ((4,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_3)
def cells_4_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 5))) cells_4_5 := by decide +kernel
theorem pair_4_5 : ((4,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_5)
theorem blockage_4_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_4_6 : ((4,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_4_6)
def cells_4_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 7))) cells_4_7 := by decide +kernel
theorem pair_4_7 : ((4,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_7)
def cells_4_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 8))) cells_4_8 := by decide +kernel
theorem pair_4_8 : ((4,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_8)
theorem blockage_4_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_4_9 : ((4,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_4_9)
theorem blockage_4_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_4_10 : ((4,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_4_10)
def cells_4_11 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_11 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 11))) cells_4_11 := by decide +kernel
theorem pair_4_11 : ((4,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 11)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_11)
theorem blockage_4_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_4_12 : ((4,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_4_12)
def cells_4_13 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_13 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 13))) cells_4_13 := by decide +kernel
theorem pair_4_13 : ((4,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 13)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_13)
theorem blockage_5_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_5_0 : ((5,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_5_0)
theorem blockage_5_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(8 : ℚ)) = true := by decide +kernel
theorem pair_5_1 : ((5,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(8 : ℚ)) (by norm_num) (by norm_num) blockage_5_1)
def cells_5_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 2))) cells_5_2 := by decide +kernel
theorem pair_5_2 : ((5,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_2)
theorem blockage_5_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_5_3 : ((5,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_5_3)
def cells_5_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 4))) cells_5_4 := by decide +kernel
theorem pair_5_4 : ((5,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_4)
def cells_5_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 6))) cells_5_6 := by decide +kernel
theorem pair_5_6 : ((5,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_6)
theorem blockage_5_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_5_7 : ((5,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_5_7)
theorem blockage_5_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_5_8 : ((5,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_5_8)
def cells_5_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 9))) cells_5_9 := by decide +kernel
theorem pair_5_9 : ((5,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_9)
theorem blockage_5_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_5_10 : ((5,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_5_10)
def cells_5_11 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_11 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 11))) cells_5_11 := by decide +kernel
theorem pair_5_11 : ((5,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 11)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_11)
theorem blockage_5_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_5_12 : ((5,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_5_12)
def cells_5_13 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_13 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 13))) cells_5_13 := by decide +kernel
theorem pair_5_13 : ((5,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 13)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_13)
theorem blockage_6_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_6_0 : ((6,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_6_0)
theorem blockage_6_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(8 : ℚ)) = true := by decide +kernel
theorem pair_6_1 : ((6,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(8 : ℚ)) (by norm_num) (by norm_num) blockage_6_1)
def cells_6_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 2))) cells_6_2 := by decide +kernel
theorem pair_6_2 : ((6,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_2)
theorem blockage_6_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_6_3 : ((6,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_6_3)
theorem blockage_6_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_6_4 : ((6,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_6_4)
def cells_6_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 5))) cells_6_5 := by decide +kernel
theorem pair_6_5 : ((6,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_5)
def cells_6_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 7))) cells_6_7 := by decide +kernel
theorem pair_6_7 : ((6,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_7)
theorem blockage_6_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_6_8 : ((6,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_6_8)
def cells_6_9 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_9 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 9))) cells_6_9 := by decide +kernel
theorem pair_6_9 : ((6,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 9)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_9)
def cells_6_10 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_10 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 10))) cells_6_10 := by decide +kernel
theorem pair_6_10 : ((6,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 10)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_10)
theorem blockage_6_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_6_11 : ((6,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_6_11)
def cells_6_12 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_6_12 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 12))) cells_6_12 := by decide +kernel
theorem pair_6_12 : ((6,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 12)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_6_12)
theorem blockage_6_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_6_13 : ((6,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 6)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_6_13)
theorem blockage_7_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_7_0 : ((7,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_7_0)
def cells_7_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 1))) cells_7_1 := by decide +kernel
theorem pair_7_1 : ((7,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_1)
theorem blockage_7_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_7_2 : ((7,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_7_2)
def cells_7_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 3))) cells_7_3 := by decide +kernel
theorem pair_7_3 : ((7,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_3)
def cells_7_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 4))) cells_7_4 := by decide +kernel
theorem pair_7_4 : ((7,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_4)
theorem blockage_7_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_7_5 : ((7,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_7_5)
def cells_7_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(3 : ℚ))), (((1 : ℚ)/(3 : ℚ)),((2 : ℚ)/(3 : ℚ))), (((2 : ℚ)/(3 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 6))) cells_7_6 := by decide +kernel
theorem pair_7_6 : ((7,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_6)
def cells_7_8 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_8 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 8))) cells_7_8 := by decide +kernel
theorem pair_7_8 : ((7,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 8)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_8)
theorem blockage_7_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_7_9 : ((7,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_7_9)
def cells_7_10 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_10 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 10))) cells_7_10 := by decide +kernel
theorem pair_7_10 : ((7,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 10)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_10)
theorem blockage_7_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_7_11 : ((7,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_7_11)
def cells_7_12 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_7_12 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 12))) cells_7_12 := by decide +kernel
theorem pair_7_12 : ((7,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 12)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_7_12)
theorem blockage_7_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_7_13 : ((7,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 7)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_7_13)
theorem blockage_8_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_8_0 : ((8,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_8_0)
def cells_8_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 1))) cells_8_1 := by decide +kernel
theorem pair_8_1 : ((8,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_1)
theorem blockage_8_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_8_2 : ((8,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_8_2)
def cells_8_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 3))) cells_8_3 := by decide +kernel
theorem pair_8_3 : ((8,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_3)
def cells_8_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 4))) cells_8_4 := by decide +kernel
theorem pair_8_4 : ((8,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_4)
theorem blockage_8_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_8_5 : ((8,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_8_5)
theorem blockage_8_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_8_6 : ((8,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_8_6)
def cells_8_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_8_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 7))) cells_8_7 := by decide +kernel
theorem pair_8_7 : ((8,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_8_7)
theorem blockage_8_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_8_9 : ((8,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_8_9)
theorem blockage_8_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_8_10 : ((8,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_8_10)
theorem blockage_8_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_8_11 : ((8,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_8_11)
theorem blockage_8_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_8_12 : ((8,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_8_12)
theorem blockage_8_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_8_13 : ((8,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 8)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_8_13)
theorem blockage_9_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_9_0 : ((9,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_9_0)
theorem blockage_9_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(8 : ℚ)) = true := by decide +kernel
theorem pair_9_1 : ((9,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(8 : ℚ)) (by norm_num) (by norm_num) blockage_9_1)
def cells_9_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 2))) cells_9_2 := by decide +kernel
theorem pair_9_2 : ((9,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_2)
theorem blockage_9_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_9_3 : ((9,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_9_3)
theorem blockage_9_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_9_4 : ((9,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_9_4)
def cells_9_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 5))) cells_9_5 := by decide +kernel
theorem pair_9_5 : ((9,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_5)
def cells_9_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_9_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 6))) cells_9_6 := by decide +kernel
theorem pair_9_6 : ((9,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_9_6)
theorem blockage_9_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_9_7 : ((9,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_9_7)
theorem blockage_9_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_9_8 : ((9,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_9_8)
theorem blockage_9_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_9_10 : ((9,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_9_10)
theorem blockage_9_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_9_11 : ((9,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_9_11)
theorem blockage_9_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_9_12 : ((9,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_9_12)
theorem blockage_9_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_9_13 : ((9,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 9)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_9_13)
theorem blockage_10_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_10_0 : ((10,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_10_0)
theorem blockage_10_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_10_1 : ((10,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_10_1)
theorem blockage_10_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_10_2 : ((10,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_10_2)
theorem blockage_10_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_10_3 : ((10,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_10_3)
theorem blockage_10_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_10_4 : ((10,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_10_4)
theorem blockage_10_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_10_5 : ((10,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_10_5)
def cells_10_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_10_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 6))) cells_10_6 := by decide +kernel
theorem pair_10_6 : ((10,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_10_6)
def cells_10_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_10_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 7))) cells_10_7 := by decide +kernel
theorem pair_10_7 : ((10,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_10_7)
theorem blockage_10_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_10_8 : ((10,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_10_8)
theorem blockage_10_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_10_9 : ((10,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_10_9)
theorem blockage_10_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_10_11 : ((10,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_10_11)
def cells_10_12 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_10_12 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 12))) cells_10_12 := by decide +kernel
theorem pair_10_12 : ((10,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 12)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_10_12)
theorem blockage_10_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_10_13 : ((10,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 10)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_10_13)
theorem blockage_11_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_11_0 : ((11,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_11_0)
theorem blockage_11_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_11_1 : ((11,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_11_1)
theorem blockage_11_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_11_2 : ((11,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_11_2)
theorem blockage_11_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_11_3 : ((11,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_11_3)
def cells_11_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_11_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 4))) cells_11_4 := by decide +kernel
theorem pair_11_4 : ((11,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_11_4)
def cells_11_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_11_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 5))) cells_11_5 := by decide +kernel
theorem pair_11_5 : ((11,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_11_5)
theorem blockage_11_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_11_6 : ((11,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_11_6)
theorem blockage_11_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_11_7 : ((11,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_11_7)
theorem blockage_11_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_11_8 : ((11,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_11_8)
theorem blockage_11_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_11_9 : ((11,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_11_9)
theorem blockage_11_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_11_10 : ((11,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_11_10)
theorem blockage_11_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_11_12 : ((11,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_11_12)
def cells_11_13 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_11_13 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 13))) cells_11_13 := by decide +kernel
theorem pair_11_13 : ((11,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 11)) (qpoint (vertex nodes 13)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_11_13)
theorem blockage_12_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_12_0 : ((12,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_12_0)
theorem blockage_12_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_12_1 : ((12,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_12_1)
theorem blockage_12_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_12_2 : ((12,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_12_2)
theorem blockage_12_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_12_3 : ((12,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_12_3)
theorem blockage_12_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_12_4 : ((12,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_12_4)
theorem blockage_12_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_12_5 : ((12,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_12_5)
def cells_12_6 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_12_6 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 6))) cells_12_6 := by decide +kernel
theorem pair_12_6 : ((12,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 6)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_12_6)
def cells_12_7 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_12_7 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 7))) cells_12_7 := by decide +kernel
theorem pair_12_7 : ((12,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 7)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_12_7)
theorem blockage_12_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_12_8 : ((12,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_12_8)
theorem blockage_12_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_12_9 : ((12,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_12_9)
def cells_12_10 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_12_10 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 10))) cells_12_10 := by decide +kernel
theorem pair_12_10 : ((12,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 10)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_12_10)
theorem blockage_12_11 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 11))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_12_11 : ((12,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 11)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_12_11)
theorem blockage_12_13 : (obstaclesFormula obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 13))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_12_13 : ((12,13) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 12)) (qpoint (vertex nodes 13)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_12_13)
theorem blockage_13_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_13_0 : ((13,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_13_0)
theorem blockage_13_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_13_1 : ((13,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_13_1)
theorem blockage_13_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_13_2 : ((13,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_13_2)
theorem blockage_13_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_13_3 : ((13,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_13_3)
def cells_13_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_13_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 4))) cells_13_4 := by decide +kernel
theorem pair_13_4 : ((13,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_13_4)
def cells_13_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_13_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 5))) cells_13_5 := by decide +kernel
theorem pair_13_5 : ((13,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_13_5)
theorem blockage_13_6 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 6))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_13_6 : ((13,6) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 6)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_13_6)
theorem blockage_13_7 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 7))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_13_7 : ((13,7) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 7)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_13_7)
theorem blockage_13_8 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 8))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_13_8 : ((13,8) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 8)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_13_8)
theorem blockage_13_9 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 9))).eval ((1 : ℚ)/(4 : ℚ)) = true := by decide +kernel
theorem pair_13_9 : ((13,9) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 9)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(4 : ℚ)) (by norm_num) (by norm_num) blockage_13_9)
theorem blockage_13_10 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 10))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_13_10 : ((13,10) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 10)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_13_10)
def cells_13_11 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_13_11 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 11))) cells_13_11 := by decide +kernel
theorem pair_13_11 : ((13,11) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 11)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_13_11)
theorem blockage_13_12 : (obstaclesFormula obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 12))).eval ((1 : ℚ)/(6 : ℚ)) = true := by decide +kernel
theorem pair_13_12 : ((13,12) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 13)) (qpoint (vertex nodes 12)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(6 : ℚ)) (by norm_num) (by norm_num) blockage_13_12)
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
  · exact pair_0_10
  · exact pair_0_11
  · exact pair_0_12
  · exact pair_0_13
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
  · exact pair_1_10
  · exact pair_1_11
  · exact pair_1_12
  · exact pair_1_13
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
  · exact pair_2_10
  · exact pair_2_11
  · exact pair_2_12
  · exact pair_2_13
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
  · exact pair_3_10
  · exact pair_3_11
  · exact pair_3_12
  · exact pair_3_13
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
  · exact pair_4_10
  · exact pair_4_11
  · exact pair_4_12
  · exact pair_4_13
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
  · exact pair_5_10
  · exact pair_5_11
  · exact pair_5_12
  · exact pair_5_13
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
  · exact pair_6_10
  · exact pair_6_11
  · exact pair_6_12
  · exact pair_6_13
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
  · exact pair_7_10
  · exact pair_7_11
  · exact pair_7_12
  · exact pair_7_13
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
  · exact pair_8_10
  · exact pair_8_11
  · exact pair_8_12
  · exact pair_8_13
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
  · exact pair_9_10
  · exact pair_9_11
  · exact pair_9_12
  · exact pair_9_13
  · exact pair_10_0
  · exact pair_10_1
  · exact pair_10_2
  · exact pair_10_3
  · exact pair_10_4
  · exact pair_10_5
  · exact pair_10_6
  · exact pair_10_7
  · exact pair_10_8
  · exact pair_10_9
  · omega
  · exact pair_10_11
  · exact pair_10_12
  · exact pair_10_13
  · exact pair_11_0
  · exact pair_11_1
  · exact pair_11_2
  · exact pair_11_3
  · exact pair_11_4
  · exact pair_11_5
  · exact pair_11_6
  · exact pair_11_7
  · exact pair_11_8
  · exact pair_11_9
  · exact pair_11_10
  · omega
  · exact pair_11_12
  · exact pair_11_13
  · exact pair_12_0
  · exact pair_12_1
  · exact pair_12_2
  · exact pair_12_3
  · exact pair_12_4
  · exact pair_12_5
  · exact pair_12_6
  · exact pair_12_7
  · exact pair_12_8
  · exact pair_12_9
  · exact pair_12_10
  · exact pair_12_11
  · omega
  · exact pair_12_13
  · exact pair_13_0
  · exact pair_13_1
  · exact pair_13_2
  · exact pair_13_3
  · exact pair_13_4
  · exact pair_13_5
  · exact pair_13_6
  · exact pair_13_7
  · exact pair_13_8
  · exact pair_13_9
  · exact pair_13_10
  · exact pair_13_11
  · exact pair_13_12
  · omega
theorem original_geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment originalObstacles (originalNodes[u]?.getD (0,0)) (originalNodes[v]?.getD (0,0))) := by
  intro u v hu hv hne
  have hu' : u < 14 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hu
  have hv' : v < 14 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hv
  rw [geometric_complete u v hu hv hne,source_obstacle_scaling,
    source_node_scaling u (List.mem_range.mpr hu'),source_node_scaling v (List.mem_range.mpr hv')]
  exact free_segment_scale ((1 : ℚ)/(1 : ℚ)) (by norm_num) _ _ _
theorem original_nodes_length : nodes.length = originalNodes.length := by decide
theorem vertex_scaling : ∀ u, u < originalNodes.length →
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (rationalVertex originalNodes u) := by
  intro u hu
  have hn : u < 14 := by simpa only [originalNodes,List.length_cons,List.length_nil] using hu
  exact source_node_scaling u (List.mem_range.mpr hn)
#print axioms original_geometric_complete
theorem no_geometric_route (c : Int) : ¬GeometricWalk obstacles nodes 0 1 c := by
  intro walk
  have hw := geometric_walk_to_graph obstacles nodes admitted geometric_complete walk
  rw [← reconstructed_edges] at hw
  exact no_route c hw
theorem no_original_route (c : ℚ) : ¬RationalGeometricWalk originalObstacles originalNodes 0 1 c := by
  intro walk
  obtain ⟨scaled,hw,_⟩ := rational_walk_scaled ((1 : ℚ)/(1 : ℚ)) (by norm_num) originalObstacles originalNodes nodes original_nodes_length vertex_scaling walk
  rw [← source_obstacle_scaling] at hw
  exact no_geometric_route scaled hw
#print axioms no_geometric_route
#print axioms no_original_route
#print axioms geometric_complete

end PerfectPower.CheckedGraph.Pbaf2b59f9b254c2c54cd880d725f9f0fd0b06dd5d57f916056084ac79fd96ffc
