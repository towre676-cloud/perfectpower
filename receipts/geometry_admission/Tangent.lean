import PerfectPower.GeometrySourceTransport
namespace PerfectPower.CheckedGraph.Pba16cde7bdb1f7ae46caa993c713e73e8fe949eeb2c8c95fc5366e3b770982a7
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
-- Source coordinates, not producer-selected vertex indices.
def sourceObstacles : List (List Point) := [[((0 : Int),(0 : Int)), ((2 : Int),(0 : Int)), ((2 : Int),(2 : Int)), ((0 : Int),(2 : Int))]]
def sourceStart : Point := ((-1 : Int),(1 : Int))
def sourceEnd : Point := ((1 : Int),(-1 : Int))
def nodes : List Point := ([sourceStart,sourceEnd] ++ sourceObstacles.flatten).eraseDups
def obstacles : List (List QPoint) := sourceObstacles.map (List.map qpoint)
theorem source_nodes : nodes = [((-1 : Int),(1 : Int)), ((1 : Int),(-1 : Int)), ((0 : Int),(0 : Int)), ((2 : Int),(0 : Int)), ((2 : Int),(2 : Int)), ((0 : Int),(2 : Int))] := by decide
def originalObstacles : List (List QPoint) := [[(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))]]
def originalNodes : List QPoint := [(((-1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))), (((1 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))]
theorem original_source_nodes : originalNodes = ([(((-1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),(((1 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ)))] ++ originalObstacles.flatten).eraseDups := by decide +kernel
theorem source_obstacle_scaling : obstacles = originalObstacles.map (List.map (scalePoint ((1 : ℚ)/(1 : ℚ)))) := by decide +kernel
theorem source_node_scaling : ∀ u ∈ List.range 6,
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (originalNodes[u]?.getD (0,0)) := by decide +kernel
def admitted : List (Nat × Nat) := [(0,1), (0,2), (0,5), (1,0), (1,2), (1,3), (2,0), (2,1), (2,3), (2,5), (3,1), (3,2), (3,4), (4,3), (4,5), (5,0), (5,2), (5,4)]
def edges : List Edge := graph nodes admitted
theorem source_edges : edges.Perm [(0,1,(4 : Int)), (0,2,(2 : Int)), (0,5,(2 : Int)), (1,2,(2 : Int)), (1,3,(2 : Int)), (2,3,(2 : Int)), (2,5,(2 : Int)), (3,4,(2 : Int)), (4,5,(2 : Int)), (1,0,(4 : Int)), (2,0,(2 : Int)), (5,0,(2 : Int)), (2,1,(2 : Int)), (3,1,(2 : Int)), (3,2,(2 : Int)), (5,2,(2 : Int)), (4,3,(2 : Int)), (5,4,(2 : Int))] := by decide
def potentials : List Int := [(0 : Int), (4 : Int), (2 : Int), (4 : Int), (4 : Int), (2 : Int)]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
theorem retained_path : Walk edges 0 1 (4) := by
  show Walk edges 0 1 (4+0)
  exact Walk.cons (edges := edges) (u := 0) (v := 1) (t := 1) (w := (4)) (c := (0)) (by decide) (Walk.nil 1)
theorem dual_equality : (4 : Int) = potential 1 - potential 0 := by decide
theorem no_cheaper_walk {other : Int} (walk : Walk edges 0 1 other) : (4 : Int) ≤ other :=
  optimal_walk edges potential edge_bounds dual_equality walk
#print axioms retained_path
#print axioms no_cheaper_walk
theorem reconstructed_edges : edges = graph nodes admitted := rfl
def cells_0_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 1))) cells_0_1 := by decide +kernel
theorem pair_0_1 : ((0,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_1)
def cells_0_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_0_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 2))) cells_0_2 := by decide +kernel
theorem pair_0_2 : ((0,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 0)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_0_2)
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
def cells_1_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(2 : ℚ))), (((1 : ℚ)/(2 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 0))) cells_1_0 := by decide +kernel
theorem pair_1_0 : ((1,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_0)
def cells_1_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 2))) cells_1_2 := by decide +kernel
theorem pair_1_2 : ((1,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_2)
def cells_1_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_1_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 3))) cells_1_3 := by decide +kernel
theorem pair_1_3 : ((1,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_1_3)
theorem blockage_1_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 4))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_1_4 : ((1,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_1_4)
theorem blockage_1_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 5))).eval ((2 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_1_5 : ((1,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 1)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((2 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_1_5)
def cells_2_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 0))) cells_2_0 := by decide +kernel
theorem pair_2_0 : ((2,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_0)
def cells_2_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 1))) cells_2_1 := by decide +kernel
theorem pair_2_1 : ((2,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_1)
def cells_2_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 3))) cells_2_3 := by decide +kernel
theorem pair_2_3 : ((2,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_3)
theorem blockage_2_4 : (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 4))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_2_4 : ((2,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 4)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_2_4)
def cells_2_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_2_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 5))) cells_2_5 := by decide +kernel
theorem pair_2_5 : ((2,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 2)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_2_5)
theorem blockage_3_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_3_0 : ((3,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_3_0)
def cells_3_1 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_1 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 1))) cells_3_1 := by decide +kernel
theorem pair_3_1 : ((3,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 1)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_1)
def cells_3_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 2))) cells_3_2 := by decide +kernel
theorem pair_3_2 : ((3,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_2)
def cells_3_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_3_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 4))) cells_3_4 := by decide +kernel
theorem pair_3_4 : ((3,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_3_4)
theorem blockage_3_5 : (obstaclesFormula obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 5))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_3_5 : ((3,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 3)) (qpoint (vertex nodes 5)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_3_5)
theorem blockage_4_0 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 0))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_4_0 : ((4,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 0)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_4_0)
theorem blockage_4_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_4_1 : ((4,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_4_1)
theorem blockage_4_2 : (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 2))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_4_2 : ((4,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 2)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_4_2)
def cells_4_3 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_3 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 3))) cells_4_3 := by decide +kernel
theorem pair_4_3 : ((4,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 3)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_3)
def cells_4_5 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_4_5 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 5))) cells_4_5 := by decide +kernel
theorem pair_4_5 : ((4,5) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 4)) (qpoint (vertex nodes 5)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_4_5)
def cells_5_0 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_0 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 0))) cells_5_0 := by decide +kernel
theorem pair_5_0 : ((5,0) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 0)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_0)
theorem blockage_5_1 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 1))).eval ((1 : ℚ)/(3 : ℚ)) = true := by decide +kernel
theorem pair_5_1 : ((5,1) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 1)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(3 : ℚ)) (by norm_num) (by norm_num) blockage_5_1)
def cells_5_2 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_2 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 2))) cells_5_2 := by decide +kernel
theorem pair_5_2 : ((5,2) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 2)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_2)
theorem blockage_5_3 : (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 3))).eval ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem pair_5_3 : ((5,3) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 3)) :=
  iff_of_false (by decide) (blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) blockage_5_3)
def cells_5_4 : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission_5_4 : accepted (obstaclesFormula obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 4))) cells_5_4 := by decide +kernel
theorem pair_5_4 : ((5,4) ∈ admitted) ↔ FreeSegment obstacles (qpoint (vertex nodes 5)) (qpoint (vertex nodes 4)) :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_5_4)
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
  · exact pair_1_0
  · omega
  · exact pair_1_2
  · exact pair_1_3
  · exact pair_1_4
  · exact pair_1_5
  · exact pair_2_0
  · exact pair_2_1
  · omega
  · exact pair_2_3
  · exact pair_2_4
  · exact pair_2_5
  · exact pair_3_0
  · exact pair_3_1
  · exact pair_3_2
  · omega
  · exact pair_3_4
  · exact pair_3_5
  · exact pair_4_0
  · exact pair_4_1
  · exact pair_4_2
  · exact pair_4_3
  · omega
  · exact pair_4_5
  · exact pair_5_0
  · exact pair_5_1
  · exact pair_5_2
  · exact pair_5_3
  · exact pair_5_4
  · omega
theorem original_geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment originalObstacles (originalNodes[u]?.getD (0,0)) (originalNodes[v]?.getD (0,0))) := by
  intro u v hu hv hne
  have hu' : u < 6 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hu
  have hv' : v < 6 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hv
  rw [geometric_complete u v hu hv hne,source_obstacle_scaling,
    source_node_scaling u (List.mem_range.mpr hu'),source_node_scaling v (List.mem_range.mpr hv')]
  exact free_segment_scale ((1 : ℚ)/(1 : ℚ)) (by norm_num) _ _ _
theorem original_nodes_length : nodes.length = originalNodes.length := by decide
theorem vertex_scaling : ∀ u, u < originalNodes.length →
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (rationalVertex originalNodes u) := by
  intro u hu
  have hn : u < 6 := by simpa only [originalNodes,List.length_cons,List.length_nil] using hu
  exact source_node_scaling u (List.mem_range.mpr hn)
#print axioms original_geometric_complete
theorem no_cheaper_geometric_walk {other : Int}
    (walk : GeometricWalk obstacles nodes 0 1 other) : (4 : Int) ≤ other := by
  apply geometric_optimal_walk obstacles nodes admitted geometric_complete potential
  · rw [← reconstructed_edges]; exact edge_bounds
  · exact dual_equality
  · exact walk
theorem no_cheaper_original_walk {other : ℚ}
    (walk : RationalGeometricWalk originalObstacles originalNodes 0 1 other) : ((4 : ℚ)/(1 : ℚ)) ≤ other := by
  apply rational_optimal_walk ((1 : ℚ)/(1 : ℚ)) (by norm_num) originalObstacles originalNodes nodes
    original_nodes_length vertex_scaling (best := (4 : Int))
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
    (fun e => qweight (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2))).sum = ((4 : ℚ)/(1 : ℚ)) := by decide +kernel
#print axioms no_cheaper_geometric_walk
#print axioms no_cheaper_original_walk
#print axioms source_path_visible
#print axioms geometric_complete

end PerfectPower.CheckedGraph.Pba16cde7bdb1f7ae46caa993c713e73e8fe949eeb2c8c95fc5366e3b770982a7
