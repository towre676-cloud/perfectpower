import PerfectPower.GeometrySourceTransport
namespace PerfectPower.CheckedGraph.P34271842c53b8da39e1ed20ebf6abdd165770f5943e73d175e262107eaedda1e
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
-- Source coordinates, not producer-selected vertex indices.
def sourceObstacles : List (List Point) := []
def sourceStart : Point := ((0 : Int),(0 : Int))
def sourceEnd : Point := ((0 : Int),(0 : Int))
def nodes : List Point := ([sourceStart,sourceEnd] ++ sourceObstacles.flatten).eraseDups
def obstacles : List (List QPoint) := sourceObstacles.map (List.map qpoint)
theorem source_nodes : nodes = [((0 : Int),(0 : Int))] := by decide
def originalObstacles : List (List QPoint) := []
def originalNodes : List QPoint := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))]
theorem original_source_nodes : originalNodes = ([(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))] ++ originalObstacles.flatten).eraseDups := by decide +kernel
theorem source_obstacle_scaling : obstacles = originalObstacles.map (List.map (scalePoint ((1 : ℚ)/(1 : ℚ)))) := by decide +kernel
theorem source_node_scaling : ∀ u ∈ List.range 1,
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (originalNodes[u]?.getD (0,0)) := by decide +kernel
def admitted : List (Nat × Nat) := []
def edges : List Edge := graph nodes admitted
theorem source_edges : edges.Perm [] := by decide
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
theorem reconstructed_edges : edges = graph nodes admitted := rfl
theorem geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment obstacles (qpoint (vertex nodes u)) (qpoint (vertex nodes v))) := by
  intro u v hu hv hne
  rw [source_nodes] at hu hv
  simp only [List.length_cons, List.length_nil] at hu hv
  interval_cases u <;> interval_cases v
  · omega
theorem original_geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment originalObstacles (originalNodes[u]?.getD (0,0)) (originalNodes[v]?.getD (0,0))) := by
  intro u v hu hv hne
  have hu' : u < 1 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hu
  have hv' : v < 1 := by simpa only [source_nodes,List.length_cons,List.length_nil] using hv
  rw [geometric_complete u v hu hv hne,source_obstacle_scaling,
    source_node_scaling u (List.mem_range.mpr hu'),source_node_scaling v (List.mem_range.mpr hv')]
  exact free_segment_scale ((1 : ℚ)/(1 : ℚ)) (by norm_num) _ _ _
theorem original_nodes_length : nodes.length = originalNodes.length := by decide
theorem vertex_scaling : ∀ u, u < originalNodes.length →
    qpoint (vertex nodes u) = scalePoint ((1 : ℚ)/(1 : ℚ)) (rationalVertex originalNodes u) := by
  intro u hu
  have hn : u < 1 := by simpa only [originalNodes,List.length_cons,List.length_nil] using hu
  exact source_node_scaling u (List.mem_range.mpr hn)
#print axioms original_geometric_complete
theorem no_cheaper_geometric_walk {other : Int}
    (walk : GeometricWalk obstacles nodes 0 0 other) : (0 : Int) ≤ other := by
  apply geometric_optimal_walk obstacles nodes admitted geometric_complete potential
  · rw [← reconstructed_edges]; exact edge_bounds
  · exact dual_equality
  · exact walk
theorem no_cheaper_original_walk {other : ℚ}
    (walk : RationalGeometricWalk originalObstacles originalNodes 0 0 other) : ((0 : ℚ)/(1 : ℚ)) ≤ other := by
  apply rational_optimal_walk ((1 : ℚ)/(1 : ℚ)) (by norm_num) originalObstacles originalNodes nodes
    original_nodes_length vertex_scaling (best := (0 : Int))
  · norm_num
  · intro c walk
    rw [← source_obstacle_scaling] at walk
    exact no_cheaper_geometric_walk walk
  · exact walk
def sourcePath : List Nat := [0]
theorem source_path_admitted : ∀ e ∈ sourcePath.zip sourcePath.tail,
    e.1 < nodes.length ∧ e.2 < nodes.length ∧ e.1 ≠ e.2 ∧ e ∈ admitted := by decide
theorem source_path_visible : ∀ e ∈ sourcePath.zip sourcePath.tail,
    FreeSegment originalObstacles (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2) := by
  intro e he
  have h := source_path_admitted e he
  exact (original_geometric_complete e.1 e.2 h.1 h.2.1 h.2.2.1).mp h.2.2.2
theorem source_path_cost : ((sourcePath.zip sourcePath.tail).map
    (fun e => qweight (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2))).sum = ((0 : ℚ)/(1 : ℚ)) := by decide +kernel
#print axioms no_cheaper_geometric_walk
#print axioms no_cheaper_original_walk
#print axioms source_path_visible
#print axioms geometric_complete

end PerfectPower.CheckedGraph.P34271842c53b8da39e1ed20ebf6abdd165770f5943e73d175e262107eaedda1e
