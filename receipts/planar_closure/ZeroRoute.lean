import PerfectPower.RealVisibility
namespace PerfectPower.CheckedGraph.P34271842c53b8da39e1ed20ebf6abdd165770f5943e73d175e262107eaedda1e
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<(1) := by decide
open PerfectPower.GeometryAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
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

open PerfectPower.PlanarCertificates
def real_source_formula : PerfectPower.PlanarCertificates.Formula := PerfectPower.RealVisibility.segmentFormula originalObstacles (rationalVertex originalNodes 0) (rationalVertex originalNodes 0)
def real_source_context_0 : Assignment := []
def real_source_context_2 : Assignment := ((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),-1)::real_source_context_0
def real_source_context_3 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),-1)::real_source_context_2
def real_source_tree_3 : Tree := (.impossible [(((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))),true),((1 : ℚ)/(1 : ℚ))),(((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),true),((1 : ℚ)/(1 : ℚ)))])
theorem real_source_checked_3 : checked real_source_formula real_source_context_3 real_source_tree_3 := by decide +kernel
def real_source_context_4 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),0)::real_source_context_2
def real_source_tree_4 : Tree := (.impossible [(((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))),false),((1 : ℚ)/(1 : ℚ))),(((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),true),((1 : ℚ)/(1 : ℚ)))])
theorem real_source_checked_4 : checked real_source_formula real_source_context_4 real_source_tree_4 := by decide +kernel
def real_source_context_5 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),1)::real_source_context_2
def real_source_tree_5 : Tree := .leaf
theorem real_source_checked_5 : checked real_source_formula real_source_context_5 real_source_tree_5 := by decide +kernel
def real_source_tree_2 : Tree := .split (((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) real_source_tree_3 real_source_tree_4 real_source_tree_5
theorem real_source_checked_2 : checked real_source_formula real_source_context_2 real_source_tree_2 := checked_split real_source_formula real_source_context_2 (((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) real_source_tree_3 real_source_tree_4 real_source_tree_5 real_source_checked_3 real_source_checked_4 real_source_checked_5
def real_source_context_6 : Assignment := ((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),0)::real_source_context_0
def real_source_context_7 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),-1)::real_source_context_6
def real_source_tree_7 : Tree := (.impossible [(((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))),true),((1 : ℚ)/(1 : ℚ))),(((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),false),((1 : ℚ)/(1 : ℚ)))])
theorem real_source_checked_7 : checked real_source_formula real_source_context_7 real_source_tree_7 := by decide +kernel
def real_source_context_8 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),0)::real_source_context_6
def real_source_tree_8 : Tree := (.impossible [(((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ))),false),((1 : ℚ)/(1 : ℚ))),(((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),false),((1 : ℚ)/(1 : ℚ)))])
theorem real_source_checked_8 : checked real_source_formula real_source_context_8 real_source_tree_8 := by decide +kernel
def real_source_context_9 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),1)::real_source_context_6
def real_source_tree_9 : Tree := .leaf
theorem real_source_checked_9 : checked real_source_formula real_source_context_9 real_source_tree_9 := by decide +kernel
def real_source_tree_6 : Tree := .split (((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) real_source_tree_7 real_source_tree_8 real_source_tree_9
theorem real_source_checked_6 : checked real_source_formula real_source_context_6 real_source_tree_6 := checked_split real_source_formula real_source_context_6 (((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) real_source_tree_7 real_source_tree_8 real_source_tree_9 real_source_checked_7 real_source_checked_8 real_source_checked_9
def real_source_context_10 : Assignment := ((((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),1)::real_source_context_0
def real_source_context_11 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),-1)::real_source_context_10
def real_source_tree_11 : Tree := .leaf
theorem real_source_checked_11 : checked real_source_formula real_source_context_11 real_source_tree_11 := by decide +kernel
def real_source_context_12 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),0)::real_source_context_10
def real_source_tree_12 : Tree := .leaf
theorem real_source_checked_12 : checked real_source_formula real_source_context_12 real_source_tree_12 := by decide +kernel
def real_source_context_13 : Assignment := ((((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))),1)::real_source_context_10
def real_source_tree_13 : Tree := .leaf
theorem real_source_checked_13 : checked real_source_formula real_source_context_13 real_source_tree_13 := by decide +kernel
def real_source_tree_10 : Tree := .split (((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) real_source_tree_11 real_source_tree_12 real_source_tree_13
theorem real_source_checked_10 : checked real_source_formula real_source_context_10 real_source_tree_10 := checked_split real_source_formula real_source_context_10 (((-1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) real_source_tree_11 real_source_tree_12 real_source_tree_13 real_source_checked_11 real_source_checked_12 real_source_checked_13
def real_source_tree_1 : Tree := .split (((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) real_source_tree_2 real_source_tree_6 real_source_tree_10
theorem real_source_checked_1 : checked real_source_formula real_source_context_0 real_source_tree_1 := checked_split real_source_formula real_source_context_0 (((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) real_source_tree_2 real_source_tree_6 real_source_tree_10 real_source_checked_2 real_source_checked_6 real_source_checked_10
theorem real_source_free : PerfectPower.RealVisibility.FreeSegment originalObstacles (rationalVertex originalNodes 0) (rationalVertex originalNodes 0) :=
  PerfectPower.RealVisibility.segment_from_tree _ _ _ real_source_tree_1 real_source_checked_1
theorem real_complete : ∀ u v, u < originalNodes.length → v < originalNodes.length → u ≠ v →
  ((u,v) ∈ admitted ↔ PerfectPower.RealVisibility.FreeSegment originalObstacles (rationalVertex originalNodes u) (rationalVertex originalNodes v)) := by
  intro u v hu hv hne
  simp only [originalNodes,List.length_cons,List.length_nil] at hu hv
  interval_cases u <;> interval_cases v
  · omega
def realWalkCost : ℚ := (0 : ℚ)
theorem source_real_walk_cost : realWalkCost = ((0 : ℚ)/(1 : ℚ)) := by decide +kernel
theorem retained_real_walk : PerfectPower.RealVisibility.SourceWalk originalObstacles originalNodes 0 0 ((0 : ℚ)/(1 : ℚ)) := by
  rw [← source_real_walk_cost]
  exact PerfectPower.RealVisibility.SourceWalk.nil 0
#print axioms retained_real_walk
def realPotential (u : Nat) : ℚ := (potential u : ℚ)/((1 : ℚ)/(1 : ℚ))
theorem real_bounds_finite : ∀ u v : Fin 1, (u.val,v.val) ∈ admitted →
  realPotential v ≤ realPotential u+qweight (rationalVertex originalNodes u) (rationalVertex originalNodes v) := by decide +kernel
theorem real_bounds : ∀ u v, u < originalNodes.length → v < originalNodes.length → u ≠ v →
  PerfectPower.RealVisibility.FreeSegment originalObstacles (rationalVertex originalNodes u) (rationalVertex originalNodes v) →
  realPotential v ≤ realPotential u+qweight (rationalVertex originalNodes u) (rationalVertex originalNodes v) := by
  intro u v hu hv hne hf
  have hu' : u < 1 := by simpa [originalNodes] using hu
  have hv' : v < 1 := by simpa [originalNodes] using hv
  exact real_bounds_finite ⟨u,hu'⟩ ⟨v,hv'⟩ ((real_complete u v hu hv hne).mpr hf)
theorem source_real_dual : ((0 : ℚ)/(1 : ℚ)) = realPotential 0-realPotential 0 := by decide +kernel
theorem no_cheaper_real_walk {other : ℚ}
  (walk : PerfectPower.RealVisibility.SourceWalk originalObstacles originalNodes 0 0 other) : ((0 : ℚ)/(1 : ℚ)) ≤ other :=
  PerfectPower.RealVisibility.source_optimal_walk originalObstacles originalNodes realPotential real_bounds source_real_dual walk
#print axioms no_cheaper_real_walk
#print axioms real_complete

end PerfectPower.CheckedGraph.P34271842c53b8da39e1ed20ebf6abdd165770f5943e73d175e262107eaedda1e
