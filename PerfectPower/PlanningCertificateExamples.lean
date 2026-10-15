import PerfectPower.PlanningCertificate
namespace PerfectPower.PlanningCertificateExamples
open PlanningDiagram PlanningCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def rows : List (List Nat) := [[3, 4, 2, 5, 1], [2, 0, 5, 1, 4]]
def caps : List Nat := [7, 5]
def node0 : CheckedNode 0 := rejectNode 0
def node1 : CheckedNode 0 := acceptNode 0
def node2 : CheckedNode 1 := branchNode (skipNode 0 node1) (skipNode 0 node0)
theorem count2 : node2.count = 1 := by decide
def node3 : CheckedNode 2 := branchNode (skipNode 1 node1) (skipNode 0 node2)
theorem count3 : node3.count = 3 := by decide
def node4 : CheckedNode 3 := branchNode (skipNode 2 node1) (skipNode 0 node3)
theorem count4 : node4.count = 7 := by decide
def node5 : CheckedNode 2 := branchNode (skipNode 1 node1) (skipNode 1 node0)
theorem count5 : node5.count = 2 := by decide
def node6 : CheckedNode 4 := branchNode (skipNode 0 node4) (skipNode 1 node5)
theorem count6 : node6.count = 11 := by decide
def node7 : CheckedNode 2 := branchNode (skipNode 0 node2) (skipNode 1 node0)
theorem count7 : node7.count = 1 := by decide
def node8 : CheckedNode 3 := branchNode (skipNode 0 node7) (skipNode 2 node0)
theorem count8 : node8.count = 1 := by decide
def node9 : CheckedNode 4 := branchNode (skipNode 1 node5) (skipNode 0 node8)
theorem count9 : node9.count = 5 := by decide
def node10 : CheckedNode 5 := branchNode (skipNode 0 node6) (skipNode 0 node9)
theorem count10 : node10.count = 16 := by decide
def node11 : CheckedNode 3 := branchNode (skipNode 2 node1) (skipNode 0 node7)
theorem count11 : node11.count = 5 := by decide
def node12 : CheckedNode 3 := branchNode (skipNode 1 node2) (skipNode 2 node0)
theorem count12 : node12.count = 2 := by decide
def node13 : CheckedNode 5 := branchNode (skipNode 1 node11) (skipNode 1 node12)
theorem count13 : node13.count = 14 := by decide
def node14 : CheckedNode 3 := branchNode (skipNode 0 node5) (skipNode 0 node7)
theorem count14 : node14.count = 3 := by decide
def node15 : CheckedNode 4 := branchNode (skipNode 0 node11) (skipNode 0 node14)
theorem count15 : node15.count = 8 := by decide
def node16 : CheckedNode 5 := branchNode (skipNode 0 node15) (skipNode 1 node8)
theorem count16 : node16.count = 10 := by decide
def root : CheckedNode 5 := skipNode 0 node16
theorem literal_count : root.count = 10 := by decide
theorem literal_source_check : (assignments 5).all (fun xs => decide (eval root.diagram xs = feasible rows caps xs)) = true := by decide
theorem native_diagram_original_predicate : ∀ xs, xs.length = 5 → eval root.diagram xs = feasible rows caps xs := finite_validation_sound 5 _ _ literal_source_check
theorem native_population_original_predicate : census 5 (feasible rows caps) = 10 := by
  rw [← small_source_bound_population root rows caps literal_source_check, literal_count]
end PerfectPower.PlanningCertificateExamples
