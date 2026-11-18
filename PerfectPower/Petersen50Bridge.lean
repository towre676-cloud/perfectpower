import PerfectPower.PetersenPlanning
import PerfectPower.PlanningReplayBridge

/-! Specialization to the exact coordinate order in the retained replay receipt.
The final result below is CONDITIONAL on complete semantic stage evidence. -/
namespace PerfectPower.Petersen50Bridge
open PlanningDiagram PlanningCertificate PlanningPermutation PlanningReplayBridge

def order : List Nat := [15, 4, 1, 42, 40, 3, 20, 2, 0, 46, 7, 22, 45, 10, 5, 39, 32, 47, 43, 14, 16, 11, 26, 31, 21, 17, 9, 41, 37, 36, 25, 6, 23, 8, 27, 28, 33, 34, 38, 24, 44, 18, 30, 48, 49, 35, 12, 13, 19, 29]

theorem receipt_order_is_permutation : List.Perm order (List.range 50) := by decide

def orderedRows : List (List Nat) := reorder order PetersenPlanning.rows

theorem ordered_dimensions : orderedRows.length = 5 ∧
    (∀ row ∈ orderedRows, row.length = 50) := by decide

/-- An explicit remaining obligation, not a certificate for the large witness. -/
theorem population_if_complete_stage_evidence (c : CheckedNode 50)
    (source : Stages 50 orderedRows (PetersenPlanning.capacities.map Int.ofNat) c.diagram)
    (count : c.count = 702508860122761) :
    census 50 (feasible PetersenPlanning.rows PetersenPlanning.capacities) = 702508860122761 := by
  rw [← count]
  exact (PlanningReplayBridge.original_population c order PetersenPlanning.rows
    PetersenPlanning.capacities receipt_order_is_permutation
    PetersenPlanning.original_dimensions.2 source).symm

end PerfectPower.Petersen50Bridge
