import PerfectPower.PlanningReplayBridge
import PerfectPower.PlanningTraceDecode

/-! Small source-bound proof objects. No final truth-table validation,
`native_decide`, or external replay result is used as a hypothesis. -/
namespace PerfectPower.PlanningReplayExamples
open PlanningDiagram PlanningCertificate PlanningPermutation PlanningReplayBridge

/-- A skipped-variable allocation at level 1 out of three variables. -/
def initial : List (StoredNode 3) := [storedReject 3, storedAccept 3]
def allocation : Option (StoredNode 3) := checkIndexedNode initial 1 1 0 2

theorem allocation_accepted : allocation.isSome = true := by decide

theorem allocation_population (out : StoredNode 3) (h : allocation = some out) :
    census (3-out.level) (eval out.value.diagram) = 2 := by
  exact (indexed_allocation_count initial 1 1 0 2 out h).symm

theorem bad_skip_multiplier : checkIndexedNode initial 1 1 0 1 = none := rfl
theorem bad_forward_reference : checkIndexedNode initial 1 7 0 2 = none := rfl
theorem bad_order : checkIndexedNode initial 3 1 0 1 = none := rfl
theorem bad_reduction : checkIndexedNode initial 1 1 1 4 = none := rfl

/-- The literal bytes are decoded inside Lean before indexed allocation. -/
def allocateBytes (bytes : List UInt8) : Option (StoredNode 3) := do
  let (record, rest) ← PlanningTraceDecode.readRecord bytes
  if rest.isEmpty then
    match record with
    | .node level lo hi claimed => checkIndexedNode initial level lo hi claimed
    | _ => none
  else none

theorem byte_allocation_accepted :
    (allocateBytes PlanningTraceDecode.fixture).isSome = true := by decide

theorem byte_allocation_population (out : StoredNode 3)
    (accepted : allocateBytes PlanningTraceDecode.fixture = some out) :
    census (3-out.level) (eval out.value.diagram) = 2 := by
  apply allocation_population out
  exact accepted

/-- The entire small binary fixture used by the Python adversarial tests has
one zero-cost coordinate, one forbidden coordinate, and one free coordinate. -/
def streamRoot : CheckedNode 3 := skipNode 1
  (branchNode (skipNode 1 (acceptNode 0)) (skipNode 1 (rejectNode 0)))

theorem stream_threshold : Threshold [0,1,0] 0 streamRoot.diagram := by
  have accepted : Threshold [0] 0 (.skip 1 .accept) :=
    Threshold.reuse (.accept [0] 0 (by decide)) (fun _ => rfl)
  have rejected : Threshold [0] (-1) (.skip 1 .reject) :=
    Threshold.reuse (.reject [0] (-1) (by decide)) (fun _ => rfl)
  have tail : Threshold [1,0] 0 (.branch (.skip 1 .accept) (.skip 1 .reject)) :=
    Threshold.split accepted rejected (same_refl _)
  exact Threshold.split tail tail (reduction_sound _)

theorem stream_stage_evidence : Stages 3 [[0,1,0]] [0] streamRoot.diagram :=
  Stages.snoc Stages.nil stream_threshold (.oneLeft 3 streamRoot.diagram)

theorem complete_small_fixture_population : census 3 (feasible [[0,1,0]] [0]) = 4 := by
  have result := stage_population streamRoot stream_stage_evidence
  change streamRoot.count = census 3 (signedFeasible [[0,1,0]] ([0].map Int.ofNat)) at result
  rw [census_congr 3 _ _ (signed_nat [[0,1,0]] [0])] at result
  have literal : streamRoot.count = 4 := by decide
  omega

/-- Reusable threshold proof, following the source recurrence, not enumeration. -/
theorem nat_threshold (ws : List Nat) (cap : Nat) :
    Threshold ws (cap : Int) (threshold ws cap) := by
  induction ws generalizing cap with
  | nil => exact .accept [] (cap : Int) (by simp)
  | cons w ws ih =>
    unfold threshold
    by_cases within : w ≤ cap
    · simp only [within, if_true]
      apply Threshold.split (ih cap)
      · have equal : ((cap-w : Nat) : Int) = (cap : Int) - (w : Int) := by omega
        rw [← equal]
        exact ih (cap-w)
      · exact same_refl _
    · simp only [within, if_false]
      exact Threshold.split (ih cap) (.reject ws _ (by omega)) (same_refl _)

/-- Construct the conjunction recurrence with existing proved cofactors. -/
theorem intersect_semantic (n : Nat) (a b : Diagram) :
    ∀ xs, xs.length = n → eval (intersect n a b) xs = (eval a xs && eval b xs) :=
  intersect_correct n a b

/-- For an explicit small proof object it is enough to supply the exact-length
intersection equation already proved by `intersect_correct`. -/
def rows : List (List Nat) := [[2,0,1], [0,1,1]]
def caps : List Nat := [1,1]
def order : List Nat := [2,0,1]
def orderedRows : List (List Nat) := reorder order rows

def t0 : Diagram := threshold [1,2,0] 1
def t1 : Diagram := threshold [1,0,1] 1
def answer : Diagram := intersect 3 t0 t1

def checkedAnswer : CheckedNode 3 :=
  ⟨answer, weight answer 3, intersect_fits 3 t0 t1, rfl⟩

theorem threshold0 : Threshold [1,2,0] 1 t0 := nat_threshold _ _
theorem threshold1 : Threshold [1,0,1] 1 t1 := nat_threshold _ _

/-- A direct conjunction derivation for these three-bit source diagrams.
At zero remaining bits all cofactors are actual terminals. -/
theorem conjunction_fixture : Conjunction 3 t0 t1 answer := by
  apply Conjunction.split
  · apply Conjunction.split
    · apply Conjunction.split
      · exact .oneLeft 0 .accept
      · exact .oneLeft 0 .accept
      · exact same_refl _
    · apply Conjunction.split
      · exact .zeroLeft 0 .accept
      · exact .zeroLeft 0 .accept
      · exact same_refl _
    · exact same_refl _
  · apply Conjunction.split
    · apply Conjunction.split
      · exact .oneLeft 0 .accept
      · exact .oneLeft 0 .reject
      · exact same_refl _
    · apply Conjunction.split
      · exact .zeroLeft 0 .accept
      · exact .zeroLeft 0 .reject
      · exact same_refl _
    · exact same_refl _
  · exact same_refl _

theorem source_stages : Stages 3 orderedRows (caps.map Int.ofNat) checkedAnswer.diagram := by
  have first : Stages 3 [[1,2,0]] [1] t0 :=
    Stages.snoc Stages.nil threshold0 (.oneLeft 3 t0)
  exact Stages.snoc first threshold1 conjunction_fixture

theorem coordinate_permutation : List.Perm order (List.range 3) := by
  exact (List.Perm.swap 0 2 [1]).trans (List.Perm.cons 0 (List.Perm.swap 1 2 []))

theorem original_exact_population : census 3 (feasible rows caps) = 3 := by
  have result := PlanningReplayBridge.original_population checkedAnswer order rows caps
    coordinate_permutation (by decide) source_stages
  have literal : checkedAnswer.count = 3 := by decide
  omega

/-- Negative capacities reject even the empty subset; natural truncation
would incorrectly accept the all-zero cost row. -/
theorem negative_threshold : Threshold [0,0] (-1) .reject := .reject _ _ (by decide)
theorem negative_population : census 2 (fun xs => decide ((dot [0,0] xs : Int) ≤ -1)) = 0 := by
  rw [← census_congr 2 _ _ (threshold_sound negative_threshold)]
  exact census_false 2

end PerfectPower.PlanningReplayExamples
