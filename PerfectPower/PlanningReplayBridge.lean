import PerfectPower.PlanningPermutation

/-! Semantic obligations for decoded pp-bdd-trace/1 records. These are proof
rules, not an assertion that the Python parser produces proofs of them. -/
namespace PerfectPower.PlanningReplayBridge
open PlanningDiagram PlanningCertificate PlanningPermutation

def signedFeasible : List (List Nat) → List Int → List Bool → Bool
  | [], [], _ => true
  | row::rows, cap::caps, xs => decide ((dot row xs : Int) ≤ cap) && signedFeasible rows caps xs
  | _, _, _ => false

/-- Unlike natural subtraction, this models negative residual capacities. -/
inductive Threshold : List Nat → Int → Diagram → Prop where
  | reject (ws cap) (negative : cap < 0) : Threshold ws cap .reject
  | accept (ws cap) (enough : (ws.sum : Int) ≤ cap) : Threshold ws cap .accept
  | split {w : Nat} {ws : List Nat} {cap : Int} {lo hi out : Diagram}
      (low : Threshold ws cap lo)
      (high : Threshold ws (cap - (w : Int)) hi)
      (made : Same (.branch lo hi) out) : Threshold (w::ws) cap out
  | reuse {ws cap a b} (proof : Threshold ws cap a) (same : Same a b) : Threshold ws cap b

theorem threshold_sound (h : Threshold ws cap d) :
    ∀ xs, eval d xs = decide ((dot ws xs : Int) ≤ cap) := by
  induction h with
  | reject ws cap negative =>
    intro xs
    have h : ¬ (dot ws xs : Int) ≤ cap := by omega
    simp [eval, h]
  | accept ws cap enough =>
    intro xs
    have bound := dot_bound ws xs
    have h : (dot ws xs : Int) ≤ cap := by omega
    simp [eval, h]
  | @split w ws cap lo hi out low high made il ih =>
    intro xs
    rw [← made xs]
    simp only [eval, dot]
    by_cases hb : xs.headD false = true
    · simp only [hb, if_true, ih, Int.natCast_add]
      simp only [show (dot ws xs.tail : Int) ≤ cap - (w : Int) ↔
        (w : Int) + (dot ws xs.tail : Int) ≤ cap by omega]
    · simp only [hb, Bool.false_eq_true, if_false, Nat.zero_add, il]
  | reuse proof same ih => intro xs; rw [← same xs]; exact ih xs

/-- Apply proofs can reuse earlier results and need only exact-length inputs.
The split rule uses actual Boolean cofactors, avoiding missing-coordinate
assumptions when a node skips levels. -/
inductive Conjunction : Nat → Diagram → Diagram → Diagram → Prop where
  | zeroLeft (n b) : Conjunction n .reject b .reject
  | zeroRight (n a) : Conjunction n a .reject .reject
  | oneLeft (n b) : Conjunction n .accept b b
  | oneRight (n a) : Conjunction n a .accept a
  | equal (n a) : Conjunction n a a a
  | split {n a b lo hi out}
      (low : Conjunction n (cofactor a false) (cofactor b false) lo)
      (high : Conjunction n (cofactor a true) (cofactor b true) hi)
      (made : Same (.branch lo hi) out) : Conjunction (n+1) a b out
  | skip {n a b out} (r : Nat) (proof : Conjunction n a b out) :
      Conjunction (n+r) (.skip r a) (.skip r b) (.skip r out)
  | reuse {n a b c out} (proof : Conjunction n a b c) (same : Same c out) : Conjunction n a b out

theorem conjunction_sound (h : Conjunction n a b d) :
    ∀ xs, xs.length = n → eval d xs = (eval a xs && eval b xs) := by
  induction h with
  | zeroLeft n b => intro xs _; simp [eval]
  | zeroRight n a => intro xs _; simp [eval]
  | oneLeft n b => intro xs _; simp [eval]
  | oneRight n a => intro xs _; simp [eval]
  | equal n a => intro xs _; simp
  | split low high made il ih =>
    apply conjunction_step_length _ _ _ _ _ _ _ _ made
    · intro xs length
      simpa only [cofactor_correct] using il xs length
    · intro xs length
      simpa only [cofactor_correct] using ih xs length
  | skip r proof ih =>
    intro xs length
    exact ih (xs.drop r) (by simp [length])
  | reuse proof same ih => intro xs length; rw [← same xs]; exact ih xs length

/-- Source stages are chronological, just as tag 4 records are. A complete
stage chain cannot omit, duplicate, or reorder a resource inequality. -/
inductive Stages (n : Nat) : List (List Nat) → List Int → Diagram → Prop where
  | nil : Stages n [] [] .accept
  | snoc {rows caps previous row cap threshold out}
      (previousStages : Stages n rows caps previous)
      (next : Threshold row cap threshold)
      (intersection : Conjunction n previous threshold out) :
      Stages n (rows++[row]) (caps++[cap]) out

theorem signed_append (rows : List (List Nat)) (caps : List Int) (row : List Nat)
    (cap : Int) (xs : List Bool) (lengths : rows.length = caps.length) :
    signedFeasible (rows++[row]) (caps++[cap]) xs =
      (signedFeasible rows caps xs && decide ((dot row xs : Int) ≤ cap)) := by
  induction rows generalizing caps with
  | nil => cases caps <;> simp_all [signedFeasible]
  | cons first rows ih =>
    cases caps with
    | nil => simp at lengths
    | cons bound caps =>
      simp only [List.cons_append, signedFeasible]
      rw [ih caps (by simpa using lengths)]
      exact (Bool.and_assoc _ _ _).symm

theorem stages_sound (h : Stages n rows caps d) :
    rows.length = caps.length ∧ ∀ xs, xs.length = n → eval d xs = signedFeasible rows caps xs := by
  induction h with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | snoc previousStages next intersection ih =>
    constructor
    · simp [ih.1]
    · intro xs length
      rw [conjunction_sound intersection xs length, ih.2 xs length,
        threshold_sound next xs, signed_append _ _ _ _ _ ih.1]

theorem signed_nat (rows : List (List Nat)) (caps : List Nat) (xs : List Bool) :
    signedFeasible rows (caps.map Int.ofNat) xs = feasible rows caps xs := by
  induction rows generalizing caps with
  | nil => cases caps <;> rfl
  | cons row rows ih =>
    cases caps with
    | nil => rfl
    | cons cap caps => simp [signedFeasible, feasible, ih]

theorem stage_population (c : CheckedNode n) (h : Stages n rows caps c.diagram) :
    c.count = census n (signedFeasible rows caps) := by
  rw [checked_node_population]
  exact census_congr_length n _ _ (stages_sound h).2

/-- Finalization bridge: checked counts + decoded semantic stage evidence +
source permutation + literal row shape imply the original exact population.
Neither parser correctness nor evidence for the large witness is assumed. -/
theorem original_population (c : CheckedNode n) (order : List Nat)
    (rows : List (List Nat)) (caps : List Nat)
    (permutation : List.Perm order (List.range n))
    (shape : ∀ row ∈ rows, row.length = n)
    (source : Stages n (reorder order rows) (caps.map Int.ofNat) c.diagram) :
    c.count = census n (feasible rows caps) := by
  have count := stage_population c source
  rw [census_congr n _ _ (signed_nat _ _)] at count
  have length : order.length = n := by simpa using permutation.length_eq
  have transport := reordered_population permutation rows caps
  rw [length, List.length_range, reorder_identity rows n shape] at transport
  exact count.trans transport

/-- The exact skipped-variable arithmetic used for a tag 1 allocation. -/
theorem branch_skipped_count (lo hi : CheckedNode n) (gap : Nat) :
    (branchNode (skipNode gap lo) (skipNode gap hi)).count =
      2^gap * lo.count + 2^gap * hi.count := rfl

theorem cast_count (h : n = m) (c : CheckedNode n) : (castNode h c).count = c.count := by
  cases h
  rfl

theorem lift_count (c : StoredNode variables) (level : Nat) (h : level ≤ c.level) :
    (liftNode c level h).count = 2^(c.level-level)*c.value.count := by
  unfold liftNode
  rw [cast_count]
  rfl

/-- Tag 4/5 root populations include all variables skipped above the root. -/
theorem root_population (c : StoredNode variables) :
    2^c.level*c.value.count =
      census variables (eval (liftNode c 0 (Nat.zero_le _)).diagram) := by
  have count := checked_node_population (liftNode c 0 (Nat.zero_le _))
  simpa only [lift_count, Nat.sub_zero] using count

/-- Children can have different levels; each free gap is multiplied separately. -/
theorem unequal_skips_count (lo : CheckedNode l) (hi : CheckedNode h) (lg hg : Nat)
    (sameLevel : h+hg = l+lg) :
    (branchNode (skipNode lg lo) (castNode sameLevel (skipNode hg hi))).count =
      2^lg*lo.count + 2^hg*hi.count := by
  simp only [branchNode, cast_count, skipNode]

/-- A successful indexed allocation certifies its count label, not just its
children. This statement also audits the existing executable local checker. -/
theorem indexed_allocation_count (table : List (StoredNode variables))
    (level lo hi claimed : Nat) (out : StoredNode variables)
    (accepted : checkIndexedNode table level lo hi claimed = some out) :
    claimed = census (variables-out.level) (eval out.value.diagram) := by
  unfold checkIndexedNode at accepted
  cases hl : table[lo]? with
  | none => simp [hl] at accepted
  | some low =>
    cases hh : table[hi]? with
    | none => simp [hl, hh] at accepted
    | some high =>
      simp only [hl, hh, bind, Option.bind] at accepted
      split at accepted
      next good =>
        by_cases count : claimed = (liftNode low (level+1) (by omega)).count +
            (liftNode high (level+1) (by omega)).count
        · simp only [checkBranch, count, if_pos, bind, Option.bind, pure,
            Pure.pure, Option.some.injEq] at accepted
          subst out
          rw [← checked_node_population]
          simpa only [cast_count, branchNode] using count
        · simp [checkBranch, count, bind, Option.bind] at accepted
      next bad => simp at accepted

end PerfectPower.PlanningReplayBridge
