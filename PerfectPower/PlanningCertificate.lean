import PerfectPower.PlanningDiagram

/-! Local replay rules for pp-bdd-trace/1. These rules are kernel checked.
The binary parser and the packed external tables are NOT imported as axioms.
A large external replay is not a kernel proof of the corresponding bytes.
-/
namespace PerfectPower.PlanningCertificate
open PlanningDiagram

/-- A node stores a checked finite population, not an assumed count label. -/
structure CheckedNode (n : Nat) where
  diagram : Diagram
  count : Nat
  fits : Fits diagram n
  correct : count = weight diagram n

def rejectNode (n : Nat) : CheckedNode n := ⟨.reject, 0, .reject n, rfl⟩
def acceptNode (n : Nat) : CheckedNode n := ⟨.accept, 2^n, .accept n, rfl⟩

def skipNode (r : Nat) (c : CheckedNode n) : CheckedNode (n+r) :=
  ⟨.skip r c.diagram, 2^r*c.count, .skip r c.fits, by simp [weight, c.correct]⟩

def branchNode (lo hi : CheckedNode n) : CheckedNode (n+1) :=
  ⟨.branch lo.diagram hi.diagram, lo.count+hi.count, .branch lo.fits hi.fits,
    by simp [weight, lo.correct, hi.correct]⟩

/-- Executable local check: an altered count label returns none. -/
def checkBranch (lo hi : CheckedNode n) (claimed : Nat) : Option (CheckedNode (n+1)) :=
  if claimed = lo.count + hi.count then some (branchNode lo hi) else none

theorem checked_node_population (c : CheckedNode n) : c.count = census n (eval c.diagram) := by
  rw [c.correct, weight_correct c.fits]

theorem checked_branch_population (lo hi : CheckedNode n) (claimed : Nat)
    (accepted : checkBranch lo hi claimed = some out) :
    claimed = census (n+1) (eval out.diagram) := by
  unfold checkBranch at accepted
  split at accepted
  next h =>
    have e : branchNode lo hi = out := Option.some.inj accepted
    rw [← e, ← checked_node_population]
    exact h
  next h => cases accepted

theorem changed_branch_count_rejected (lo hi : CheckedNode n) (claimed : Nat)
    (bad : claimed ≠ lo.count + hi.count) : checkBranch lo hi claimed = none := by
  simp [checkBranch, bad]

/-- Level-aware node table. Its entries carry kernel-checked weights. -/
structure StoredNode (variables : Nat) where
  level : Nat
  bound : level ≤ variables
  value : CheckedNode (variables-level)

def castNode (h : n = m) (c : CheckedNode n) : CheckedNode m := h ▸ c

def liftNode (c : StoredNode variables) (level : Nat) (h : level ≤ c.level) :
    CheckedNode (variables-level) :=
  castNode (by have b := c.bound; omega) (skipNode (c.level-level) c.value)

/-- Child indices must address earlier entries supplied in the table. The
caller cannot construct a successful result by assuming a numerical weight. -/
def checkIndexedNode (table : List (StoredNode variables)) (level lo hi claimed : Nat) :
    Option (StoredNode variables) := do
  let low ← table[lo]?
  let high ← table[hi]?
  if h : level < variables ∧ level < low.level ∧ level < high.level ∧ lo ≠ hi then
    let l := liftNode low (level+1) (by omega)
    let r := liftNode high (level+1) (by omega)
    let checked ← checkBranch l r claimed
    pure ⟨level, by omega, castNode (by omega) checked⟩
  else none

theorem stored_node_population (c : StoredNode variables) :
    c.value.count = census (variables-c.level) (eval c.value.diagram) :=
  checked_node_population c.value

theorem missing_child_rejected :
    checkIndexedNode ([] : List (StoredNode 5)) 0 0 0 1 = none := rfl

def storedReject (n : Nat) : StoredNode n := ⟨n, Nat.le_refl n, castNode (by omega) (rejectNode 0)⟩
def storedAccept (n : Nat) : StoredNode n := ⟨n, Nat.le_refl n, castNode (by omega) (acceptNode 0)⟩

theorem variable_order_rejected :
    checkIndexedNode [storedReject 5, storedAccept 5] 5 0 1 1 = none := rfl

theorem unreduced_node_rejected :
    checkIndexedNode [storedReject 5, storedAccept 5] 0 1 1 32 = none := rfl

theorem manipulated_count_rejected :
    checkIndexedNode [storedReject 5, storedAccept 5] 0 0 1 17 = none := rfl

/-- Interprets native reduction/reuse as equality of finite predicates. -/
def Same (a b : Diagram) : Prop := ∀ xs, eval a xs = eval b xs

theorem same_refl (a : Diagram) : Same a a := fun _ => rfl

theorem reduction_sound (a : Diagram) : Same (.branch a a) (.skip 1 a) :=
  reduce_equal_branches a

theorem skip_sound (r : Nat) (a b : Diagram) (h : Same a b) :
    Same (.skip r a) (.skip r b) := fun xs => h (xs.drop r)

theorem count_transport (a b : Diagram) (h : Same a b) (n : Nat) :
    census n (eval a) = census n (eval b) := census_congr n _ _ h

/-- Bottom-up threshold replay. Child evidence may be shared arbitrarily. -/
inductive ThresholdEvidence : List Nat → Nat → Diagram → Prop where
  | accept (ws cap) (bound : ws.sum ≤ cap) : ThresholdEvidence ws cap .accept
  | branch (w ws cap lo hi) (within : w ≤ cap)
      (low : ThresholdEvidence ws cap lo)
      (high : ThresholdEvidence ws (cap-w) hi) :
      ThresholdEvidence (w::ws) cap (.branch lo hi)
  | heavy (w ws cap lo hi) (over : cap < w)
      (low : ThresholdEvidence ws cap lo) (high : Same hi .reject) :
      ThresholdEvidence (w::ws) cap (.branch lo hi)
  | reuse {ws cap a b} : ThresholdEvidence ws cap a → Same a b → ThresholdEvidence ws cap b

theorem threshold_evidence_sound (e : ThresholdEvidence ws cap d) :
    ∀ xs, eval d xs = decide (dot ws xs ≤ cap) := by
  induction e with
  | accept ws cap bound =>
    intro xs
    have h := Nat.le_trans (dot_bound ws xs) bound
    simp [eval, h]
  | branch w ws cap lo hi within low high il ih =>
    intro xs
    simp only [eval, dot]
    by_cases hb : xs.headD false = true
    · simp only [hb, if_true, ih]
      simp only [show dot ws xs.tail ≤ cap-w ↔ w+dot ws xs.tail ≤ cap by omega]
    · simp only [hb, Bool.false_eq_true, if_false, Nat.zero_add, il]
  | heavy w ws cap lo hi over low high il =>
    intro xs
    simp only [eval, dot]
    by_cases hb : xs.headD false = true
    · simp only [hb, if_true]
      have hh := high xs.tail
      simp only [eval] at hh
      rw [hh]
      exact (decide_eq_false (by omega)).symm
    · simp only [hb, Bool.false_eq_true, if_false, Nat.zero_add, il]
  | reuse e same ih => intro xs; rw [← same xs]; exact ih xs

/-- Length-restricted replay rule; unlike arbitrary-list equality it never
uses a missing input coordinate. -/
theorem conjunction_step_length (a b lo hi out : Diagram) (n : Nat)
    (low : ∀ xs, xs.length = n → eval lo xs = (eval a (false::xs) && eval b (false::xs)))
    (high : ∀ xs, xs.length = n → eval hi xs = (eval a (true::xs) && eval b (true::xs)))
    (made : Same (.branch lo hi) out) :
    ∀ xs, xs.length = n+1 → eval out xs = (eval a xs && eval b xs) := by
  intro xs length
  cases xs with
  | nil => simp at length
  | cons bit xs =>
    have h : xs.length = n := by simpa using length
    rw [← made (bit::xs)]
    cases bit <;> simp [eval, low xs h, high xs h]

/-- Resource-stage induction is the missing source obligation in a bare DAG
count. This relation requires evidence for EVERY supplied inequality. -/
inductive SourceChain : List (List Nat) → List Nat → Diagram → Prop where
  | nil : SourceChain [] [] .accept
  | cons {row rows cap caps t rest out}
      (threshold : ThresholdEvidence row cap t)
      (tail : SourceChain rows caps rest)
      (intersection : ∀ xs, eval out xs = (eval t xs && eval rest xs)) :
      SourceChain (row::rows) (cap::caps) out

theorem source_chain_sound (h : SourceChain rows caps d) :
    ∀ xs, eval d xs = feasible rows caps xs := by
  induction h with
  | nil => intro xs; rfl
  | cons threshold tail intersection ih =>
    intro xs
    rw [intersection xs, threshold_evidence_sound threshold xs, ih xs]
    rfl

theorem source_bound_population (c : CheckedNode n) (h : SourceChain rows caps c.diagram) :
    c.count = census n (feasible rows caps) := by
  rw [checked_node_population]
  exact census_congr n _ _ (source_chain_sound h)

/-- Original feasible predicate after appending one more resource. -/
theorem feasible_append_resource (rows : List (List Nat)) (caps row : List Nat)
    (cap : Nat) (xs : List Bool) (lengths : rows.length = caps.length) :
    feasible (rows++[row]) (caps++[cap]) xs =
      (feasible rows caps xs && decide (dot row xs ≤ cap)) := by
  induction rows generalizing caps with
  | nil => cases caps <;> simp_all [feasible]
  | cons first rows ih =>
    cases caps with
    | nil => simp at lengths
    | cons bound caps =>
      simp only [List.cons_append, feasible]
      rw [ih caps (by simpa using lengths)]
      exact (Bool.and_assoc _ _ _).symm

/-- Chronological stage evidence matches the binary stream's left-to-right
resource order, including its exact previous-root conjunction. -/
inductive PrefixEvidence : List (List Nat) → List Nat → Diagram → Prop where
  | nil : PrefixEvidence [] [] .accept
  | snoc {rows caps previous row cap threshold out}
      (tail : PrefixEvidence rows caps previous)
      (next : ThresholdEvidence row cap threshold)
      (intersection : ∀ xs, eval out xs = (eval previous xs && eval threshold xs)) :
      PrefixEvidence (rows++[row]) (caps++[cap]) out

theorem prefix_evidence_sound (h : PrefixEvidence rows caps d) :
    rows.length = caps.length ∧ ∀ xs, eval d xs = feasible rows caps xs := by
  induction h with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | snoc tail next intersection ih =>
    constructor
    · simp [ih.1]
    · intro xs
      rw [intersection xs, ih.2 xs, threshold_evidence_sound next xs,
        feasible_append_resource _ _ _ _ xs ih.1]

theorem prefix_source_bound_population (c : CheckedNode n)
    (h : PrefixEvidence rows caps c.diagram) : c.count = census n (feasible rows caps) := by
  rw [checked_node_population]
  exact census_congr n _ _ (prefix_evidence_sound h).2

/-- Exhaustive source bridge for deliberately small independent fixtures. -/
theorem finite_validation_sound (n : Nat) (f g : List Bool → Bool)
    (checked : (assignments n).all (fun xs => decide (f xs = g xs)) = true) :
    ∀ xs, xs.length = n → f xs = g xs := by
  intro xs length
  have hc := assignments_multiplicity n xs
  rw [if_pos length] at hc
  have positive : 0 < (assignments n).countP (fun ys => decide (ys = xs)) := by omega
  obtain ⟨ys, member, equal⟩ := List.countP_pos_iff.mp positive
  have eq : ys = xs := of_decide_eq_true equal
  subst ys
  exact of_decide_eq_true (List.all_eq_true.mp checked xs member)

theorem small_source_bound_population (c : CheckedNode n) (rows : List (List Nat)) (caps : List Nat)
    (checked : (assignments n).all (fun xs => decide (eval c.diagram xs = feasible rows caps xs)) = true) :
    c.count = census n (feasible rows caps) := by
  rw [checked_node_population]
  exact census_congr_length n _ _ (finite_validation_sound n _ _ checked)

end PerfectPower.PlanningCertificate
