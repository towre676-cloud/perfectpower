import Std
import Lean.Elab.Tactic.Omega

namespace PerfectPower.BlastRecurrence

/-- Multiplicity-preserving nonempty path language, with an explicit fuel bound. -/
def paths (children : Nat → List Nat) : Nat → Nat → List (List Nat)
  | 0, _ => []
  | fuel + 1, v => [v] :: (children v).flatMap
      (fun w => (paths children fuel w).map (fun p => v :: p))

def coverage (weight : Nat → Nat) (p : List Nat) : Nat := (p.map weight).sum

def coefficient (weight : Nat → Nat) (language : List (List Nat)) (k c : Nat) : Nat :=
  language.countP (fun p => decide (p.length = k ∧ coverage weight p = c))

/-- The bivariate recurrence, coefficient by coefficient, retaining multiplicity.
    F_v = u v^(weight v) (1 + sum of child F_w). The translated predicate
    avoids truncated subtraction at coefficient indices below the shift. -/
theorem coefficient_recurrence (children : Nat → List Nat) (weight : Nat → Nat)
    (fuel v k c : Nat) :
    coefficient weight (paths children (fuel + 1) v) k c =
      (if 1 = k ∧ weight v = c then 1 else 0) +
      ((children v).map (fun w => (paths children fuel w).countP
        (fun p => decide (p.length + 1 = k ∧ weight v + coverage weight p = c)))).sum := by
  simp [coefficient, paths, List.countP_cons, List.countP_flatMap, List.countP_map, coverage,
    Function.comp_def, Nat.add_comm]

/-- Graph walks start at v, stop anywhere, and must be nonempty. -/
def walk (children : Nat → List Nat) : Nat → List Nat → Prop
  | _, [] => False
  | v, [a] => a = v
  | v, a :: b :: rest => a = v ∧ b ∈ children v ∧ walk children b (b :: rest)

theorem walk_length_bound (children : Nat → List Nat) (rank : Nat → Nat)
    (decreases : ∀ v w, w ∈ children v → rank w < rank v)
    (p : List Nat) (v : Nat) (h : walk children v p) : p.length ≤ rank v + 1 := by
  induction p generalizing v with
  | nil => simp [walk] at h
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b tail =>
      simp only [walk] at h
      have bound := ih b h.2.2
      have drop := decreases v b h.2.1
      simp only [List.length_cons] at *
      omega

/-- Every enumerated path is a walk, and every bounded walk is enumerated. -/
theorem mem_paths (children : Nat → List Nat) (fuel v : Nat) (p : List Nat) :
    p ∈ paths children fuel v ↔ walk children v p ∧ p.length ≤ fuel := by
  induction fuel generalizing v p with
  | zero =>
    cases p with
    | nil => simp [paths, walk]
    | cons a rest => simp [paths]
  | succ fuel ih =>
    cases p with
    | nil => simp [paths, walk]
    | cons a rest =>
      cases rest with
      | nil =>
        have empty : ∀ w, [] ∉ paths children fuel w := by
          intro w h
          have impossible := (ih w []).mp h
          simp [walk] at impossible
        simp [paths, List.mem_flatMap, List.mem_map, empty, walk, eq_comm]
      | cons b tail =>
        simp only [paths, List.mem_cons, List.mem_flatMap, List.mem_map,
          List.cons.injEq, List.cons_ne_nil, and_false, false_or, exists_and_right,
          walk, List.length_cons]
        constructor
        · rintro ⟨w, hw, path, hp, hv, htail⟩
          subst path
          have bound := (ih w (b :: tail)).mp hp
          have head : b = w := by
            cases tail with
            | nil => simpa [walk] using bound.1
            | cons x xs => exact bound.1.1
          subst w
          exact ⟨⟨hv.symm, hw, bound.1⟩, by simpa using Nat.succ_le_succ bound.2⟩
        · rintro ⟨⟨hv, hb, hw⟩, hl⟩
          refine ⟨b, hb, b :: tail, (ih b (b :: tail)).mpr ⟨hw, ?_⟩, hv.symm, rfl⟩
          simpa using Nat.le_of_succ_le_succ hl

/-- In a decreasing-rank DAG the fuel bound omits no admissible walk. -/
theorem complete_language (children : Nat → List Nat) (rank : Nat → Nat)
    (decreases : ∀ v w, w ∈ children v → rank w < rank v)
    (v : Nat) (p : List Nat) :
    p ∈ paths children (rank v + 1) v ↔ walk children v p := by
  rw [mem_paths]
  exact ⟨fun h => h.1, fun h => ⟨h, walk_length_bound children rank decreases p v h⟩⟩

theorem paths_head (children : Nat → List Nat) (fuel v : Nat) (p : List Nat)
    (h : p ∈ paths children fuel v) : p.head? = some v := by
  have hw := (mem_paths children fuel v p).mp h |>.1
  cases p with
  | nil => simp [walk] at hw
  | cons a rest =>
    cases rest with
    | nil => simpa [walk] using congrArg some hw
    | cons b tail => simpa using congrArg some hw.1

/-- Distinct successor lists enumerate every vertex path without duplicates. -/
theorem paths_nodup (children : Nat → List Nat) (distinct : ∀ v, (children v).Nodup)
    (fuel v : Nat) : (paths children fuel v).Nodup := by
  induction fuel generalizing v with
  | zero => simp [paths]
  | succ fuel ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨w, _, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
      have empty : p = [] := (List.cons.inj he).2
      have head := paths_head children fuel w p hp
      simp [empty] at head
    · apply List.pairwise_flatMap.mpr
      constructor
      · intro w _
        simpa [List.Nodup, List.pairwise_map] using ih w
      · apply (distinct v).imp
        intro w z different p hp q hq same
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
        have equal := (List.cons.inj same).2
        have headA := paths_head children fuel w a ha
        have headB := paths_head children fuel z b hb
        rw [equal] at headA
        exact different (Option.some.inj (headA.symm.trans headB))

#print axioms coefficient_recurrence
#print axioms walk_length_bound
#print axioms mem_paths
#print axioms complete_language
#print axioms paths_nodup
end PerfectPower.BlastRecurrence
