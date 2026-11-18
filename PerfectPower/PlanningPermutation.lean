import PerfectPower.PlanningCertificate

/-! Population transport under an arbitrary permutation of source projects.
The proof enumerates neither the assignments nor the large witness. -/
namespace PerfectPower.PlanningPermutation
open PlanningDiagram PlanningCertificate

/-- The selected projects, in the supplied coordinate order. -/
def selected : List α → List Bool → List α
  | [], _ => []
  | a::as, xs => if xs.headD false then a :: selected as xs.tail else selected as xs.tail

/-- Count subsets using project identities rather than bit positions. -/
def subsets : List α → (List α → Bool) → Nat
  | [], f => if f [] then 1 else 0
  | a::as, f => subsets as f + subsets as (fun chosen => f (a::chosen))

theorem subsets_congr (as : List α) (f g : List α → Bool)
    (h : ∀ xs, f xs = g xs) : subsets as f = subsets as g := by
  induction as generalizing f g with
  | nil => simp [subsets, h]
  | cons a as ih => simp only [subsets]; rw [ih f g h, ih _ _ (fun xs => h (a::xs))]

theorem subsets_census (as : List α) (f : List α → Bool) :
    subsets as f = census as.length (fun xs => f (selected as xs)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [subsets, census, selected, ih]

/-- Reordering project identities preserves population when feasibility depends
only on the selected projects. This is a generic, non-enumerative theorem. -/
theorem subsets_perm {as bs : List α} (p : List.Perm as bs) (f : List α → Bool)
    (invariant : ∀ xs ys, List.Perm xs ys → f xs = f ys) :
    subsets as f = subsets bs f := by
  induction p generalizing f with
  | nil => rfl
  | cons a p ih =>
    simp only [subsets]
    rw [ih f invariant, ih (fun xs => f (a::xs))
      (fun xs ys h => invariant _ _ (List.Perm.cons a h))]
  | swap a b as =>
    simp only [subsets]
    have h := subsets_congr as (fun xs => f (b::a::xs)) (fun xs => f (a::b::xs))
      (fun xs => invariant _ _ (List.Perm.swap a b xs))
    omega
  | trans p q ip iq => exact (ip f invariant).trans (iq f invariant)

theorem sum_perm (p : List.Perm xs ys) : (xs : List Nat).sum = ys.sum := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [ih]
  | swap a b as => simp only [List.sum_cons]; omega
  | trans p q ip iq => exact ip.trans iq

def cost (row : List Nat) (projects : List Nat) : Nat :=
  (projects.map (fun i => row[i]?.getD 0)).sum

def projectFeasible : List (List Nat) → List Nat → List Nat → Bool
  | [], [], _ => true
  | row::rows, cap::caps, chosen => decide (cost row chosen ≤ cap) && projectFeasible rows caps chosen
  | _, _, _ => false

theorem projectFeasible_perm (rows : List (List Nat)) (caps : List Nat)
    (p : List.Perm xs ys) : projectFeasible rows caps xs = projectFeasible rows caps ys := by
  induction rows generalizing caps with
  | nil => cases caps <;> rfl
  | cons row rows ih =>
    cases caps with
    | nil => rfl
    | cons cap caps =>
      have h : cost row xs = cost row ys := sum_perm (p.map _)
      simp only [projectFeasible, h, ih caps]

def reorder (order : List Nat) (rows : List (List Nat)) : List (List Nat) :=
  rows.map (fun row => order.map (fun i => row[i]?.getD 0))

theorem dot_selected (as : List α) (w : α → Nat) (xs : List Bool) :
    dot (as.map w) xs = ((selected as xs).map w).sum := by
  induction as generalizing xs with
  | nil => rfl
  | cons a as ih =>
    cases hb : xs.headD false <;> simp only [List.map_cons, dot, selected, hb, Bool.false_eq_true, if_false, if_true, List.map_cons, List.sum_cons, Nat.zero_add, ih]

theorem reordered_semantics (order : List Nat) (rows : List (List Nat)) (caps : List Nat)
    (xs : List Bool) :
    feasible (reorder order rows) caps xs = projectFeasible rows caps (selected order xs) := by
  induction rows generalizing caps with
  | nil => cases caps <;> rfl
  | cons row rows ih =>
    cases caps with
    | nil => rfl
    | cons cap caps =>
      change (decide (dot (order.map _) xs ≤ cap) && feasible (reorder order rows) caps xs) = _
      rw [dot_selected, ih caps]
      rfl

theorem reordered_population (p : List.Perm order original) (rows : List (List Nat)) (caps : List Nat) :
    census order.length (feasible (reorder order rows) caps) =
      census original.length (feasible (reorder original rows) caps) := by
  rw [census_congr _ _ _ (reordered_semantics order rows caps),
      census_congr _ _ _ (reordered_semantics original rows caps),
      ← subsets_census, ← subsets_census]
  exact subsets_perm p _ (fun _ _ h => projectFeasible_perm rows caps h)

theorem range_reconstruct (row : List Nat) :
    (List.range row.length).map (fun i => row[i]?.getD 0) = row := by
  induction row with
  | nil => rfl
  | cons a row ih => simpa [List.range_succ_eq_map, List.map_map] using congrArg (a::·) ih

theorem reorder_identity (rows : List (List Nat)) (n : Nat)
    (shape : ∀ row ∈ rows, row.length = n) : reorder (List.range n) rows = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hr := shape row (by simp)
    have ht := ih (fun r h => shape r (by simp [h]))
    simp only [reorder, List.map_cons] at ht ⊢
    rw [ht, ← hr, range_reconstruct]

/-- The original-coordinate population follows from a checked ordered diagram
and a permutation certificate; source costs are the original literal rows. -/
theorem original_population (c : CheckedNode n) (order : List Nat)
    (rows : List (List Nat)) (caps : List Nat)
    (permutation : List.Perm order (List.range n))
    (shape : ∀ row ∈ rows, row.length = n)
    (source : PrefixEvidence (reorder order rows) caps c.diagram) :
    c.count = census n (feasible rows caps) := by
  have length : order.length = n := by simpa using permutation.length_eq
  have transport := reordered_population permutation rows caps
  rw [length, List.length_range, reorder_identity rows n shape] at transport
  exact (prefix_source_bound_population c source).trans transport

end PerfectPower.PlanningPermutation
