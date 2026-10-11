import Std

/-! Exact finite graph certificate foundations. No Python correctness is assumed. -/
namespace PerfectPower.GraphCertificates

def total (xs : List Nat) : Nat := xs.foldr (· + ·) 0

theorem total_mul (xs : List Nat) (k : Nat) :
    total (xs.map (fun x => x * k)) = total xs * k := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    simp only [List.map_cons, total, List.foldr_cons] at *
    rw [ih, Nat.add_mul]

def productWeights (xs ys : List Nat) : List Nat :=
  xs.flatMap fun x => ys.map fun y => x * y

theorem total_append (xs ys : List Nat) : total (xs ++ ys) = total xs + total ys := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simpa [total, Nat.add_assoc] using congrArg (x + ·) ih

/-- Exact count multiplication for independent weighted populations. -/
theorem independent_product (xs ys : List Nat) :
    total (productWeights xs ys) = total xs * total ys := by
  induction xs with
  | nil => simp [productWeights, total]
  | cons x xs ih =>
    simp only [productWeights, List.flatMap_cons]
    rw [total_append]
    have h : total (ys.map (fun y => x * y)) = x * total ys := by
      simpa only [Nat.mul_comm] using total_mul ys x
    rw [h]
    change x * total ys + total (productWeights xs ys) = (x + total xs) * total ys
    rw [ih, Nat.add_mul]

/-- A feasible object reaching a universal bound is optimal on its stated carrier. -/
theorem maximum_of_bound {X : Type} (feasible : X → Prop) (value : X → Nat)
    (winner : X) (bound : Nat) (hw : feasible winner)
    (heq : value winner = bound) (hbound : ∀ x, feasible x → value x ≤ bound) :
    feasible winner ∧ ∀ x, feasible x → value x ≤ value winner := by
  constructor
  · exact hw
  · intro x hx
    rw [heq]
    exact hbound x hx

/-- Pointwise capacity bounds accumulate exactly. -/
theorem total_map_le {X : Type} (xs : List X) (f g : X → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : total (xs.map f) ≤ total (xs.map g) := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have hx : f x ≤ g x := h x (by simp)
    have ht : total (xs.map f) ≤ total (xs.map g) := ih (by
      intro y hy
      exact h y (by simp [hy]))
    simpa only [List.map_cons, total, List.foldr_cons] using Nat.add_le_add hx ht

/-- Any supplied cut balance identity plus edge capacities gives weak duality.
The cut balance premise must itself be proved from the flow's conservation laws. -/
theorem cut_upper_bound {E : Type} (cut : List E) (flow capacity : E → Nat)
    (value : Nat) (hbalance : value = total (cut.map flow))
    (hcapacity : ∀ e ∈ cut, flow e ≤ capacity e) :
    value ≤ total (cut.map capacity) := by
  rw [hbalance]
  exact total_map_le cut flow capacity hcapacity

-- Literal finite checks, reduced by the kernel; no native_decide.
def cnfExample (a : Fin 16) : Bool :=
  let x := a.val
  ((x / 1 % 2 == 1) || (x / 2 % 2 == 1)) &&
  ((x / 2 % 2 == 0) || (x / 4 % 2 == 1)) &&
  ((x / 4 % 2 == 1) || (x / 8 % 2 == 1))

theorem cnf_example_count :
    ((List.range 16).filter fun x => cnfExample ⟨x % 16, Nat.mod_lt _ (by decide)⟩).length = 7 := by decide

-- Three variables, two values, each assigned 0 (unassigned), 1 or 2.
def matchingFeasible (a : Fin 27) : Prop :=
  let x := a.val % 3
  let y := a.val / 3 % 3
  let z := a.val / 9 % 3
  (x = 0 ∨ y = 0 ∨ x ≠ y) ∧ (x = 0 ∨ z = 0 ∨ x ≠ z) ∧ (y = 0 ∨ z = 0 ∨ y ≠ z)
instance (a : Fin 27) : Decidable (matchingFeasible a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def matchingValue (a : Fin 27) : Nat :=
  (if a.val % 3 = 0 then 0 else 1) +
  (if a.val / 3 % 3 = 0 then 0 else 1) +
  (if a.val / 9 % 3 = 0 then 0 else 1)
theorem matching_example_optimal :
    matchingFeasible ⟨7, by decide⟩ ∧
    ∀ a : Fin 27, matchingFeasible a → matchingValue a ≤ matchingValue ⟨7, by decide⟩ := by decide

-- Four vertices and five directed arcs, with capacities 3,2,1,2,3.
-- Mixed-radix enumeration covers every capacity-respecting integral arc flow.
def flowFeasible (a : Fin 288) : Prop :=
  let f01 := a.val % 4
  let f02 := a.val / 4 % 3
  let f12 := a.val / 12 % 2
  let f13 := a.val / 24 % 3
  let f23 := a.val / 72 % 4
  f01 = f12 + f13 ∧ f02 + f12 = f23
instance (a : Fin 288) : Decidable (flowFeasible a) := inferInstanceAs (Decidable (_ ∧ _))
def flowValue (a : Fin 288) : Nat := a.val % 4 + a.val / 4 % 3
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem flow_example_optimal :
    flowFeasible ⟨287, by decide⟩ ∧ flowValue ⟨287, by decide⟩ = 5 ∧
    ∀ a : Fin 288, flowFeasible a → flowValue a ≤ 5 := by decide

#print axioms flow_example_optimal

#print axioms independent_product
#print axioms maximum_of_bound
#print axioms cut_upper_bound
#print axioms cnf_example_count
#print axioms matching_example_optimal
end PerfectPower.GraphCertificates
