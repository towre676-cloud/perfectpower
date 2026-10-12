import Std

/-! Kernel proofs for finite Boolean populations and reduced decision diagrams.
No native_decide, external certificate assumptions, or C++ imports are used.
-/
namespace PerfectPower.PlanningDiagram

def census : Nat → (List Bool → Bool) → Nat
  | 0, f => if f [] then 1 else 0
  | n+1, f => census n (fun xs => f (false::xs)) + census n (fun xs => f (true::xs))

def assignments : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (assignments n).map (false::·) ++ (assignments n).map (true::·)

theorem census_enumerates (n : Nat) (f : List Bool → Bool) :
    census n f = (assignments n).countP f := by
  induction n generalizing f with
  | zero => simp [census, assignments, List.countP_cons, List.countP_nil]
  | succ n ih =>
    simp only [census, assignments, List.countP_append, List.countP_map, ih]
    rfl

theorem census_cardinality (n : Nat) (f : List Bool → Bool) :
    census n f = ((assignments n).filter f).length := by
  rw [census_enumerates, List.countP_eq_length_filter]

theorem assignments_multiplicity (n : Nat) (xs : List Bool) :
    (assignments n).countP (fun ys => decide (ys = xs)) = if xs.length = n then 1 else 0 := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [assignments]
  | succ n ih =>
    cases xs with
    | nil => simp [assignments, List.countP_append, List.countP_map, Function.comp_def]
    | cons bit xs =>
      cases bit <;> simp [assignments, List.countP_append, List.countP_map,
        Function.comp_def, ih, List.cons.injEq]

theorem census_congr (n : Nat) (f g : List Bool → Bool) (h : ∀ xs, f xs = g xs) :
    census n f = census n g := by
  induction n generalizing f g with
  | zero => simp [census, h]
  | succ n ih =>
    simp only [census]
    rw [ih _ _ (fun xs => h (false::xs)), ih _ _ (fun xs => h (true::xs))]

theorem census_congr_length (n : Nat) (f g : List Bool → Bool)
    (h : ∀ xs, xs.length = n → f xs = g xs) : census n f = census n g := by
  induction n generalizing f g with
  | zero => simp [census, h [] rfl]
  | succ n ih =>
    simp only [census]
    rw [ih _ _ (fun xs hx => h (false::xs) (by simp [hx])),
      ih _ _ (fun xs hx => h (true::xs) (by simp [hx]))]

theorem census_false (n : Nat) : census n (fun _ => false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [census, ih]

theorem census_true (n : Nat) : census n (fun _ => true) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [census, ih, Nat.pow_succ, Nat.mul_succ]

theorem census_bound (n : Nat) (f : List Bool → Bool) : census n f ≤ 2^n := by
  induction n generalizing f with
  | zero => simp only [census, Nat.pow_zero]; split <;> decide
  | succ n ih =>
    have h0 := ih (fun xs => f (false::xs))
    have h1 := ih (fun xs => f (true::xs))
    simp only [census, Nat.pow_succ]
    omega

theorem census_skip (n r : Nat) (f : List Bool → Bool) :
    census (n+r) (fun xs => f (xs.drop r)) = 2^r * census n f := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Nat.add_succ, census, List.drop_succ_cons]
    change census (n+r) (fun xs => f (xs.drop r)) +
      census (n+r) (fun xs => f (xs.drop r)) = 2^(r+1) * census n f
    rw [ih]
    simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm (2^r) 2]
    omega

inductive Diagram where
  | reject
  | accept
  | branch (lo hi : Diagram)
  | skip (variables : Nat) (child : Diagram)
deriving Repr

def eval : Diagram → List Bool → Bool
  | .reject, _ => false
  | .accept, _ => true
  | .branch lo hi, xs => if xs.headD false then eval hi xs.tail else eval lo xs.tail
  | .skip r child, xs => eval child (xs.drop r)

inductive Fits : Diagram → Nat → Prop where
  | reject (n) : Fits .reject n
  | accept (n) : Fits .accept n
  | branch {n lo hi} : Fits lo n → Fits hi n → Fits (.branch lo hi) (n+1)
  | skip {n child} (r) : Fits child n → Fits (.skip r child) (n+r)

def weight : Diagram → Nat → Nat
  | .reject, _ => 0
  | .accept, n => 2^n
  | .branch lo hi, n => weight lo (n-1) + weight hi (n-1)
  | .skip r child, n => 2^r * weight child (n-r)

theorem weight_correct {d n} (h : Fits d n) : weight d n = census n (eval d) := by
  induction h with
  | reject n => exact (census_false n).symm
  | accept n => exact (census_true n).symm
  | @branch n lo hi hl hh il ih =>
    simp [weight, census, eval, il, ih]
  | @skip n child r h ih =>
    simp only [weight, Nat.add_sub_cancel, eval]
    rw [ih, census_skip]

theorem weight_bound {d n} (h : Fits d n) : weight d n ≤ 2^n := by
  rw [weight_correct h]
  exact census_bound n _

theorem reduce_equal_branches (d : Diagram) (xs : List Bool) :
    eval (.branch d d) xs = eval (.skip 1 d) xs := by
  simp [eval, List.drop_one]

theorem branch_population_split (n : Nat) (f : List Bool → Bool) :
    census (n+1) f = census n (fun xs => f (false::xs)) + census n (fun xs => f (true::xs)) := rfl

def dot : List Nat → List Bool → Nat
  | [], _ => 0
  | w::ws, xs => (if xs.headD false then w else 0) + dot ws xs.tail

def threshold : List Nat → Nat → Diagram
  | [], _ => .accept
  | w::ws, cap => .branch (threshold ws cap)
      (if w ≤ cap then threshold ws (cap-w) else .reject)

theorem threshold_fits (weights : List Nat) (cap : Nat) :
    Fits (threshold weights cap) weights.length := by
  induction weights generalizing cap with
  | nil => exact Fits.accept 0
  | cons w ws ih =>
    apply Fits.branch (ih cap)
    split
    · exact ih _
    · exact Fits.reject _

theorem threshold_correct (weights : List Nat) (cap : Nat) (xs : List Bool) :
    eval (threshold weights cap) xs = decide (dot weights xs ≤ cap) := by
  induction weights generalizing cap xs with
  | nil => simp [threshold, eval, dot]
  | cons w ws ih =>
    simp only [threshold, eval, dot]
    by_cases hb : xs.headD false = true
    ·
      by_cases hw : w ≤ cap
      · simp only [hb, if_true, hw]
        rw [ih]
        simp only [show dot ws xs.tail ≤ cap-w ↔ w + dot ws xs.tail ≤ cap by omega]
      · simp only [hb, if_true, hw, if_false, eval]
        simp only [show ¬ w + dot ws xs.tail ≤ cap by omega, decide_false]
    · simp only [if_neg hb, Nat.zero_add, ih]

theorem threshold_count (weights : List Nat) (cap : Nat) :
    weight (threshold weights cap) weights.length =
      census weights.length (fun xs => decide (dot weights xs ≤ cap)) := by
  rw [weight_correct (threshold_fits weights cap)]
  exact census_congr _ _ _ (threshold_correct weights cap)

theorem dot_bound (weights : List Nat) (xs : List Bool) : dot weights xs ≤ weights.sum := by
  induction weights generalizing xs with
  | nil => simp [dot]
  | cons w ws ih =>
    have h := ih xs.tail
    simp only [dot, List.sum_cons]
    split <;> omega

theorem dot_prefix (weights : List Nat) (pre xs : List Bool) :
    dot weights (pre++xs) = dot (weights.take pre.length) pre +
      dot (weights.drop pre.length) xs := by
  induction pre generalizing weights with
  | nil => simp [dot]
  | cons bit pre ih =>
    cases weights with
    | nil => simp [dot]
    | cons w weights =>
      cases bit <;> simp [dot, ih, Nat.add_assoc]

theorem dot_zero_prefix (weights : List Nat) (n : Nat) (xs : List Bool) :
    dot weights (List.replicate n false ++ xs) = dot (weights.drop n) xs := by
  induction n generalizing weights with
  | zero => simp
  | succ n ih =>
    cases weights with
    | nil => simp [dot]
    | cons w weights => simp [dot, List.replicate_succ, ih]

def allowedTotal : List Nat → List Nat → Nat → Nat
  | a::rest, g::guard, cap => (if g ≤ cap then a else 0) + allowedTotal rest guard cap
  | _, _, _ => 0

theorem forced_zero_implication (row guard : List Nat) (cap : Nat) (xs : List Bool)
    (lengths : row.length = guard.length) (valid : dot guard xs ≤ cap) :
    dot row xs ≤ allowedTotal row guard cap := by
  induction row generalizing guard xs with
  | nil => simp [dot]
  | cons a rest ih =>
    cases guard with
    | nil => simp at lengths
    | cons g guard =>
      have ht : dot guard xs.tail ≤ cap := by
        simp only [dot] at valid
        omega
      have hl : rest.length = guard.length := by simpa using lengths
      have hi := ih guard xs.tail hl ht
      have hb : (if xs.headD false then a else 0) ≤ (if g ≤ cap then a else 0) := by
        by_cases hg : g ≤ cap
        · simp only [if_pos hg]; split <;> omega
        · by_cases hx : xs.headD false = true
          · simp only [dot, if_pos hx] at valid
            omega
          · simp only [if_neg hx, if_neg hg]; exact Nat.le_refl 0
      simp only [dot, allowedTotal]
      omega

def feasible : List (List Nat) → List Nat → List Bool → Bool
  | [], [], _ => true
  | row::rows, cap::caps, xs => decide (dot row xs ≤ cap) && feasible rows caps xs
  | _, _, _ => false

theorem feasible_member_bound (rows : List (List Nat)) (caps : List Nat) (xs : List Bool)
    (row : List Nat) (cap : Nat) (member : (row,cap) ∈ rows.zip caps)
    (valid : feasible rows caps xs = true) : dot row xs ≤ cap := by
  induction rows generalizing caps with
  | nil => simp at member
  | cons first rows ih =>
    cases caps with
    | nil => simp at member
    | cons bound caps =>
      have hv : decide (dot first xs ≤ bound) = true ∧ feasible rows caps xs = true := by
        simpa only [feasible, Bool.and_eq_true] using valid
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with heq | hm
      · cases heq; exact of_decide_eq_true hv.1
      · exact ih caps hm hv.2

theorem feasible_prefix (rows : List (List Nat)) (caps : List Nat) (pre xs : List Bool)
    (lengths : rows.length = caps.length)
    (h : ∀ row cap, (row,cap) ∈ rows.zip caps → dot (row.take pre.length) pre ≤ cap) :
    feasible rows caps (pre++xs) = feasible (rows.map (fun row => row.drop pre.length))
      (rows.zipWith (fun row cap => cap-dot (row.take pre.length) pre) caps) xs := by
  induction rows generalizing caps with
  | nil => cases caps <;> simp_all [feasible]
  | cons row rows ih =>
    cases caps with
    | nil => simp at lengths
    | cons cap caps =>
      have hc := h row cap (by simp)
      have ht : ∀ r c, (r,c) ∈ rows.zip caps → dot (r.take pre.length) pre ≤ c := by
        intro r c hm
        exact h r c (by simp [hm])
      have hl : rows.length = caps.length := by simpa using lengths
      simp only [feasible, List.map_cons, List.zipWith_cons_cons, dot_prefix, ih caps hl ht]
      simp only [show dot (row.take pre.length) pre + dot (row.drop pre.length) xs ≤ cap ↔
        dot (row.drop pre.length) xs ≤ cap-dot (row.take pre.length) pre by omega]

theorem guard_implies_feasible (rows : List (List Nat)) (caps guard : List Nat)
    (guardCap : Nat) (xs : List Bool) (lengths : rows.length = caps.length)
    (h : ∀ row cap, (row,cap) ∈ rows.zip caps →
      (row = guard ∧ cap = guardCap) ∨
      (row.length = guard.length ∧ allowedTotal row guard guardCap ≤ cap))
    (valid : dot guard xs ≤ guardCap) : feasible rows caps xs = true := by
  induction rows generalizing caps with
  | nil => cases caps <;> simp_all [feasible]
  | cons row rows ih =>
    cases caps with
    | nil => simp at lengths
    | cons cap caps =>
      have hc := h row cap (by simp)
      have hd : dot row xs ≤ cap := by
        rcases hc with heq | hbound
        · rcases heq with ⟨rfl,rfl⟩; exact valid
        · exact Nat.le_trans (forced_zero_implication row guard guardCap xs hbound.1 valid) hbound.2
      have ht : ∀ r c, (r,c) ∈ rows.zip caps →
          (r = guard ∧ c = guardCap) ∨
          (r.length = guard.length ∧ allowedTotal r guard guardCap ≤ c) := by
        intro r c hm
        exact h r c (by simp [hm])
      simp [feasible, hd, ih caps (by simpa using lengths) ht]

theorem all_bounds_feasible (rows : List (List Nat)) (caps : List Nat)
    (h : ∀ row cap, (row,cap) ∈ rows.zip caps → row.sum ≤ cap)
    (lengths : rows.length = caps.length) (xs : List Bool) : feasible rows caps xs = true := by
  induction rows generalizing caps with
  | nil => cases caps <;> simp_all [feasible]
  | cons row rows ih =>
    cases caps with
    | nil => simp at lengths
    | cons cap caps =>
      have hc : row.sum ≤ cap := h row cap (by simp)
      have hd : dot row xs ≤ cap := Nat.le_trans (dot_bound row xs) hc
      have ht : ∀ r c, (r,c) ∈ rows.zip caps → r.sum ≤ c := by
        intro r c hm
        exact h r c (by simp [hm])
      have hl : rows.length = caps.length := by simpa using lengths
      simp [feasible, hd, ih caps ht hl]

theorem unconstrained_population (n : Nat) (rows : List (List Nat)) (caps : List Nat)
    (h : ∀ row cap, (row,cap) ∈ rows.zip caps → row.sum ≤ cap)
    (lengths : rows.length = caps.length) : census n (feasible rows caps) = 2^n := by
  rw [census_congr n _ (fun _ => true) (all_bounds_feasible rows caps h lengths)]
  exact census_true n

def cofactor : Diagram → Bool → Diagram
  | .reject, _ => .reject
  | .accept, _ => .accept
  | .branch lo hi, bit => if bit then hi else lo
  | .skip 0 child, bit => cofactor child bit
  | .skip (r+1) child, _ => .skip r child

theorem cofactor_correct (d : Diagram) (bit : Bool) (xs : List Bool) :
    eval (cofactor d bit) xs = eval d (bit::xs) := by
  induction d with
  | reject => rfl
  | accept => rfl
  | branch lo hi il ih => cases bit <;> rfl
  | skip r child ih => cases r <;> simp [cofactor, eval, ih, List.drop_succ_cons]

def intersect : Nat → Diagram → Diagram → Diagram
  | 0, a, b => if eval a [] && eval b [] then .accept else .reject
  | n+1, a, b => .branch
      (intersect n (cofactor a false) (cofactor b false))
      (intersect n (cofactor a true) (cofactor b true))

theorem intersect_correct (n : Nat) (a b : Diagram) (xs : List Bool)
    (h : xs.length = n) : eval (intersect n a b) xs = (eval a xs && eval b xs) := by
  induction n generalizing a b xs with
  | zero =>
    cases xs with
    | nil => cases ha : eval a [] <;> cases hb : eval b [] <;> simp [intersect, ha, hb, eval]
    | cons bit xs => simp at h
  | succ n ih =>
    cases xs with
    | nil => simp at h
    | cons bit xs =>
      have ht : xs.length = n := by simpa using h
      cases bit <;> simp [intersect, eval, ih _ _ xs ht, cofactor_correct]

theorem intersect_fits (n : Nat) (a b : Diagram) : Fits (intersect n a b) n := by
  induction n generalizing a b with
  | zero => simp only [intersect]; split <;> constructor
  | succ n ih => exact Fits.branch (ih _ _) (ih _ _)

theorem intersect_count (n : Nat) (a b : Diagram) :
    weight (intersect n a b) n = census n (fun xs => eval a xs && eval b xs) := by
  rw [weight_correct (intersect_fits n a b)]
  exact census_congr_length n _ _ (intersect_correct n a b)

def natCensus : Nat → (List Bool → Nat) → Nat
  | 0, f => f []
  | n+1, f => natCensus n (fun xs => f (false::xs)) + natCensus n (fun xs => f (true::xs))

theorem natCensus_congr (n : Nat) (f g : List Bool → Nat) (h : ∀ xs, f xs = g xs) :
    natCensus n f = natCensus n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih =>
    simp only [natCensus]
    rw [ih _ _ (fun xs => h (false::xs)), ih _ _ (fun xs => h (true::xs))]

theorem natCensus_add (n : Nat) (f g : List Bool → Nat) :
    natCensus n (fun xs => f xs + g xs) = natCensus n f + natCensus n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [natCensus, ih]; omega

theorem census_indicator (n : Nat) (f : List Bool → Bool) :
    census n f = natCensus n (fun xs => if f xs then 1 else 0) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [census, natCensus, ih]

inductive Partition where
  | leaf
  | split (coordinate : Nat) (zero one : Partition)
deriving Repr, DecidableEq

def gate (coordinate : Nat) (bit : Bool) (f : List Bool → Nat) (xs : List Bool) : Nat :=
  if xs[coordinate]?.getD false == bit then f xs else 0

def aggregate : Partition → (List Bool → Nat) → List Bool → Nat
  | .leaf, f, xs => f xs
  | .split j zero one, f, xs =>
      aggregate zero (gate j false f) xs + aggregate one (gate j true f) xs

theorem partition_pointwise (tree : Partition) (f : List Bool → Nat) (xs : List Bool) :
    aggregate tree f xs = f xs := by
  induction tree generalizing f with
  | leaf => rfl
  | split j zero one iz io =>
    simp only [aggregate, iz, io]
    cases hb : xs[j]?.getD false <;> simp [gate, hb]

theorem partition_aggregation (n : Nat) (tree : Partition) (f : List Bool → Bool) :
    natCensus n (aggregate tree (fun xs => if f xs then 1 else 0)) = census n f := by
  rw [census_indicator]
  exact natCensus_congr n _ _ (partition_pointwise tree _)

theorem partition_disjoint_cover (tree : Partition) (xs : List Bool) :
    aggregate tree (fun _ => 1) xs = 1 := partition_pointwise tree _ xs

def partitionPaths : Partition → List (List (Nat × Bool))
  | .leaf => [[]]
  | .split j zero one =>
      (partitionPaths zero).map (fun path => (j,false)::path) ++
      (partitionPaths one).map (fun path => (j,true)::path)

def insertCoordinate (pair : Nat × Bool) : List (Nat × Bool) → List (Nat × Bool)
  | [] => [pair]
  | first::rest => if pair.1 ≤ first.1 then pair::first::rest else first::insertCoordinate pair rest

def sortCoordinates : List (Nat × Bool) → List (Nat × Bool)
  | [] => []
  | first::rest => insertCoordinate first (sortCoordinates rest)

def freshCoordinates : Partition → List Nat → Bool
  | .leaf, _ => true
  | .split j zero one, used => !used.contains j &&
      freshCoordinates zero (j::used) && freshCoordinates one (j::used)

def inRange : Partition → Nat → Bool
  | .leaf, _ => true
  | .split j zero one, n => decide (j<n) && inRange zero n && inRange one n

#print axioms partition_aggregation
#print axioms partition_disjoint_cover

#print axioms weight_correct
#print axioms threshold_correct
#print axioms intersect_count

end PerfectPower.PlanningDiagram
