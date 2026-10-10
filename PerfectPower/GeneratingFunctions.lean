import Std

/-!
Formal coefficient laws and positive-delay observable transport.
These theorems use Lean's standard library only. They do not verify Python
discovery, JSON parsing, or analytic convergence.
-/
namespace PerfectPower.GeneratingFunctions

def tailAt (q : List Int) (a : Nat → Int) (n : Nat) : Int :=
  ((List.range n).map fun j => q.getD (j+1) 0 * a (n-(j+1))).foldr (·+·) 0

/-- A normalized denominator and the numerator determine every coefficient. -/
theorem rational_coefficients_unique (p q : List Int) (a b : Nat → Int)
    (ha : ∀ n, a n + tailAt q a n = p.getD n 0)
    (hb : ∀ n, b n + tailAt q b n = p.getD n 0) : a = b := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have ht : tailAt q a n = tailAt q b n := by
      unfold tailAt
      congr 1
      apply List.map_congr_left
      intro j hj
      have hj' : j < n := List.mem_range.mp hj
      rw [ih (n-(j+1)) (by omega)]
    have h1 := ha n
    have h2 := hb n
    rw [ht] at h1
    omega

def sumMap {X : Type} (add : X → X → X) (zero : X) (xs : List X) : X :=
  xs.foldr add zero

theorem hom_sum {X Y : Type} (addX : X → X → X) (addY : Y → Y → Y)
    (zeroX : X) (zeroY : Y) (E : X → Y)
    (hzero : E zeroX = zeroY) (hadd : ∀ x y, E (addX x y) = addY (E x) (E y))
    (xs : List X) : E (sumMap addX zeroX xs) = sumMap addY zeroY (xs.map E) := by
  induction xs with
  | nil => exact hzero
  | cons x xs ih =>
    simpa only [sumMap, List.foldr_cons, List.map_cons] using
      (hadd x (sumMap addX zeroX xs)).trans (congrArg (addY (E x)) ih)

def delaySum {X : Type} (add : X → X → X) (zero : X) (d : Nat)
    (A : Nat → X → X) (a : Nat → X) (n : Nat) : X :=
  sumMap add zero ((List.range (min n d)).map fun j => A (j+1) (a (n-(j+1))))

/-- Cost-specific intertwining transports every formal state coefficient. -/
theorem delay_transport {X Y : Type} (addX : X → X → X) (addY : Y → Y → Y)
    (zeroX : X) (zeroY : Y) (E : X → Y)
    (hzero : E zeroX = zeroY) (hadd : ∀ x y, E (addX x y) = addY (E x) (E y))
    (d : Nat) (A : Nat → X → X) (G : Nat → Y → Y)
    (hstep : ∀ c x, E (A c x) = G c (E x))
    (s : X) (a : Nat → X) (b : Nat → Y)
    (ha : ∀ n, a n = addX (if n = 0 then s else zeroX) (delaySum addX zeroX d A a n))
    (hb : ∀ n, b n = addY (if n = 0 then E s else zeroY) (delaySum addY zeroY d G b n)) :
    ∀ n, E (a n) = b n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [ha n, hadd, hb n]
    have hseed : E (if n = 0 then s else zeroX) = if n = 0 then E s else zeroY := by
      split <;> simp_all
    rw [hseed]
    congr 1
    unfold delaySum
    rw [hom_sum addX addY zeroX zeroY E hzero hadd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj' : j < min n d := List.mem_range.mp hj
    have hn : j < n := Nat.lt_of_lt_of_le hj' (Nat.min_le_left n d)
    dsimp
    rw [hstep, ih (n-(j+1)) (by omega)]

/-- A target readout then has the same coefficient at every total cost. -/
theorem output_transport {X Y O : Type} (E : X → Y) (C : X → O) (D : Y → O)
    (a : Nat → X) (b : Nat → Y)
    (hstate : ∀ n, E (a n) = b n) (hreadout : ∀ x, C x = D (E x)) :
    ∀ n, C (a n) = D (b n) := by
  intro n
  rw [hreadout, hstate]

/-- The finite telescope keeps both endpoints in the statement. -/
theorem telescope (g : Nat → Int) (n : Nat) :
    ((List.range n).map fun k => g (k+1)-g k).foldr (·+·) 0 = g n-g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldr_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    have hfold : ∀ (xs : List Int) (v : Int), xs.foldr (·+·) v = xs.foldr (·+·) 0 + v := by
      intro xs v
      induction xs with
      | nil => simp
      | cons x xs ih => simp only [List.foldr_cons]; rw [ih]; omega
    rw [hfold, ih]
    omega

def thetaTail (q : Nat → Nat → Int) (a : Nat → Int) (n : Nat) : Int :=
  ((List.range n).map fun j => q (j+1) (n-(j+1)) * a (n-(j+1))).foldr (·+·) 0

/-- Singular leading coefficients require equality of the corresponding seeds. -/
theorem theta_coefficients_unique (q : Nat → Nat → Int) (p a b : Nat → Int)
    (ha : ∀ n, q 0 n * a n + thetaTail q a n = p n)
    (hb : ∀ n, q 0 n * b n + thetaTail q b n = p n)
    (hseed : ∀ n, q 0 n = 0 → a n = b n) : a = b := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : q 0 n = 0
    · exact hseed n hz
    · have ht : thetaTail q a n = thetaTail q b n := by
        unfold thetaTail
        congr 1
        apply List.map_congr_left
        intro j hj
        have hj' : j < n := List.mem_range.mp hj
        rw [ih (n-(j+1)) (by omega)]
      apply Int.eq_of_mul_eq_mul_left hz
      have h1 := ha n
      have h2 := hb n
      rw [ht] at h1
      omega

namespace WorkedCostQuotient

def addPair (x y : Int × Int) : Int × Int := (x.1+y.1, x.2+y.2)
def encode (x : Int × Int) : Int := x.1+x.2
def source (c : Nat) (x : Int × Int) : Int × Int :=
  if c = 1 then (x.1+x.2, 2*(x.1+x.2)) else if c = 2 then (x.2, x.1) else (0, 0)
def target (c : Nat) (y : Int) : Int :=
  if c = 1 then 3*y else if c = 2 then y else 0

theorem step_preserved (c : Nat) (x : Int × Int) : encode (source c x) = target c (encode x) := by
  by_cases h1 : c = 1
  · simp [source, target, encode, h1]; omega
  · by_cases h2 : c = 2
    · simp [source, target, encode, h1, h2]; omega
    · simp [source, target, encode, h1, h2]

/-- An actual two-state, two-cost quotient preserves every coefficient. -/
theorem all_costs (s : Int × Int) (a : Nat → Int × Int) (b : Nat → Int)
    (ha : ∀ n, a n = addPair (if n = 0 then s else (0, 0))
      (delaySum addPair (0, 0) 2 source a n))
    (hb : ∀ n, b n = (if n = 0 then encode s else 0) +
      delaySum (·+·) 0 2 target b n) : ∀ n, encode (a n) = b n := by
  apply delay_transport addPair (·+·) (0, 0) 0 encode (by rfl) _ 2 source target
    step_preserved s a b ha hb
  intro x y
  simp only [encode, addPair]
  omega

end WorkedCostQuotient

#print axioms rational_coefficients_unique
#print axioms delay_transport
#print axioms theta_coefficients_unique
#print axioms WorkedCostQuotient.all_costs
#print axioms telescope

end PerfectPower.GeneratingFunctions
