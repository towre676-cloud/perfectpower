import PerfectPower.BoundedNative

/-! An exact query language over original integer coordinates. Completeness is
inherited from the source population; no global bound is manufactured here. -/
namespace PerfectPower.QueryNative

/-- Polynomial expressions in the original two integer coordinates. -/
inductive Expr where
  | constant (n : Int)
  | x | y
  | add (a b : Expr)
  | mul (a b : Expr)
  | power (a : Expr) (n : Nat)
  deriving Repr, DecidableEq

/-- Interpret an arithmetic expression in exact integer arithmetic. -/
def Expr.eval : Expr → Int × Int → Int
  | .constant n, _ => n
  | .x, p => p.1
  | .y, p => p.2
  | .add a b, p => a.eval p + b.eval p
  | .mul a b, p => a.eval p * b.eval p
  | .power a n, p => a.eval p ^ n

/-- Expand a coefficient list into the query language without changing its meaning. -/
def polynomial : List Int → Expr
  | [] => .constant 0
  | c :: cs => .add (.constant c) (.mul .x (polynomial cs))

theorem polynomial_correct (cs : List Int) (p : Int × Int) :
    (polynomial cs).eval p = PerfectPower.BoundedNative.horner cs p.1 := by
  induction cs <;> simp_all [polynomial, Expr.eval, PerfectPower.BoundedNative.horner]

/-- Sum of coefficient times monomial, starting at the specified exponent. -/
def monomials : List Int → Int → Nat → Int
  | [], _, _ => 0
  | c :: cs, x, n => c * x^n + monomials cs x (n+1)

theorem monomials_horner (cs : List Int) (x : Int) (n : Nat) :
    monomials cs x n = x^n * PerfectPower.BoundedNative.horner cs x := by
  induction cs generalizing n with
  | nil => simp [monomials, PerfectPower.BoundedNative.horner]
  | cons c cs ih =>
    simp [monomials, PerfectPower.BoundedNative.horner, ih, Int.pow_succ,
      Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem polynomial_monomials (cs : List Int) (p : Int × Int) :
    (polynomial cs).eval p = monomials cs p.1 0 := by
  rw [polynomial_correct, monomials_horner]
  simp

/-- Symbolic coordinate substitution, including nonlinear polynomial maps. -/
def Expr.substitute : Expr → Expr → Expr → Expr
  | .constant n, _, _ => .constant n
  | .x, sx, _ => sx
  | .y, _, sy => sy
  | .add a b, sx, sy => .add (a.substitute sx sy) (b.substitute sx sy)
  | .mul a b, sx, sy => .mul (a.substitute sx sy) (b.substitute sx sy)
  | .power a n, sx, sy => .power (a.substitute sx sy) n

theorem substitution_correct (e sx sy : Expr) (p : Int × Int) :
    (e.substitute sx sy).eval p = e.eval (sx.eval p, sy.eval p) := by
  induction e <;> simp_all [Expr.substitute, Expr.eval]

theorem original_equation_pullback (cs : List Int) (d : Nat) (sx sy : Expr)
    (p : Int × Int) :
    (Expr.power sy d).eval p = ((polynomial cs).substitute sx sy).eval p ↔
      (sy.eval p)^d = PerfectPower.BoundedNative.horner cs (sx.eval p) := by
  rw [substitution_correct, polynomial_correct]
  rfl

/-- Boolean combinations of exact arithmetic constraints. -/
inductive Condition where
  | truth | falsity
  | equal (a b : Expr)
  | le (a b : Expr)
  | congruent (a : Expr) (residue modulus : Int)
  | both (a b : Condition)
  | either (a b : Condition)
  | negate (a : Condition)
  deriving Repr, DecidableEq

/-- Mathematical proposition expressed by a condition at a coordinate pair. -/
def Condition.holds : Condition → Int × Int → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .equal a b, p => a.eval p = b.eval p
  | .le a b, p => a.eval p ≤ b.eval p
  | .congruent a r m, p => a.eval p % m = r % m
  | .both a b, p => a.holds p ∧ b.holds p
  | .either a b, p => a.holds p ∨ b.holds p
  | .negate a, p => ¬ a.holds p

/-- Executable Boolean interpreter for the same mathematical condition. -/
def Condition.test : Condition → Int × Int → Bool
  | .truth, _ => true
  | .falsity, _ => false
  | .equal a b, p => decide (a.eval p = b.eval p)
  | .le a b, p => decide (a.eval p ≤ b.eval p)
  | .congruent a r m, p => decide (a.eval p % m = r % m)
  | .both a b, p => a.test p && b.test p
  | .either a b, p => a.test p || b.test p
  | .negate a, p => !(a.test p)

theorem test_correct (c : Condition) (p : Int × Int) : c.test p = true ↔ c.holds p := by
  induction c <;> simp_all [Condition.test, Condition.holds, Bool.eq_false_iff]

/-- Retain admissible original points in their existing order. -/
def restrict (points : List (Int × Int)) (c : Condition) := points.filter c.test

theorem restrict_complete (points : List (Int × Int)) (S : Int × Int → Prop)
    (h : ∀ p, p ∈ points ↔ S p) (c : Condition) (p : Int × Int) :
    p ∈ restrict points c ↔ S p ∧ c.holds p := by
  simp only [restrict, List.mem_filter, test_correct, h]

theorem restrict_composition (points : List (Int × Int)) (a b : Condition) :
    restrict (restrict points a) b = restrict points (.both a b) := by
  simp [restrict, List.filter_filter, Condition.test, Bool.and_comm]

theorem restriction_preserves_identity (points : List (Int × Int)) (c : Condition)
    (i : Nat) (p : Int × Int) (h : (restrict points c)[i]? = some p) : p ∈ points := by
  exact (List.mem_filter.mp (List.mem_of_getElem? h)).1

/-- First zero-based occurrence, or none if the point is absent. -/
def rank {α : Type} [DecidableEq α] (p : α) : List α → Option Nat
  | [] => none
  | a :: rest => if p = a then some 0 else (rank p rest).map Nat.succ

theorem rank_select {α : Type} [DecidableEq α] (p : α) (points : List α) (i : Nat)
    (h : rank p points = some i) : points[i]? = some p := by
  induction points generalizing i with
  | nil => simp [rank] at h
  | cons a rest ih =>
    by_cases e : p = a
    · subst a
      simp [rank] at h
      subst i
      rfl
    · cases hr : rank p rest with
      | none => simp [rank, e, hr] at h
      | some j =>
        simp [rank, e, hr] at h
        subst i
        exact ih j hr

theorem rank_exists_iff {α : Type} [DecidableEq α] (p : α) (points : List α) :
    (∃ i, rank p points = some i) ↔ p ∈ points := by
  induction points with
  | nil => simp [rank]
  | cons a rest ih =>
    by_cases e : p = a
    · simp [rank, e]
    · simp only [List.mem_cons, e, false_or]
      rw [← ih]
      cases hr : rank p rest <;> simp [rank, e, hr]

theorem select_rank {α : Type} [DecidableEq α] (p : α) (points : List α)
    (hn : points.Nodup) (i : Nat) (h : points[i]? = some p) : rank p points = some i := by
  have hm := List.mem_of_getElem? h
  obtain ⟨j, hj⟩ := (rank_exists_iff p points).mpr hm
  have hs := rank_select p points j hj
  have hi : i < points.length := (List.getElem?_eq_some_iff.mp h).1
  have eq : i = j := List.getElem?_inj hi hn (h.trans hs.symm)
  simpa [eq] using hj

theorem query_rank_exists (points : List (Int × Int)) (S : Int × Int → Prop)
    (h : ∀ p, p ∈ points ↔ S p) (c : Condition) (p : Int × Int) :
    (∃ i, rank p (restrict points c) = some i) ↔ S p ∧ c.holds p := by
  rw [rank_exists_iff, restrict_complete points S h]

theorem objective_lower_bound (points : List (Int × Int)) (S : Int × Int → Prop)
    (h : ∀ p, p ∈ points ↔ S p) (objective : Expr) (v : Int)
    (hv : (points.all fun p => decide (v ≤ objective.eval p)) = true)
    (p : Int × Int) (hp : S p) : v ≤ objective.eval p := by
  exact of_decide_eq_true (List.all_eq_true.mp hv p ((h p).mpr hp))

theorem objective_ties_complete (points : List (Int × Int)) (S : Int × Int → Prop)
    (h : ∀ p, p ∈ points ↔ S p) (objective : Expr) (v : Int) (p : Int × Int) :
    p ∈ points.filter (fun q => decide (objective.eval q = v)) ↔
      S p ∧ objective.eval p = v := by
  simp only [List.mem_filter, decide_eq_true_eq, h]

theorem objective_attained (points : List (Int × Int)) (S : Int × Int → Prop)
    (h : ∀ p, p ∈ points ↔ S p) (objective : Expr) (v : Int)
    (p : Int × Int) (hp : p ∈ points) (hv : objective.eval p = v) :
    ∃ q, S q ∧ objective.eval q = v := ⟨p, (h p).mp hp, hv⟩

end PerfectPower.QueryNative
