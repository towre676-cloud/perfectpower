import Std

namespace PerfectPower.BlastSourceReplay

def complement (c : Char) : Char :=
  match c with
  | 'A' => 'T' | 'C' => 'G' | 'G' => 'C' | 'T' => 'A'
  | 'R' => 'Y' | 'Y' => 'R' | 'S' => 'S' | 'W' => 'W'
  | 'K' => 'M' | 'M' => 'K' | 'B' => 'V' | 'D' => 'H'
  | 'H' => 'D' | 'V' => 'B' | 'N' => 'N' | 'U' => 'A'
  | _ => c

def segment (source : List Char) (start stop : Nat) : List Char :=
  let chars := (source.drop (min start stop - 1)).take (max start stop - min start stop + 1)
  if stop < start then chars.reverse.map complement else chars

/-- Literal raw BTOP decoder: bounded matching runs, mismatch pairs and gaps. -/
def replay : Nat → List Char → List Char → List Char → Bool
  | 0, _, _, _ => false
  | _ + 1, [], query, subject => query.isEmpty && subject.isEmpty
  | fuel + 1, trace@(a :: rest), query, subject =>
    if a.isDigit then
      let digits := trace.takeWhile Char.isDigit
      let n := digits.foldl (fun value digit => value * 10 + (digit.toNat - 48)) 0
      decide (n ≤ query.length ∧ n ≤ subject.length) &&
        (query.take n == subject.take n) &&
        replay fuel (trace.drop digits.length) (query.drop n) (subject.drop n)
    else
      match rest with
      | [] => false
      | b :: tail =>
        a != b && (a == '-' || a.isUpper) && (b == '-' || b.isUpper) &&
        (a == '-' || query.head? == some a) &&
        (b == '-' || subject.head? == some b) &&
        replay fuel tail (if a == '-' then query else query.drop 1)
          (if b == '-' then subject else subject.drop 1)

/-- Declarative literal-trace semantics, independent of recursion fuel. -/
inductive Valid : List Char → List Char → List Char → Prop
  | done (q s : List Char) (hq : q.isEmpty = true) (hs : s.isEmpty = true) : Valid [] q s
  | matches (a : Char) (rest q s : List Char) (n : Nat)
      (digit : a.isDigit = true)
      (parsed : n = ((a :: rest).takeWhile Char.isDigit).foldl
        (fun value digit => value * 10 + (digit.toNat - 48)) 0)
      (bounds : n ≤ q.length ∧ n ≤ s.length)
      (equal : (q.take n == s.take n) = true)
      (tail : Valid ((a :: rest).drop ((a :: rest).takeWhile Char.isDigit).length)
        (q.drop n) (s.drop n)) : Valid (a :: rest) q s
  | pair (a b : Char) (rest q s : List Char)
      (grammar : (a != b && (a == '-' || a.isUpper) && (b == '-' || b.isUpper)) = true)
      (query : (a == '-' || q.head? == some a) = true)
      (subject : (b == '-' || s.head? == some b) = true)
      (tail : Valid rest (if a == '-' then q else q.drop 1)
        (if b == '-' then s else s.drop 1)) : Valid (a :: b :: rest) q s

/-- A successful executable decoder constructs a declaratively valid traceback. -/
theorem replay_sound (fuel : Nat) (trace q s : List Char)
    (h : replay fuel trace q s = true) : Valid trace q s := by
  induction fuel generalizing trace q s with
  | zero => simp [replay] at h
  | succ fuel ih =>
    cases trace with
    | nil =>
      simp only [replay, Bool.and_eq_true] at h
      exact Valid.done q s h.1 h.2
    | cons a rest =>
      simp only [replay] at h
      split at h
      · rename_i digit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact Valid.matches a rest q s _ digit rfl h.1.1 h.1.2
          (ih _ _ _ h.2)
      · cases rest with
        | nil => simp at h
        | cons b tail =>
          simp only [Bool.and_eq_true] at h
          apply Valid.pair a b tail q s
          · simp only [Bool.and_eq_true]
            exact ⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, h.1.1.1.2⟩
          · exact h.1.1.2
          · exact h.1.2
          · exact ih _ _ _ h.2

structure Input where
  query : String
  subject : String
  qstart : Nat
  qend : Nat
  sstart : Nat
  send : Nat
  trace : String

def accepts (input : Input) : Bool :=
  decide (1 ≤ min input.qstart input.qend ∧ max input.qstart input.qend ≤ input.query.length ∧
    1 ≤ min input.sstart input.send ∧ max input.sstart input.send ≤ input.subject.length) &&
  replay (input.trace.length + 1) input.trace.toList
    (segment input.query.toList input.qstart input.qend)
    (segment input.subject.toList input.sstart input.send)

/-- Acceptance includes successful consumption of both declared source intervals. -/
theorem acceptance_replays (input : Input) (h : accepts input = true) :
    replay (input.trace.length + 1) input.trace.toList
      (segment input.query.toList input.qstart input.qend)
      (segment input.subject.toList input.sstart input.send) = true := by
  exact (Bool.and_eq_true_iff.mp h).2

theorem acceptance_bounds (input : Input) (h : accepts input = true) :
    1 ≤ min input.qstart input.qend ∧ max input.qstart input.qend ≤ input.query.length ∧
    1 ≤ min input.sstart input.send ∧ max input.sstart input.send ≤ input.subject.length := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem acceptance_valid (input : Input) (h : accepts input = true) :
    Valid input.trace.toList (segment input.query.toList input.qstart input.qend)
      (segment input.subject.toList input.sstart input.send) := by
  exact replay_sound _ _ _ _ (acceptance_replays input h)

#print axioms acceptance_replays
#print axioms replay_sound
#print axioms acceptance_bounds
#print axioms acceptance_valid
end PerfectPower.BlastSourceReplay
