import Std

/-! Pure Lean decoding for one uncompressed pp-bdd-trace/1 record. Decompression
and source-header acquisition are deliberately outside this module. -/
namespace PerfectPower.PlanningTraceDecode

def word (a b c d : UInt8) : Nat :=
  a.toNat + 256*b.toNat + 65536*c.toNat + 16777216*d.toNat

theorem word_bound (a b c d : UInt8) : word a b c d < 4294967296 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  unfold word
  omega

def readWord : List UInt8 → Option (Nat × List UInt8)
  | a::b::c::d::rest => some (word a b c d, rest)
  | _ => none

def readWords : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, bytes => some ([], bytes)
  | n+1, bytes => do
      let (w, rest) ← readWord bytes
      let (ws, tail) ← readWords n rest
      pure (w::ws, tail)

theorem readWord_sound (bytes : List UInt8) (w : Nat) (rest : List UInt8)
    (h : readWord bytes = some (w,rest)) :
    bytes.length = 4 + rest.length ∧ w < 4294967296 := by
  cases bytes with
  | nil => cases h
  | cons a bytes =>
    cases bytes with
    | nil => cases h
    | cons b bytes =>
      cases bytes with
      | nil => cases h
      | cons c bytes =>
        cases bytes with
        | nil => cases h
        | cons d bytes =>
          cases h
          exact ⟨by simp; omega, word_bound a b c d⟩

theorem readWords_sound (n : Nat) (bytes : List UInt8) (ws : List Nat) (rest : List UInt8)
    (h : readWords n bytes = some (ws,rest)) :
    ws.length = n ∧ bytes.length = 4*n + rest.length ∧ ∀ w ∈ ws, w < 4294967296 := by
  induction n generalizing bytes ws rest with
  | zero =>
    simp only [readWords, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp
  | succ n ih =>
    simp only [readWords] at h
    cases hw : readWord bytes with
    | none => simp [hw] at h
    | some pair =>
      rcases pair with ⟨w, tail⟩
      cases ht : readWords n tail with
      | none => simp [hw, ht] at h
      | some pair =>
        rcases pair with ⟨words, last⟩
        simp only [hw, ht, bind, Option.bind, pure, Pure.pure, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have first := readWord_sound bytes w tail hw
        have remaining := ih tail words last ht
        refine ⟨by simp [remaining.1], by omega, ?_⟩
        intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact first.2
        · exact remaining.2.2 x member

def join64 (lo hi : Nat) : Nat := lo + 4294967296*hi

theorem join64_bound (lo hi : Nat) (low : lo < 4294967296) (high : hi < 4294967296) :
    join64 lo hi < 18446744073709551616 := by unfold join64; omega

def signed32 (w : Nat) : Int := if w < 2147483648 then (w : Int) else (w : Int)-4294967296

theorem signed32_range (w : Nat) (bound : w < 4294967296) :
    -2147483648 ≤ signed32 w ∧ signed32 w < 2147483648 := by
  unfold signed32
  split <;> omega

inductive Record where
  | node (level lo hi count : Nat)
  | threshold (row level cap result lowProof highProof : Nat)
  | conjunction (left right result lowProof highProof : Nat)
  | stage (row threshold thresholdProof root applyProof count : Nat)
  | finish (root count : Nat)
  deriving Repr, DecidableEq

def fromWords : List Nat → Option Record
  | [1,a,b,c,d,e,0,0] => some (.node a b c (join64 d e))
  | [2,a,b,c,d,e,f,0] => some (.threshold a b c d e f)
  | [3,a,b,c,d,e,0,0] => some (.conjunction a b c d e)
  | [4,a,b,c,d,e,f,g] => some (.stage a b c d e (join64 f g))
  | [5,a,b,c,0,0,0,0] => some (.finish a (join64 b c))
  | _ => none

def readRecord (bytes : List UInt8) : Option (Record × List UInt8) := do
  let (words, rest) ← readWords 8 bytes
  let record ← fromWords words
  pure (record, rest)

theorem readRecord_consumes_32 (bytes : List UInt8) (record : Record) (rest : List UInt8)
    (h : readRecord bytes = some (record,rest)) : bytes.length = 32 + rest.length := by
  unfold readRecord at h
  cases hw : readWords 8 bytes with
  | none => simp [hw] at h
  | some pair =>
    rcases pair with ⟨words, tail⟩
    cases hr : fromWords words with
    | none => simp [hw, hr] at h
    | some value =>
      simp only [hw, hr, bind, Option.bind, pure, Pure.pure, Option.some.injEq,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact (readWords_sound 8 bytes words tail hw).2.1

theorem truncated_record_rejected (bytes : List UInt8) (short : bytes.length < 32) :
    readRecord bytes = none := by
  cases h : readRecord bytes with
  | none => rfl
  | some pair =>
    have length := readRecord_consumes_32 bytes pair.1 pair.2 h
    omega

/-- Literal little-endian allocation: tag 1, level 1, children 1/0, count 2. -/
def fixture : List UInt8 :=
  [1,0,0,0, 1,0,0,0, 1,0,0,0, 0,0,0,0,
   2,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0]

theorem fixture_decode : readRecord fixture = some (.node 1 1 0 2, []) := by decide
theorem signed_negative_fixture : signed32 (word 255 255 255 255) = -1 := by decide
theorem malformed_padding : fromWords [1,1,1,0,2,0,1,0] = none := rfl
theorem unknown_tag : fromWords [6,0,0,0,0,0,0,0] = none := rfl

end PerfectPower.PlanningTraceDecode
