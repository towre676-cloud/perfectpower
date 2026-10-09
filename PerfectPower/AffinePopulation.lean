import PerfectPower.QueryNative

/-! Exact pullback of complete populations along an integer affine input map. -/
namespace PerfectPower.AffinePopulation

/-- Map an original input to the source equation's coordinate. -/
def encode (a b : Int) (p : Int × Int) : Int × Int := (a*p.1+b,p.2)

/-- Recover the original input; admissibility requires exact divisibility. -/
def decode (a b : Int) (p : Int × Int) : Int × Int := ((p.1-b)/a,p.2)

theorem decode_encode (a b : Int) (ha : a ≠ 0) (p : Int × Int) :
    decode a b (encode a b p) = p := by
  simp [decode, encode, Int.mul_ediv_cancel_left, ha]

theorem encode_decode (a b : Int) (p : Int × Int) (h : a ∣ p.1-b) :
    encode a b (decode a b p) = p := by
  simp [encode, decode, Int.mul_ediv_cancel' h]

theorem encode_injective (a b : Int) (ha : a ≠ 0) :
    ∀ p q, encode a b p = encode a b q → p = q := by
  intro p q h
  have := congrArg (decode a b) h
  simpa [decode_encode a b ha] using this

/-- Filter the exact image condition before dividing coordinates. -/
def pullback (points : List (Int × Int)) (a b : Int) :=
  (points.filter fun p => decide (a ∣ p.1-b)).map (decode a b)

theorem pullback_complete (points : List (Int × Int)) (S : Int × Int → Prop)
    (complete : ∀ p, p ∈ points ↔ S p) (a b : Int) (ha : a ≠ 0) (p : Int × Int) :
    p ∈ pullback points a b ↔ S (encode a b p) := by
  simp only [pullback, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨q, ⟨hq, hd⟩, he⟩
    rw [← he, encode_decode a b q hd]
    exact (complete q).mp hq
  · intro hp
    refine ⟨encode a b p, ⟨(complete _).mpr hp, ?_⟩, decode_encode a b ha p⟩
    simp [encode]

end PerfectPower.AffinePopulation
