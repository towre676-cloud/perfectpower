import Mathlib
namespace PerfectPower.IntegralOutputTransport

def run {ι X : Type*} (A : ι → X → X) (x : X) : List ι → X
  | [] => x
  | i::w => run A (A i x) w

theorem quotient_words {ι X Y : Type*} (A : ι → X → X) (B : ι → Y → Y)
    (q : X → Y) (commutes : ∀ i x, q (A i x)=B i (q x))
    (x : X) (w : List ι) : q (run A x w)=run B (q x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simpa only [run,commutes] using ih (A i x)

theorem all_outputs {ι X Y Z : Type*} (A : ι → X → X) (B : ι → Y → Y)
    (q : X → Y) (H : X → Z) (D : Y → Z)
    (commutes : ∀ i x, q (A i x)=B i (q x))
    (readout : ∀ x, H x=D (q x)) (x : X) (w : List ι) :
    H (run A x w)=D (run B (q x) w) := by
  rw [readout,quotient_words A B q commutes]

theorem output_fibre {X Y Z : Type*} (q : X → Y) (lift : Y → X)
    (H : X → Z) (D : Y → Z) (split : ∀ y, q (lift y)=y)
    (readout : ∀ x, H x=D (q x)) (z : Z) :
    (∃ x, H x=z) ↔ ∃ y, D y=z := by
  constructor
  · rintro ⟨x,h⟩
    exact ⟨q x,by rwa [← readout]⟩
  · rintro ⟨y,h⟩
    exact ⟨lift y,by rwa [readout,split]⟩

/-- Includes zero diagonal entries: 0 divides y exactly when y is zero. -/
theorem diagonal_integer_image {ι : Type*} (d y : ι → ℤ) :
    (∀ i, d i ∣ y i) ↔ ∃ t : ι → ℤ, ∀ i, y i=d i*t i := by
  constructor
  · intro h
    choose t ht using h
    exact ⟨t,ht⟩
  · rintro ⟨t,ht⟩
    exact fun i => ⟨t i,ht i⟩

end PerfectPower.IntegralOutputTransport
