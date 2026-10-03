import PerfectPower.CurveScaling

/-! Explicit coordinate export for a supplied inverse scale, over any commutative ring. -/
namespace PerfectPower.CurveReadout
variable {R : Type*} [CommRing R]

theorem export_coordinates (Z W x y : R) (hinv : W * Z = 1) :
    W ^ 2 * (Z ^ 2 * x) = x ∧ W ^ 3 * (Z ^ 3 * y) = y := by
  constructor
  · calc
      W ^ 2 * (Z ^ 2 * x) = (W * Z) ^ 2 * x := by ring
      _ = x := by rw [hinv]; simp
  · calc
      W ^ 3 * (Z ^ 3 * y) = (W * Z) ^ 3 * y := by ring
      _ = y := by rw [hinv]; simp

/-- Equation transfer with an explicit inverse witness: no primality premise. -/
theorem equation_iff (A B Z W x y : R) (hinv : W * Z = 1) :
    (Z ^ 3 * y) ^ 2 - (Z ^ 2 * x) ^ 3 - (A * Z ^ 4) * (Z ^ 2 * x) - B * Z ^ 6 = 0 ↔
      y ^ 2 - x ^ 3 - A * x - B = 0 := by
  rw [CurveScaling.residual]
  constructor
  · intro h
    have e : W ^ 6 * (Z ^ 6 * (y ^ 2 - x ^ 3 - A*x-B)) = y ^ 2 - x ^ 3 - A*x-B := by
      calc
        _ = (W*Z)^6 * (y ^ 2 - x ^ 3 - A*x-B) := by ring
        _ = _ := by rw [hinv]; simp
    rw [h, mul_zero] at e
    exact e.symm
  · intro h; rw [h, mul_zero]
end PerfectPower.CurveReadout
