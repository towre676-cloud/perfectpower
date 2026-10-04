import Mathlib
namespace PerfectPower.ResidueCover

/-- Every solution survives any exact ring-valued local cover. -/
theorem necessary {R : Type*} [CommRing R] (f : ℤ →+* R) (F : ℤ → ℤ)
    (S : R → R) (hcompat : ∀ x,f (F x)=S (f x)) (d : ℕ) (x y : ℤ)
    (h : y^d=F x) : (f y)^d=S (f x) := by
  rw [← map_pow,h,hcompat]

theorem empty_obstruction {R : Type*} [CommRing R] (f : ℤ →+* R)
    (F : ℤ → ℤ) (S : R → R) (hcompat : ∀ x,f (F x)=S (f x)) (d : ℕ)
    (hempty : ∀ r z,z^d ≠ S r) (x y : ℤ) : y^d ≠ F x := by
  intro h
  exact hempty (f x) (f y) (necessary f F S hcompat d x y h)

/-- Concrete complete prime-power table, checked by the kernel. -/
theorem quartic_mod16 : ∀ r z : ZMod 16,z^2 ≠ 2*r^4+3 := by decide +kernel

/-- The enhanced engine's global obstruction needs no search or height bound. -/
theorem quartic_no_square (x y : ℤ) : y^2 ≠ 2*x^4+3 := by
  intro h
  have hm := congrArg (fun z : ℤ => (z : ZMod 16)) h
  push_cast at hm
  exact quartic_mod16 (x : ZMod 16) (y : ZMod 16) hm

end PerfectPower.ResidueCover
