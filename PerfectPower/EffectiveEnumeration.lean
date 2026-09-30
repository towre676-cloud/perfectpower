import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# From an effective bound to a complete list; the even-quartic degree-two map

Ported from `expert_push/lean/EffectiveEnumeration.lean` (an uncompiled draft from another
session), with the lift conditions added.

* `enumeration_complete`: **a proved rectangle bound turns a finite search into a complete
  list** of the integral points of `y^2 = x^3 + k`.  This is a bridge, not a bound: no unresolved
  curve gains a bound here.
* `even_quartic_forward`: `v^2 = a u^4 + b u^2 + c` maps to `Y^2 = X^3 + b X^2 + a c X` by
  `X = a u^2`, `Y = a u v`.  **The map has degree two; it is not birational.**
* `even_quartic_lift`: the exact integral lift conditions.  A target point with `X = a u^2`,
  `a u ≠ 0` and `Y = a u v` comes from the source point `(u, v)`; the fibre `u = 0` (target
  `(0, 0)`) is handled separately by `even_quartic_zero_fibre`.  Together with the forward map,
  a complete integral list of the target gives a complete integral list of the source.
-/

namespace PerfectPower.EffectiveEnumeration

/-- The integral points of `y^2 = x^3 + k` in the box `[L, U] × [-V, V]`. -/
def boundedSolutions (k L U V : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc L U ×ˢ Finset.Icc (-V) V).filter (fun p => p.2 ^ 2 = p.1 ^ 3 + k)

theorem mem_boundedSolutions (k L U V x y : ℤ) :
    (x, y) ∈ boundedSolutions k L U V ↔
      (L ≤ x ∧ x ≤ U) ∧ (-V ≤ y ∧ y ≤ V) ∧ y ^ 2 = x ^ 3 + k := by
  simp [boundedSolutions, Finset.mem_product, and_assoc]

/-- **A bound makes the finite search complete.** -/
theorem enumeration_complete (k L U V : ℤ)
    (bound : ∀ x y : ℤ, y ^ 2 = x ^ 3 + k → (L ≤ x ∧ x ≤ U) ∧ (-V ≤ y ∧ y ≤ V)) (x y : ℤ) :
    y ^ 2 = x ^ 3 + k ↔ (x, y) ∈ boundedSolutions k L U V := by
  rw [mem_boundedSolutions]
  exact ⟨fun h => ⟨(bound x y h).1, (bound x y h).2, h⟩, fun h => h.2.2⟩

/-- The degree-two map from the even quartic to the cubic. -/
theorem even_quartic_forward (a b c u v : ℤ) (h : v ^ 2 = a * u ^ 4 + b * u ^ 2 + c) :
    (a * u * v) ^ 2 = (a * u ^ 2) ^ 3 + b * (a * u ^ 2) ^ 2 + a * c * (a * u ^ 2) := by
  calc (a * u * v) ^ 2 = (a * u) ^ 2 * v ^ 2 := by ring
    _ = (a * u) ^ 2 * (a * u ^ 4 + b * u ^ 2 + c) := by rw [h]
    _ = (a * u ^ 2) ^ 3 + b * (a * u ^ 2) ^ 2 + a * c * (a * u ^ 2) := by ring

/-- **The lift.** If `X = a u^2`, `Y = a u v` with `a u ≠ 0` and `(X, Y)` is on the cubic, then
`(u, v)` is on the quartic. -/
theorem even_quartic_lift (a b c u v X Y : ℤ) (hX : X = a * u ^ 2) (hY : Y = a * u * v)
    (hau : a * u ≠ 0) (h : Y ^ 2 = X ^ 3 + b * X ^ 2 + a * c * X) :
    v ^ 2 = a * u ^ 4 + b * u ^ 2 + c := by
  subst hX hY
  have h2 : (a * u) ^ 2 * (v ^ 2 - (a * u ^ 4 + b * u ^ 2 + c)) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3) hau
  · linarith

/-- **The `u = 0` fibre**: source points `(0, v)` with `v^2 = c` all map to `(0, 0)`. -/
theorem even_quartic_zero_fibre (a b c v : ℤ) :
    v ^ 2 = a * 0 ^ 4 + b * 0 ^ 2 + c ↔ v ^ 2 = c := by
  constructor <;> intro h <;> linarith [h]

/-- **Completeness transfers along the map**: if `T` contains every integral point of the cubic,
every integral point `(u, v)` of the quartic has `(a u^2, a u v) ∈ T`; so the quartic's points
are the lifts (`even_quartic_lift`) of `T`'s points, plus the `u = 0` fibre. -/
theorem even_quartic_complete (a b c : ℤ) (T : Set (ℤ × ℤ))
    (hT : ∀ X Y : ℤ, Y ^ 2 = X ^ 3 + b * X ^ 2 + a * c * X → (X, Y) ∈ T) (u v : ℤ)
    (h : v ^ 2 = a * u ^ 4 + b * u ^ 2 + c) : (a * u ^ 2, a * u * v) ∈ T :=
  hT _ _ (even_quartic_forward a b c u v h)

end PerfectPower.EffectiveEnumeration
