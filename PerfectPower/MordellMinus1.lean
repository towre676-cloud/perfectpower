import PerfectPower.DescentBranch

/-!
# `y^2 = x^3 - 1`: the Gaussian pilot of the branch compiler

The earlier certificate (`Descent.tableB`) refused this curve.  Its table requires every
representation `p^2 + q^2 = k^3` (`k ≤ K = 2`) to be `± j^3`, i.e. it assumes the units are `± 1`
and that `y + i`, `y - i` are coprime.  The actual table is

* `k = 1`: `± 1` and the Gaussian units `± i`;
* `k = 2`: `± 2 ± 2i`, the common-factor case (`(1 + i)^6 = -8i` divides `(y + i)(y - i)` when `y`
  is odd, and these entries carry exactly that factor).

**Every Gaussian unit is a cube** (`units_are_cubes`: `i = (-i)^3`, `-i = i^3`, `± 1 = (± 1)^3`), and
**`± 2 ± 2i` are cubes** (`common_factor_cubes`: `2 + 2i = (i - 1)^3`, ...).  So every entry is a
field cube, the branch equations `B (3 A^2 - B^2) = k^3` are reducible, and
`DescentBranch.complete_of_branch` lists every point: only `(1, 0)`.

Here `(c, d)` stands for `c + d i`, and `(c + d i)^3 = (c^3 - 3 c d^2) + (3 c^2 d - d^3) i`.
No coprimality is assumed anywhere: an odd `y` would have to enter through a `k = 2` branch, and
those branches are closed like the others.
-/

namespace PerfectPower.MordellMinus1

/-- Real and imaginary parts of `(c + d i)^3`. -/
def cube (c d : ℤ) : ℤ × ℤ := (c ^ 3 - 3 * c * d ^ 2, 3 * c ^ 2 * d - d ^ 3)

/-- **All four Gaussian units are cubes**: `1 = 1^3`, `-1 = (-1)^3`, `i = (-i)^3`, `-i = i^3`. -/
theorem units_are_cubes :
    cube 1 0 = (1, 0) ∧ cube (-1) 0 = (-1, 0) ∧ cube 0 (-1) = (0, 1) ∧ cube 0 1 = (0, -1) := by
  decide

/-- **The common-factor entries are cubes**: `± 2 ± 2i = (∓ 1 ± i)^3`, e.g. `2 + 2i = (i - 1)^3`. -/
theorem common_factor_cubes :
    cube (-1) 1 = (2, 2) ∧ cube 1 1 = (-2, 2) ∧ cube (-1) (-1) = (2, -2) ∧ cube 1 (-1) = (-2, -2) := by
  decide

/-- **`y^2 = x^3 - 1` has exactly one integral point, `(1, 0)`.** -/
theorem complete (x y : ℤ) : y ^ 2 = x ^ 3 - 1 ↔ (x, y) ∈ ([(1, 0)] : List (ℤ × ℤ)) :=
  DescentBranch.complete_of_branch 1 (by norm_num) 1 1 (by norm_num) (by norm_num) 2 2
    (by norm_num) (by norm_num)
    [(1, 0, (-1), 0, 1, 1), (1, 1, 0, 1, 0, 1), (1, (-1), 0, (-1), 0, 1), (1, 0, 1, 0, (-1), 1),
      (2, 2, (-2), (-1), (-1), 1), (2, (-2), (-2), 1, (-1), 1), (2, 2, 2, (-1), 1, 1),
      (2, (-2), 2, 1, 1, 1)]
    []
    [0]
    [(1, 0)]
    (by decide +kernel) (by decide +kernel) x y

theorem points_iff (x y : ℤ) : y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0 := by
  rw [complete]; simp

end PerfectPower.MordellMinus1
