import PerfectPower.FibOrbit
import PerfectPower.SqrtTwoOrbit
import PerfectPower.OEISLib

/-!
# OEIS definitions, generated (do not edit)

Written by `python/make_oeis_auto.py` from the committed `.seq` files in `data/oeis/` through the
definition language `python/perfectpower/oeis_dsl.py`.  Each block quotes the entry's name, defines
the entry **from that text** (recurrence with its initial values, rational generating function,
coordinate expression, or set with its domain) at the entry's own offset, and proves it equal to a
coordinate of a quadratic-unit orbit, or, for a set, that it lists the set in increasing order via
a seed certificate of `QuadOrbit`.  OEIS content: CC BY-SA 4.0, The OEIS Foundation.
-/

namespace PerfectPower.OEISAuto

/-- A000032 (generated from its name): «Lucas numbers beginning at 2: L(n) = L(n-1) + L(n-2), L(0) = 2, L(1) = 1.» -/
def A000032 : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | m + 2 => 1 * A000032 (m + 1) + 1 * A000032 (m + 0) + 0

/-- **A000032 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 0). -/
theorem A000032_eq (m : ℕ) : 1 * A000032 (m + 0) + 0 = 1 * PerfectPower.FibOrbit.L (1 * m + 0) + 0 * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A000032 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.FibOrbit.L (1 * m + 0) + 0 * PerfectPower.FibOrbit.F (1 * m + 0)) 1 1 0
    (fun m => by
      show 1 * A000032 (m + 2) + 0 = 1 * (1 * A000032 (m + 1) + 0) + 1 * (1 * A000032 (m + 0) + 0) + 0
      simp only [A000032]; ring)
    (fun m => by
      show 1 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + 0 * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (1 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + 0 * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (1 * PerfectPower.FibOrbit.L (1 * m + 0) + 0 * PerfectPower.FibOrbit.F (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (0) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A000045 (generated from its name): «Fibonacci numbers: F(n) = F(n-1) + F(n-2) with F(0) = 0 and F(1) = 1.» -/
def A000045 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 1 * A000045 (m + 1) + 1 * A000045 (m + 0) + 0

/-- **A000045 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 0). -/
theorem A000045_eq (m : ℕ) : 1 * A000045 (m + 0) + 0 = 0 * PerfectPower.FibOrbit.L (1 * m + 0) + 1 * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A000045 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.FibOrbit.L (1 * m + 0) + 1 * PerfectPower.FibOrbit.F (1 * m + 0)) 1 1 0
    (fun m => by
      show 1 * A000045 (m + 2) + 0 = 1 * (1 * A000045 (m + 1) + 0) + 1 * (1 * A000045 (m + 0) + 0) + 0
      simp only [A000045]; ring)
    (fun m => by
      show 0 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + 1 * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (0 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + 1 * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (0 * PerfectPower.FibOrbit.L (1 * m + 0) + 1 * PerfectPower.FibOrbit.F (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A000129 (generated from its name): «Pell numbers: a(0) = 0, a(1) = 1; for n > 1, a(n) = 2*a(n-1) + a(n-2).» -/
def A000129 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 2 * A000129 (m + 1) + 1 * A000129 (m + 0) + 0

/-- **A000129 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A000129_eq (m : ℕ) : 1 * A000129 (m + 0) + 0 = 0 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A000129 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) 2 1 0
    (fun m => by
      show 1 * A000129 (m + 2) + 0 = 2 * (1 * A000129 (m + 1) + 0) + 1 * (1 * A000129 (m + 0) + 0) + 0
      simp only [A000129]; ring)
    (fun m => by
      show 0 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 2) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 2) + 0) = 2 * (0 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 1) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 1) + 0)) + 1 * (0 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A000204 (generated from its name): «Lucas numbers (beginning with 1): L(n) = L(n-1) + L(n-2) with L(1) = 1, L(2) = 3.» -/
def A000204 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | m + 2 => 1 * A000204 (m + 1) + 1 * A000204 (m + 0) + 0

/-- **A000204 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 1). -/
theorem A000204_eq (m : ℕ) : 2 * A000204 (m + 0) + 0 = 1 * PerfectPower.FibOrbit.L (1 * m + 0) + 5 * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A000204 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.FibOrbit.L (1 * m + 0) + 5 * PerfectPower.FibOrbit.F (1 * m + 0)) 1 1 0
    (fun m => by
      show 2 * A000204 (m + 2) + 0 = 1 * (2 * A000204 (m + 1) + 0) + 1 * (2 * A000204 (m + 0) + 0) + 0
      simp only [A000204]; ring)
    (fun m => by
      show 1 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + 5 * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (1 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + 5 * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (1 * PerfectPower.FibOrbit.L (1 * m + 0) + 5 * PerfectPower.FibOrbit.F (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (5) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001075 (generated from its name): «a(0) = 1, a(1) = 2, a(n) = 4*a(n-1) - a(n-2).» -/
def A001075 : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | m + 2 => 4 * A001075 (m + 1) + (-1) * A001075 (m + 0) + 0

/-- **A001075 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A001075_eq (m : ℕ) : 1 * A001075 (m + 0) + 0 = 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 0 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A001075 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 0 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) 4 (-1) 0
    (fun m => by
      show 1 * A001075 (m + 2) + 0 = 4 * (1 * A001075 (m + 1) + 0) + (-1) * (1 * A001075 (m + 0) + 0) + 0
      simp only [A001075]; ring)
    (fun m => by
      show 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 2) + 0) + 0 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 2) + 0) = 4 * (1 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 1) + 0) + 0 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 0 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (0) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001108 (generated from its name): «a(n)-th triangular number is a square: a(n+1) = 6*a(n) - a(n-1) + 2, with a(0) = 0, a(1) = 1.» -/
def A001108 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 6 * A001108 (m + 1) + (-1) * A001108 (m + 0) + 2

/-- **A001108 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A001108_eq (m : ℕ) : 2 * A001108 (m + 0) + 1 = 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A001108 (m + 0) + 1)
    (g := fun m => 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 2 * A001108 (m + 2) + 1 = 6 * (2 * A001108 (m + 1) + 1) + (-1) * (2 * A001108 (m + 0) + 1) + 0
      simp only [A001108]; ring)
    (fun m => by
      show 1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (1) * hX + (0) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001109 (generated from its name): «a(n)^2 is a triangular number: a(n) = 6*a(n-1) - a(n-2) with a(0)=0, a(1)=1.» -/
def A001109 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 6 * A001109 (m + 1) + (-1) * A001109 (m + 0) + 0

/-- **A001109 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A001109_eq (m : ℕ) : 2 * A001109 (m + 0) + 0 = 0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A001109 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 2 * A001109 (m + 2) + 0 = 6 * (2 * A001109 (m + 1) + 0) + (-1) * (2 * A001109 (m + 0) + 0) + 0
      simp only [A001109]; ring)
    (fun m => by
      show 0 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (0 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001254 (generated from its name): «Squares of Lucas numbers.» -/
def A001254 (m : ℕ) : ℤ := (PerfectPower.FibOrbit.L (1 * m + 0)) ^ 2

/-- A001353 (generated from its name): «a(n) = 4*a(n-1) - a(n-2) with a(0) = 0, a(1) = 1.» -/
def A001353 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 4 * A001353 (m + 1) + (-1) * A001353 (m + 0) + 0

/-- **A001353 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A001353_eq (m : ℕ) : 1 * A001353 (m + 0) + 0 = 0 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A001353 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) 4 (-1) 0
    (fun m => by
      show 1 * A001353 (m + 2) + 0 = 4 * (1 * A001353 (m + 1) + 0) + (-1) * (1 * A001353 (m + 0) + 0) + 0
      simp only [A001353]; ring)
    (fun m => by
      show 0 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 2) + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 2) + 0) = 4 * (0 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 1) + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001519 (generated from its name): «a(n) = 3*a(n-1) - a(n-2) for n >= 2, with a(0) = a(1) = 1.» -/
def A001519 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | m + 2 => 3 * A001519 (m + 1) + (-1) * A001519 (m + 0) + 0

/-- **A001519 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 0). -/
theorem A001519_eq (m : ℕ) : 2 * A001519 (m + 0) + 0 = 1 * PerfectPower.FibOrbit.L (2 * m + 0) + (-1) * PerfectPower.FibOrbit.F (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A001519 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.FibOrbit.L (2 * m + 0) + (-1) * PerfectPower.FibOrbit.F (2 * m + 0)) 3 (-1) 0
    (fun m => by
      show 2 * A001519 (m + 2) + 0 = 3 * (2 * A001519 (m + 1) + 0) + (-1) * (2 * A001519 (m + 0) + 0) + 0
      simp only [A001519]; ring)
    (fun m => by
      show 1 * PerfectPower.FibOrbit.L (2 * (m + 2) + 0) + (-1) * PerfectPower.FibOrbit.F (2 * (m + 2) + 0) = 3 * (1 * PerfectPower.FibOrbit.L (2 * (m + 1) + 0) + (-1) * PerfectPower.FibOrbit.F (2 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.FibOrbit.L (2 * m + 0) + (-1) * PerfectPower.FibOrbit.F (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (1) * hX + ((-1)) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001541 (generated from its name): «a(0) = 1, a(1) = 3; for n > 1, a(n) = 6*a(n-1) - a(n-2).» -/
def A001541 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | m + 2 => 6 * A001541 (m + 1) + (-1) * A001541 (m + 0) + 0

/-- **A001541 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A001541_eq (m : ℕ) : 1 * A001541 (m + 0) + 0 = 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A001541 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 1 * A001541 (m + 2) + 0 = 6 * (1 * A001541 (m + 1) + 0) + (-1) * (1 * A001541 (m + 0) + 0) + 0
      simp only [A001541]; ring)
    (fun m => by
      show 1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 0 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (1) * hX + (0) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001542 (generated from its name): «a(n) = 6*a(n-1) - a(n-2) for n > 1, a(0)=0 and a(1)=2.» -/
def A001542 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | m + 2 => 6 * A001542 (m + 1) + (-1) * A001542 (m + 0) + 0

/-- **A001542 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A001542_eq (m : ℕ) : 1 * A001542 (m + 0) + 0 = 0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A001542 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 1 * A001542 (m + 2) + 0 = 6 * (1 * A001542 (m + 1) + 0) + (-1) * (1 * A001542 (m + 0) + 0) + 0
      simp only [A001542]; ring)
    (fun m => by
      show 0 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (0 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001652 (generated from its name): «a(n) = 6*a(n-1) - a(n-2) + 2 with a(0) = 0, a(1) = 3.» -/
def A001652 : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | m + 2 => 6 * A001652 (m + 1) + (-1) * A001652 (m + 0) + 2

/-- **A001652 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A001652_eq (m : ℕ) : 2 * A001652 (m + 0) + 1 = 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A001652 (m + 0) + 1)
    (g := fun m => 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 2 * A001652 (m + 2) + 1 = 6 * (2 * A001652 (m + 1) + 1) + (-1) * (2 * A001652 (m + 0) + 1) + 0
      simp only [A001652]; ring)
    (fun m => by
      show 1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (1) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001653 (generated from its name): «Numbers k such that 2*k^2 - 1 is a square.» -/
def A001653Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + (-1)}

/-- A001653 as the increasing enumeration of `A001653Set` from offset 1. -/
def A001653 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(1, 1)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = -1`, unit `3 + 2√2`: 1 seed orbit(s), complete. -/
theorem A001653_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 (-1) [(1, 1)] 2 = true := by
  decide +kernel

theorem A001653_order : PerfectPower.OEISLib.orderB 2 3 2 [(1, 1)] = true := by
  decide +kernel

/-- **A001653 lists its defining set in increasing order, from its offset.** -/
theorem A001653_enumerates : PerfectPower.OEISLib.Enumerates A001653 1 A001653Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 (-1) [(1, 1)] 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A001653_cert A001653_order (fun k h => by generalize k ^ 2 = w at h; omega) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A001835 (generated from its name): «a(n) = 4*a(n-1) - a(n-2), with a(0) = 1, a(1) = 1.» -/
def A001835 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | m + 2 => 4 * A001835 (m + 1) + (-1) * A001835 (m + 0) + 0

/-- **A001835 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A001835_eq (m : ℕ) : 1 * A001835 (m + 0) + 0 = 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + (-1) * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A001835 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + (-1) * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) 4 (-1) 0
    (fun m => by
      show 1 * A001835 (m + 2) + 0 = 4 * (1 * A001835 (m + 1) + 0) + (-1) * (1 * A001835 (m + 0) + 0) + 0
      simp only [A001835]; ring)
    (fun m => by
      show 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 2) + 0) + (-1) * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 2) + 0) = 4 * (1 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 1) + 0) + (-1) * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + (-1) * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + ((-1)) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A001906 (generated from its name): «F(2n) = bisection of Fibonacci sequence: a(n) = 3*a(n-1) - a(n-2).» -/
def A001906 (m : ℕ) : ℤ := PerfectPower.FibOrbit.F (2 * m + 0)

/-- The recurrence stated in A001906. -/
theorem A001906_rec (m : ℕ) : A001906 (m + 2) = 3 * A001906 (m + 1) + (-1) * A001906 m := by
  simp only [A001906]
  have h := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (2 * m + 0)).2.1
  rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring,
    show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
  linear_combination (1) * h

/-- A002315 (generated from its name): «NSW numbers: a(n) = 6*a(n-1) - a(n-2); also a(n)^2 - 2*b(n)^2 = -1 with b(n) = A001653(n+1).» -/
def A002315 : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | m + 2 => 6 * A002315 (m + 1) + (-1) * A002315 (m + 0) + 0

/-- **A002315 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A002315_eq (m : ℕ) : 1 * A002315 (m + 0) + 0 = 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A002315 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 1 * A002315 (m + 2) + 0 = 6 * (1 * A002315 (m + 1) + 0) + (-1) * (1 * A002315 (m + 0) + 0) + 0
      simp only [A002315]; ring)
    (fun m => by
      show 1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (1 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (1) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A002878 (generated from its name): «Bisection of Lucas sequence: a(n) = L(2*n+1).» -/
def A002878 (m : ℕ) : ℤ := PerfectPower.FibOrbit.L (2 * m + 1)

/-- A005248 (generated from its name): «Bisection of Lucas numbers: a(n) = L(2*n) = A000032(2*n).» -/
def A005248 (m : ℕ) : ℤ := PerfectPower.FibOrbit.L (2 * m + 0)

/-- A005319 (generated from its name): «a(n) = 6*a(n-1) - a(n-2).» -/
def A005319 : ℕ → ℤ
  | 0 => 0
  | 1 => 4
  | m + 2 => 6 * A005319 (m + 1) + (-1) * A005319 (m + 0) + 0

/-- **A005319 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A005319_eq (m : ℕ) : 1 * A005319 (m + 0) + 0 = 0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A005319 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 1 * A005319 (m + 2) + 0 = 6 * (1 * A005319 (m + 1) + 0) + (-1) * (1 * A005319 (m + 0) + 0) + 0
      simp only [A005319]; ring)
    (fun m => by
      show 0 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * (0 * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (0) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A007598 (generated from its name): «Squared Fibonacci numbers: a(n) = F(n)^2 where F = A000045.» -/
def A007598 (m : ℕ) : ℤ := (PerfectPower.FibOrbit.F (1 * m + 0)) ^ 2

/-- A011944 (generated from its name): «a(n) = 14*a(n-1) - a(n-2) with a(0) = 0, a(1) = 2.» -/
def A011944 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | m + 2 => 14 * A011944 (m + 1) + (-1) * A011944 (m + 0) + 0

/-- **A011944 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A011944_eq (m : ℕ) : 2 * A011944 (m + 0) + 0 = 0 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A011944 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0)) 14 (-1) 0
    (fun m => by
      show 2 * A011944 (m + 2) + 0 = 14 * (2 * A011944 (m + 1) + 0) + (-1) * (2 * A011944 (m + 0) + 0) + 0
      simp only [A011944]; ring)
    (fun m => by
      show 0 * PerfectPower.OEISLib.ox 3 2 1 (2 * (m + 2) + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (2 * (m + 2) + 0) = 14 * (0 * PerfectPower.OEISLib.ox 3 2 1 (2 * (m + 1) + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (2 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A025169 (generated from its name): «a(n) = 2*Fibonacci(2*n+2).» -/
def A025169 (m : ℕ) : ℤ := 2 * PerfectPower.FibOrbit.F (2 * m + 2)

/-- A033888 (generated from its name): «a(n) = Fibonacci(4*n).» -/
def A033888 (m : ℕ) : ℤ := PerfectPower.FibOrbit.F (4 * m + 0)

/-- A033890 (generated from its name): «a(n) = Fibonacci(4*n + 2).» -/
def A033890 (m : ℕ) : ℤ := PerfectPower.FibOrbit.F (4 * m + 2)

/-- A048739 (generated from its name): «Expansion of 1/((1 - x)*(1 - 2*x - x^2)).» -/
def A048739 : ℕ → ℤ := PerfectPower.OEISLib.gf3 [1] 3 (-1) (-1)

/-- **A048739 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A048739_eq (m : ℕ) : 2 * A048739 (m + 0) + 1 = 3 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 4 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0) :=
  PerfectPower.OEISLib.gf3_eq [1] 3 (-1) (-1) 2 1 0 (fun m => 3 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 4 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0))
    (fun m => by
      show 3 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 3) + 0) + 4 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 3) + 0) = 3 * (3 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 2) + 0) + 4 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 2) + 0)) + (-1) * (3 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 1) + 0) + 4 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 1) + 0)) + (-1) * (3 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 4 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) + 1 * (1 - 3 - (-1) - (-1))
      have hX0 := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0)).1
      have hY0 := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0)).1
      have hX1 := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0 + 1)).1
      have hY1 := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0 + 1)).1
      rw [show 1 * (m + 3) + 0 = 1 * m + 0 + 1 + 2 by ring,
        show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring,
        show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      rw [show 1 * m + 0 + 1 + 1 = 1 * m + 0 + 2 by ring] at hX1 hY1
      linear_combination (3) * (hX1 - hX0) + (4) * (hY1 - hY0))
    (fun i hi => by have hi' : i < 4 := hi; interval_cases i <;> decide +kernel) m

/-- A049684 (generated from its name): «a(n) = Fibonacci(2n)^2.» -/
def A049684 (m : ℕ) : ℤ := (PerfectPower.FibOrbit.F (2 * m + 0)) ^ 2

/-- A052454 (generated from its name): «Positive integer values of k such that 10*k^2 - 9 is a square.» -/
def A052454Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + (-9)}

/-- A052454 as the increasing enumeration of `A052454Set` from offset 1. -/
def A052454 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(1, 1), (9, 3), (41, 13)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 10 y^2 = -9`, unit `19 + 6√10`: 3 seed orbit(s), complete. -/
theorem A052454_cert : PerfectPower.QuadOrbit.seedCheck 10 19 6 (-9) [(1, 1), (9, 3), (41, 13)] 18 = true := by
  decide +kernel

theorem A052454_order : PerfectPower.OEISLib.orderB 10 19 6 [(1, 1), (9, 3), (41, 13)] = true := by
  decide +kernel

/-- **A052454 lists its defining set in increasing order, from its offset.** -/
theorem A052454_enumerates : PerfectPower.OEISLib.Enumerates A052454 1 A052454Set :=
  PerfectPower.OEISLib.setsq_enumerates 10 19 6 (-9) [(1, 1), (9, 3), (41, 13)] 18 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A052454_cert A052454_order (fun k h => by generalize k ^ 2 = w at h; omega) 1 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A052530 (generated from its name): «a(n) = 4*a(n-1) - a(n-2), with a(0) = 0, a(1) = 2.» -/
def A052530 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | m + 2 => 4 * A052530 (m + 1) + (-1) * A052530 (m + 0) + 0

/-- **A052530 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A052530_eq (m : ℕ) : 1 * A052530 (m + 0) + 0 = 0 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A052530 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) 4 (-1) 0
    (fun m => by
      show 1 * A052530 (m + 2) + 0 = 4 * (1 * A052530 (m + 1) + 0) + (-1) * (1 * A052530 (m + 0) + 0) + 0
      simp only [A052530]; ring)
    (fun m => by
      show 0 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 2) + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 2) + 0) = 4 * (0 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 1) + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (0) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A052542 (generated from its name): «a(n) = 2*a(n-1) + a(n-2), with a(0) = 1, a(1) = 2, a(2) = 4.» -/
def A052542 : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | m + 3 => 2 * A052542 (m + 2) + 1 * A052542 (m + 1) + 0

/-- **A052542 is an orbit coordinate** of `1 + √2` (from index 1). -/
theorem A052542_eq (m : ℕ) : 1 * A052542 (m + 1) + 0 = 2 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A052542 (m + 1) + 0)
    (g := fun m => 2 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) 2 1 0
    (fun m => by
      show 1 * A052542 (m + 3) + 0 = 2 * (1 * A052542 (m + 2) + 0) + 1 * (1 * A052542 (m + 1) + 0) + 0
      simp only [A052542]; ring)
    (fun m => by
      show 2 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 2) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 2) + 0) = 2 * (2 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 1) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 1) + 0)) + 1 * (2 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (2) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A052995 (generated from its name): «Expansion of 2*x*(1 - x)/(1 - 3*x + x^2).» -/
def A052995 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [0, 2, (-2)] 3 (-1)

/-- **A052995 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 1). -/
theorem A052995_eq (m : ℕ) : 1 * A052995 (m + 1) + 0 = 1 * PerfectPower.FibOrbit.L (2 * m + 0) + 1 * PerfectPower.FibOrbit.F (2 * m + 0) :=
  PerfectPower.OEISLib.gf2_eq [0, 2, (-2)] 3 (-1) 1 0 1 (fun m => 1 * PerfectPower.FibOrbit.L (2 * m + 0) + 1 * PerfectPower.FibOrbit.F (2 * m + 0))
    (fun m => by
      show 1 * PerfectPower.FibOrbit.L (2 * (m + 2) + 0) + 1 * PerfectPower.FibOrbit.F (2 * (m + 2) + 0) = 3 * (1 * PerfectPower.FibOrbit.L (2 * (m + 1) + 0) + 1 * PerfectPower.FibOrbit.F (2 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.FibOrbit.L (2 * m + 0) + 1 * PerfectPower.FibOrbit.F (2 * m + 0)) + 0 * (1 - 3 - (-1))
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (1) * hX + (1) * hY)
    (fun i hi => by have hi' : i < 5 := hi; interval_cases i <;> decide +kernel) m

/-- A067900 (generated from its name): «a(n) = 14*a(n-1) - a(n-2); a(0) = 0, a(1) = 8.» -/
def A067900 : ℕ → ℤ
  | 0 => 0
  | 1 => 8
  | m + 2 => 14 * A067900 (m + 1) + (-1) * A067900 (m + 0) + 0

/-- **A067900 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A067900_eq (m : ℕ) : 1 * A067900 (m + 0) + 0 = 0 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A067900 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0)) 14 (-1) 0
    (fun m => by
      show 1 * A067900 (m + 2) + 0 = 14 * (1 * A067900 (m + 1) + 0) + (-1) * (1 * A067900 (m + 0) + 0) + 0
      simp only [A067900]; ring)
    (fun m => by
      show 0 * PerfectPower.OEISLib.ox 3 2 1 (2 * (m + 2) + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (2 * (m + 2) + 0) = 14 * (0 * PerfectPower.OEISLib.ox 3 2 1 (2 * (m + 1) + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (2 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + 2 * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (0) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A074061 (generated from its name): «Positive integers k such that 24*k^2 - 23 is a square.» -/
def A074061Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 24 * k ^ 2 + (-23)}

/-- A074061 as the increasing enumeration of `A074061Set` from offset 0. -/
def A074061 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 24 5 1 [(1, 1), (19, 4)] (n - 0 + 0)

/-- Seed certificate for `x^2 - 24 y^2 = -23`, unit `5 + 1√24`: 2 seed orbit(s), complete. -/
theorem A074061_cert : PerfectPower.QuadOrbit.seedCheck 24 5 1 (-23) [(1, 1), (19, 4)] 4 = true := by
  decide +kernel

theorem A074061_order : PerfectPower.OEISLib.orderB 24 5 1 [(1, 1), (19, 4)] = true := by
  decide +kernel

/-- **A074061 lists its defining set in increasing order, from its offset.** -/
theorem A074061_enumerates : PerfectPower.OEISLib.Enumerates A074061 0 A074061Set :=
  PerfectPower.OEISLib.setsq_enumerates 24 5 1 (-23) [(1, 1), (19, 4)] 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A074061_cert A074061_order (fun k h => by generalize k ^ 2 = w at h; omega) 1 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 0

/-- A075796 (generated from its name): «Numbers k such that 5*k^2 + 5 is a square.» -/
def A075796Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 5 * k ^ 2 + 5}

/-- A075796 as the increasing enumeration of `A075796Set` from offset 1. -/
def A075796 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 5 9 4 [(5, 2)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 5 y^2 = 5`, unit `9 + 4√5`: 1 seed orbit(s), complete. -/
theorem A075796_cert : PerfectPower.QuadOrbit.seedCheck 5 9 4 5 [(5, 2)] 9 = true := by
  decide +kernel

theorem A075796_order : PerfectPower.OEISLib.orderB 5 9 4 [(5, 2)] = true := by
  decide +kernel

/-- **A075796 lists its defining set in increasing order, from its offset.** -/
theorem A075796_enumerates : PerfectPower.OEISLib.Enumerates A075796 1 A075796Set :=
  PerfectPower.OEISLib.setsq_enumerates 5 9 4 5 [(5, 2)] 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075796_cert A075796_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075835 (generated from its name): «Numbers k such that 13*k^2 + 4 is a square.» -/
def A075835Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 13 * k ^ 2 + 4}

/-- A075835 as the increasing enumeration of `A075835Set` from offset 1. -/
def A075835 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 13 649 180 [(2, 0), (11, 3), (119, 33)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 13 y^2 = 4`, unit `649 + 180√13`: 3 seed orbit(s), complete. -/
theorem A075835_cert : PerfectPower.QuadOrbit.seedCheck 13 649 180 4 [(2, 0), (11, 3), (119, 33)] 360 = true := by
  decide +kernel

theorem A075835_order : PerfectPower.OEISLib.orderB 13 649 180 [(2, 0), (11, 3), (119, 33)] = true := by
  decide +kernel

/-- **A075835 lists its defining set in increasing order, from its offset.** -/
theorem A075835_enumerates : PerfectPower.OEISLib.Enumerates A075835 1 A075835Set :=
  PerfectPower.OEISLib.setsq_enumerates 13 649 180 4 [(2, 0), (11, 3), (119, 33)] 360 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075835_cert A075835_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075836 (generated from its name): «Numbers k such that 10*k^2 + 9 is a square.» -/
def A075836Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + 9}

/-- A075836 as the increasing enumeration of `A075836Set` from offset 1. -/
def A075836 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(3, 0), (7, 2), (13, 4)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 10 y^2 = 9`, unit `19 + 6√10`: 3 seed orbit(s), complete. -/
theorem A075836_cert : PerfectPower.QuadOrbit.seedCheck 10 19 6 9 [(3, 0), (7, 2), (13, 4)] 18 = true := by
  decide +kernel

theorem A075836_order : PerfectPower.OEISLib.orderB 10 19 6 [(3, 0), (7, 2), (13, 4)] = true := by
  decide +kernel

/-- **A075836 lists its defining set in increasing order, from its offset.** -/
theorem A075836_enumerates : PerfectPower.OEISLib.Enumerates A075836 1 A075836Set :=
  PerfectPower.OEISLib.setsq_enumerates 10 19 6 9 [(3, 0), (7, 2), (13, 4)] 18 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075836_cert A075836_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075839 (generated from its name): «Numbers k such that 11*k^2 - 2 is a square.» -/
def A075839Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 11 * k ^ 2 + (-2)}

/-- A075839 as the increasing enumeration of `A075839Set` from offset 1. -/
def A075839 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 11 10 3 [(3, 1)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 11 y^2 = -2`, unit `10 + 3√11`: 1 seed orbit(s), complete. -/
theorem A075839_cert : PerfectPower.QuadOrbit.seedCheck 11 10 3 (-2) [(3, 1)] 4 = true := by
  decide +kernel

theorem A075839_order : PerfectPower.OEISLib.orderB 11 10 3 [(3, 1)] = true := by
  decide +kernel

/-- **A075839 lists its defining set in increasing order, from its offset.** -/
theorem A075839_enumerates : PerfectPower.OEISLib.Enumerates A075839 1 A075839Set :=
  PerfectPower.OEISLib.setsq_enumerates 11 10 3 (-2) [(3, 1)] 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075839_cert A075839_order (fun k h => by generalize k ^ 2 = w at h; omega) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075841 (generated from its name): «Numbers k such that 2*k^2 - 9 is a square.» -/
def A075841Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + (-9)}

/-- A075841 as the increasing enumeration of `A075841Set` from offset 1. -/
def A075841 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(3, 3)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = -9`, unit `3 + 2√2`: 1 seed orbit(s), complete. -/
theorem A075841_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 (-9) [(3, 3)] 6 = true := by
  decide +kernel

theorem A075841_order : PerfectPower.OEISLib.orderB 2 3 2 [(3, 3)] = true := by
  decide +kernel

/-- **A075841 lists its defining set in increasing order, from its offset.** -/
theorem A075841_enumerates : PerfectPower.OEISLib.Enumerates A075841 1 A075841Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 (-9) [(3, 3)] 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075841_cert A075841_order (fun k h => by generalize k ^ 2 = w at h; omega) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075843 (generated from its name): «Numbers k such that 99*k^2 + 1 is a square.» -/
def A075843Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 99 * k ^ 2 + 1}

/-- A075843 as the increasing enumeration of `A075843Set` from offset 0. -/
def A075843 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 99 10 1 [(1, 0)] (n - 0 + 0)

/-- Seed certificate for `x^2 - 99 y^2 = 1`, unit `10 + 1√99`: 1 seed orbit(s), complete. -/
theorem A075843_cert : PerfectPower.QuadOrbit.seedCheck 99 10 1 1 [(1, 0)] 1 = true := by
  decide +kernel

theorem A075843_order : PerfectPower.OEISLib.orderB 99 10 1 [(1, 0)] = true := by
  decide +kernel

/-- **A075843 lists its defining set in increasing order, from its offset.** -/
theorem A075843_enumerates : PerfectPower.OEISLib.Enumerates A075843 0 A075843Set :=
  PerfectPower.OEISLib.setsq_enumerates 99 10 1 1 [(1, 0)] 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075843_cert A075843_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 0

/-- A075844 (generated from its name): «Numbers k such that 11*k^2 + 4 is a square.» -/
def A075844Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 11 * k ^ 2 + 4}

/-- A075844 as the increasing enumeration of `A075844Set` from offset 0. -/
def A075844 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 11 10 3 [(2, 0)] (n - 0 + 0)

/-- Seed certificate for `x^2 - 11 y^2 = 4`, unit `10 + 3√11`: 1 seed orbit(s), complete. -/
theorem A075844_cert : PerfectPower.QuadOrbit.seedCheck 11 10 3 4 [(2, 0)] 6 = true := by
  decide +kernel

theorem A075844_order : PerfectPower.OEISLib.orderB 11 10 3 [(2, 0)] = true := by
  decide +kernel

/-- **A075844 lists its defining set in increasing order, from its offset.** -/
theorem A075844_enumerates : PerfectPower.OEISLib.Enumerates A075844 0 A075844Set :=
  PerfectPower.OEISLib.setsq_enumerates 11 10 3 4 [(2, 0)] 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075844_cert A075844_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 0

/-- A075848 (generated from its name): «Numbers k such that 2*k^2 + 9 is a square.» -/
def A075848Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 9}

/-- A075848 as the increasing enumeration of `A075848Set` from offset 0. -/
def A075848 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(3, 0)] (n - 0 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = 9`, unit `3 + 2√2`: 1 seed orbit(s), complete. -/
theorem A075848_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 9 [(3, 0)] 6 = true := by
  decide +kernel

theorem A075848_order : PerfectPower.OEISLib.orderB 2 3 2 [(3, 0)] = true := by
  decide +kernel

/-- **A075848 lists its defining set in increasing order, from its offset.** -/
theorem A075848_enumerates : PerfectPower.OEISLib.Enumerates A075848 0 A075848Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 9 [(3, 0)] 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075848_cert A075848_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 0

/-- A075869 (generated from its name): «Numbers k such that 5*k^2 - 9 is a square.» -/
def A075869Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 5 * k ^ 2 + (-9)}

/-- A075869 as the increasing enumeration of `A075869Set` from offset 1. -/
def A075869 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 5 9 4 [(6, 3)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 5 y^2 = -9`, unit `9 + 4√5`: 1 seed orbit(s), complete. -/
theorem A075869_cert : PerfectPower.QuadOrbit.seedCheck 5 9 4 (-9) [(6, 3)] 12 = true := by
  decide +kernel

theorem A075869_order : PerfectPower.OEISLib.orderB 5 9 4 [(6, 3)] = true := by
  decide +kernel

/-- **A075869 lists its defining set in increasing order, from its offset.** -/
theorem A075869_enumerates : PerfectPower.OEISLib.Enumerates A075869 1 A075869Set :=
  PerfectPower.OEISLib.setsq_enumerates 5 9 4 (-9) [(6, 3)] 12 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075869_cert A075869_order (fun k h => by generalize k ^ 2 = w at h; omega) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075870 (generated from its name): «Numbers k such that 2*k^2 - 4 is a square.» -/
def A075870Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + (-4)}

/-- A075870 as the increasing enumeration of `A075870Set` from offset 1. -/
def A075870 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(2, 2)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = -4`, unit `3 + 2√2`: 1 seed orbit(s), complete. -/
theorem A075870_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 (-4) [(2, 2)] 4 = true := by
  decide +kernel

theorem A075870_order : PerfectPower.OEISLib.orderB 2 3 2 [(2, 2)] = true := by
  decide +kernel

/-- **A075870 lists its defining set in increasing order, from its offset.** -/
theorem A075870_enumerates : PerfectPower.OEISLib.Enumerates A075870 1 A075870Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 (-4) [(2, 2)] 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075870_cert A075870_order (fun k h => by
    have h1 : k ^ 2 = 2 := by linarith
    rcases le_or_lt |k| 1 with hk | hk <;> nlinarith [abs_nonneg k, sq_abs k]) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A075871 (generated from its name): «Numbers k such that 13*k^2 + 1 is a square.» -/
def A075871Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 13 * k ^ 2 + 1}

/-- A075871 as the increasing enumeration of `A075871Set` from offset 1. -/
def A075871 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 13 649 180 [(1, 0)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 13 y^2 = 1`, unit `649 + 180√13`: 1 seed orbit(s), complete. -/
theorem A075871_cert : PerfectPower.QuadOrbit.seedCheck 13 649 180 1 [(1, 0)] 180 = true := by
  decide +kernel

theorem A075871_order : PerfectPower.OEISLib.orderB 13 649 180 [(1, 0)] = true := by
  decide +kernel

/-- **A075871 lists its defining set in increasing order, from its offset.** -/
theorem A075871_enumerates : PerfectPower.OEISLib.Enumerates A075871 1 A075871Set :=
  PerfectPower.OEISLib.setsq_enumerates 13 649 180 1 [(1, 0)] 180 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A075871_cert A075871_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A077446 (generated from its name): «Numbers k such that 2*k^2 + 14 is a square.» -/
def A077446Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 14}

/-- A077446 as the increasing enumeration of `A077446Set` from offset 1. -/
def A077446 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(4, 1), (8, 5)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = 14`, unit `3 + 2√2`: 2 seed orbit(s), complete. -/
theorem A077446_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 14 [(4, 1), (8, 5)] 7 = true := by
  decide +kernel

theorem A077446_order : PerfectPower.OEISLib.orderB 2 3 2 [(4, 1), (8, 5)] = true := by
  decide +kernel

/-- **A077446 lists its defining set in increasing order, from its offset.** -/
theorem A077446_enumerates : PerfectPower.OEISLib.Enumerates A077446 1 A077446Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 14 [(4, 1), (8, 5)] 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A077446_cert A077446_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A078057 (generated from its name): «Expansion of (1+x)/(1-2*x-x^2).» -/
def A078057 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, 1] 2 1

/-- **A078057 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A078057_eq (m : ℕ) : 1 * A078057 (m + 0) + 0 = 1 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0) :=
  PerfectPower.OEISLib.gf2_eq [1, 1] 2 1 1 0 0 (fun m => 1 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0))
    (fun m => by
      show 1 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 2) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 2) + 0) = 2 * (1 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 1) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 1) + 0)) + 1 * (1 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) + 0 * (1 - 2 - 1)
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (2) * hY)
    (fun i hi => by have hi' : i < 4 := hi; interval_cases i <;> decide +kernel) m

/-- A079291 (generated from its name): «Squares of Pell numbers.» -/
def A079291 (m : ℕ) : ℤ := (PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) ^ 2

/-- A079935 (generated from its name): «a(n) = 4*a(n-1) - a(n-2) with a(1) = 1, a(2) = 3.» -/
def A079935 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | m + 2 => 4 * A079935 (m + 1) + (-1) * A079935 (m + 0) + 0

/-- **A079935 is an orbit coordinate** of `2 + √3` (from index 1). -/
theorem A079935_eq (m : ℕ) : 1 * A079935 (m + 0) + 0 = 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A079935 (m + 0) + 0)
    (g := fun m => 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) 4 (-1) 0
    (fun m => by
      show 1 * A079935 (m + 2) + 0 = 4 * (1 * A079935 (m + 1) + 0) + (-1) * (1 * A079935 (m + 0) + 0) + 0
      simp only [A079935]; ring)
    (fun m => by
      show 1 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 2) + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 2) + 0) = 4 * (1 * PerfectPower.OEISLib.ox 3 2 1 (1 * (m + 1) + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * (m + 1) + 0)) + (-1) * (1 * PerfectPower.OEISLib.ox 3 2 1 (1 * m + 0) + 1 * PerfectPower.OEISLib.oy 3 2 1 (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A080806 (generated from its name): «Positive integer values of n such that 6*n^2-5 is a square.» -/
def A080806Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 6 * k ^ 2 + (-5)}

/-- A080806 as the increasing enumeration of `A080806Set` from offset 1. -/
def A080806 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 6 5 2 [(1, 1), (7, 3)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 6 y^2 = -5`, unit `5 + 2√6`: 2 seed orbit(s), complete. -/
theorem A080806_cert : PerfectPower.QuadOrbit.seedCheck 6 5 2 (-5) [(1, 1), (7, 3)] 4 = true := by
  decide +kernel

theorem A080806_order : PerfectPower.OEISLib.orderB 6 5 2 [(1, 1), (7, 3)] = true := by
  decide +kernel

/-- **A080806 lists its defining set in increasing order, from its offset.** -/
theorem A080806_enumerates : PerfectPower.OEISLib.Enumerates A080806 1 A080806Set :=
  PerfectPower.OEISLib.setsq_enumerates 6 5 2 (-5) [(1, 1), (7, 3)] 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A080806_cert A080806_order (fun k h => by generalize k ^ 2 = w at h; omega) 1 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A082405 (generated from its name): «a(n) = 34*a(n-1) - a(n-2); a(0)=0, a(1)=6.» -/
def A082405 : ℕ → ℤ
  | 0 => 0
  | 1 => 6
  | m + 2 => 34 * A082405 (m + 1) + (-1) * A082405 (m + 0) + 0

/-- **A082405 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A082405_eq (m : ℕ) : 2 * A082405 (m + 0) + 0 = 0 * PerfectPower.SqrtTwoOrbit.A (4 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (4 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A082405 (m + 0) + 0)
    (g := fun m => 0 * PerfectPower.SqrtTwoOrbit.A (4 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (4 * m + 0)) 34 (-1) 0
    (fun m => by
      show 2 * A082405 (m + 2) + 0 = 34 * (2 * A082405 (m + 1) + 0) + (-1) * (2 * A082405 (m + 0) + 0) + 0
      simp only [A082405]; ring)
    (fun m => by
      show 0 * PerfectPower.SqrtTwoOrbit.A (4 * (m + 2) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (4 * (m + 2) + 0) = 34 * (0 * PerfectPower.SqrtTwoOrbit.A (4 * (m + 1) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (4 * (m + 1) + 0)) + (-1) * (0 * PerfectPower.SqrtTwoOrbit.A (4 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (4 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (4 * m + 0)).2.2.2
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (4 * m + 0)).2.2.2
      rw [show 4 * (m + 2) + 0 = 4 * m + 0 + 8 by ring, show 4 * (m + 1) + 0 = 4 * m + 0 + 4 by ring]
      linear_combination (0) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A082651 (generated from its name): «Positive integer values of n such that 5n^2+11 is a square.» -/
def A082651Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 5 * k ^ 2 + 11}

/-- A082651 as the increasing enumeration of `A082651Set` from offset 1. -/
def A082651 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 5 9 4 [(4, 1), (16, 7)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 5 y^2 = 11`, unit `9 + 4√5`: 2 seed orbit(s), complete. -/
theorem A082651_cert : PerfectPower.QuadOrbit.seedCheck 5 9 4 11 [(4, 1), (16, 7)] 13 = true := by
  decide +kernel

theorem A082651_order : PerfectPower.OEISLib.orderB 5 9 4 [(4, 1), (16, 7)] = true := by
  decide +kernel

/-- **A082651 lists its defining set in increasing order, from its offset.** -/
theorem A082651_enumerates : PerfectPower.OEISLib.Enumerates A082651 1 A082651Set :=
  PerfectPower.OEISLib.setsq_enumerates 5 9 4 11 [(4, 1), (16, 7)] 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A082651_cert A082651_order (fun k => ne_of_gt (by positivity)) 1 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A094347 (generated from its name): «a(n) = 14*a(n-1) - a(n-2); a(0) = a(1) = 2.» -/
def A094347 : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | m + 2 => 14 * A094347 (m + 1) + (-1) * A094347 (m + 0) + 0

/-- **A094347 is an orbit coordinate** of `2 + √3` (from index 0). -/
theorem A094347_eq (m : ℕ) : 1 * A094347 (m + 0) + 0 = 2 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + (-3) * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A094347 (m + 0) + 0)
    (g := fun m => 2 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + (-3) * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0)) 14 (-1) 0
    (fun m => by
      show 1 * A094347 (m + 2) + 0 = 14 * (1 * A094347 (m + 1) + 0) + (-1) * (1 * A094347 (m + 0) + 0) + 0
      simp only [A094347]; ring)
    (fun m => by
      show 2 * PerfectPower.OEISLib.ox 3 2 1 (2 * (m + 2) + 0) + (-3) * PerfectPower.OEISLib.oy 3 2 1 (2 * (m + 2) + 0) = 14 * (2 * PerfectPower.OEISLib.ox 3 2 1 (2 * (m + 1) + 0) + (-3) * PerfectPower.OEISLib.oy 3 2 1 (2 * (m + 1) + 0)) + (-1) * (2 * PerfectPower.OEISLib.ox 3 2 1 (2 * m + 0) + (-3) * PerfectPower.OEISLib.oy 3 2 1 (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3x_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_four PerfectPower.OEISLib.s3y_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination (2) * hX + ((-3)) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A106256 (generated from its name): «Numbers n such that 12*n^2 + 13 is a square.» -/
def A106256Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 12 * k ^ 2 + 13}

/-- A106256 as the increasing enumeration of `A106256Set` from offset 1. -/
def A106256 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 12 7 2 [(5, 1), (11, 3)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 12 y^2 = 13`, unit `7 + 2√12`: 2 seed orbit(s), complete. -/
theorem A106256_cert : PerfectPower.QuadOrbit.seedCheck 12 7 2 13 [(5, 1), (11, 3)] 7 = true := by
  decide +kernel

theorem A106256_order : PerfectPower.OEISLib.orderB 12 7 2 [(5, 1), (11, 3)] = true := by
  decide +kernel

/-- **A106256 lists its defining set in increasing order, from its offset.** -/
theorem A106256_enumerates : PerfectPower.OEISLib.Enumerates A106256 1 A106256Set :=
  PerfectPower.OEISLib.setsq_enumerates 12 7 2 13 [(5, 1), (11, 3)] 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A106256_cert A106256_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A128588 (generated from its name): «Expansion of g.f. x*(1+x+x^2)/(1-x-x^2).» -/
def A128588 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [0, 1, 1, 1] 1 1

/-- **A128588 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 2). -/
theorem A128588_eq (m : ℕ) : 1 * A128588 (m + 2) + 0 = 1 * PerfectPower.FibOrbit.L (1 * m + 0) + 3 * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.OEISLib.gf2_eq [0, 1, 1, 1] 1 1 1 0 2 (fun m => 1 * PerfectPower.FibOrbit.L (1 * m + 0) + 3 * PerfectPower.FibOrbit.F (1 * m + 0))
    (fun m => by
      show 1 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + 3 * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (1 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + 3 * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (1 * PerfectPower.FibOrbit.L (1 * m + 0) + 3 * PerfectPower.FibOrbit.F (1 * m + 0)) + 0 * (1 - 1 - 1)
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (3) * hY)
    (fun i hi => by have hi' : i < 6 := hi; interval_cases i <;> decide +kernel) m

/-- A133283 (generated from its name): «Numbers k such that 30*k^2 + 6 is a square.» -/
def A133283Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 30 * k ^ 2 + 6}

/-- A133283 as the increasing enumeration of `A133283Set` from offset 1. -/
def A133283 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 30 11 2 [(6, 1)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 30 y^2 = 6`, unit `11 + 2√30`: 1 seed orbit(s), complete. -/
theorem A133283_cert : PerfectPower.QuadOrbit.seedCheck 30 11 2 6 [(6, 1)] 4 = true := by
  decide +kernel

theorem A133283_order : PerfectPower.OEISLib.orderB 30 11 2 [(6, 1)] = true := by
  decide +kernel

/-- **A133283 lists its defining set in increasing order, from its offset.** -/
theorem A133283_enumerates : PerfectPower.OEISLib.Enumerates A133283 1 A133283Set :=
  PerfectPower.OEISLib.setsq_enumerates 30 11 2 6 [(6, 1)] 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A133283_cert A133283_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A133326 (generated from its name): «Numbers n such that 2*n^2 + 41 is a square.» -/
def A133326Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 41}

/-- A133326 as the increasing enumeration of `A133326Set` from offset 1. -/
def A133326 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(7, 2), (13, 8)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = 41`, unit `3 + 2√2`: 2 seed orbit(s), complete. -/
theorem A133326_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 41 [(7, 2), (13, 8)] 13 = true := by
  decide +kernel

theorem A133326_order : PerfectPower.OEISLib.orderB 2 3 2 [(7, 2), (13, 8)] = true := by
  decide +kernel

/-- **A133326 lists its defining set in increasing order, from its offset.** -/
theorem A133326_enumerates : PerfectPower.OEISLib.Enumerates A133326 1 A133326Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 41 [(7, 2), (13, 8)] 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A133326_cert A133326_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A144797 (generated from its name): «Numbers k such that 2*k^2 + 17 is a square.» -/
def A144797Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 2 * k ^ 2 + 17}

/-- A144797 as the increasing enumeration of `A144797Set` from offset 1. -/
def A144797 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 2 3 2 [(5, 2), (7, 4)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 2 y^2 = 17`, unit `3 + 2√2`: 2 seed orbit(s), complete. -/
theorem A144797_cert : PerfectPower.QuadOrbit.seedCheck 2 3 2 17 [(5, 2), (7, 4)] 8 = true := by
  decide +kernel

theorem A144797_order : PerfectPower.OEISLib.orderB 2 3 2 [(5, 2), (7, 4)] = true := by
  decide +kernel

/-- **A144797 lists its defining set in increasing order, from its offset.** -/
theorem A144797_enumerates : PerfectPower.OEISLib.Enumerates A144797 1 A144797Set :=
  PerfectPower.OEISLib.setsq_enumerates 2 3 2 17 [(5, 2), (7, 4)] 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A144797_cert A144797_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A176981 (generated from its name): «Expansion of 2+(1-2*x)/(-1+2*x+x^2).» -/
def A176981 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, (-2), (-2)] 2 1

/-- **A176981 is an orbit coordinate** of `1 + √2` (from index 1). -/
theorem A176981_eq (m : ℕ) : 1 * A176981 (m + 1) + 0 = 0 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + (-1) * PerfectPower.SqrtTwoOrbit.B (1 * m + 0) :=
  PerfectPower.OEISLib.gf2_eq [1, (-2), (-2)] 2 1 1 0 1 (fun m => 0 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + (-1) * PerfectPower.SqrtTwoOrbit.B (1 * m + 0))
    (fun m => by
      show 0 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 2) + 0) + (-1) * PerfectPower.SqrtTwoOrbit.B (1 * (m + 2) + 0) = 2 * (0 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 1) + 0) + (-1) * PerfectPower.SqrtTwoOrbit.B (1 * (m + 1) + 0)) + 1 * (0 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + (-1) * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) + 0 * (1 - 2 - 1)
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (0) * hX + ((-1)) * hY)
    (fun i hi => by have hi' : i < 5 := hi; interval_cases i <;> decide +kernel) m

/-- A182435 (generated from its name): «a(n) = 6*a(n-1) - a(n-2) - 2 with n>1, a(0)=0, a(1)=1.» -/
def A182435 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => 6 * A182435 (m + 1) + (-1) * A182435 (m + 0) + (-2)

/-- **A182435 is an orbit coordinate** of `1 + √2` (from index 0). -/
theorem A182435_eq (m : ℕ) : 2 * A182435 (m + 0) + (-1) = (-1) * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 2 * A182435 (m + 0) + (-1))
    (g := fun m => (-1) * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) 6 (-1) 0
    (fun m => by
      show 2 * A182435 (m + 2) + (-1) = 6 * (2 * A182435 (m + 1) + (-1)) + (-1) * (2 * A182435 (m + 0) + (-1)) + 0
      simp only [A182435]; ring)
    (fun m => by
      show (-1) * PerfectPower.SqrtTwoOrbit.A (2 * (m + 2) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 2) + 0) = 6 * ((-1) * PerfectPower.SqrtTwoOrbit.A (2 * (m + 1) + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * (m + 1) + 0)) + (-1) * ((-1) * PerfectPower.SqrtTwoOrbit.A (2 * m + 0) + 2 * PerfectPower.SqrtTwoOrbit.B (2 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (2 * m + 0)).2.1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (2 * m + 0)).2.1
      rw [show 2 * (m + 2) + 0 = 2 * m + 0 + 4 by ring, show 2 * (m + 1) + 0 = 2 * m + 0 + 2 by ring]
      linear_combination ((-1)) * hX + (2) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A212804 (generated from its name): «Expansion of (1 - x)/(1 - x - x^2).» -/
def A212804 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, (-1)] 1 1

/-- **A212804 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 0). -/
theorem A212804_eq (m : ℕ) : 2 * A212804 (m + 0) + 0 = 1 * PerfectPower.FibOrbit.L (1 * m + 0) + (-1) * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.OEISLib.gf2_eq [1, (-1)] 1 1 2 0 0 (fun m => 1 * PerfectPower.FibOrbit.L (1 * m + 0) + (-1) * PerfectPower.FibOrbit.F (1 * m + 0))
    (fun m => by
      show 1 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + (-1) * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (1 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + (-1) * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (1 * PerfectPower.FibOrbit.L (1 * m + 0) + (-1) * PerfectPower.FibOrbit.F (1 * m + 0)) + 0 * (1 - 1 - 1)
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + ((-1)) * hY)
    (fun i hi => by have hi' : i < 4 := hi; interval_cases i <;> decide +kernel) m

/-- A215928 (generated from its name): «a(n) = 2*a(n-1) + a(n-2) for n > 2, a(0) = a(1) = 1, a(2) = 2.» -/
def A215928 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | m + 3 => 2 * A215928 (m + 2) + 1 * A215928 (m + 1) + 0

/-- **A215928 is an orbit coordinate** of `1 + √2` (from index 1). -/
theorem A215928_eq (m : ℕ) : 1 * A215928 (m + 1) + 0 = 1 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A215928 (m + 1) + 0)
    (g := fun m => 1 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) 2 1 0
    (fun m => by
      show 1 * A215928 (m + 3) + 0 = 2 * (1 * A215928 (m + 2) + 0) + 1 * (1 * A215928 (m + 1) + 0) + 0
      simp only [A215928]; ring)
    (fun m => by
      show 1 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 2) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 2) + 0) = 2 * (1 * PerfectPower.SqrtTwoOrbit.A (1 * (m + 1) + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * (m + 1) + 0)) + 1 * (1 * PerfectPower.SqrtTwoOrbit.A (1 * m + 0) + 1 * PerfectPower.SqrtTwoOrbit.B (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.A_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_two PerfectPower.SqrtTwoOrbit.B_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (1) * hX + (1) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A239365 (generated from its name): «Numbers n such that 10*n^2+4 is a square.» -/
def A239365Set : Set ℤ := {k | 1 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + 4}

/-- A239365 as the increasing enumeration of `A239365Set` from offset 1. -/
def A239365 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(2, 0)] (n - 1 + 1)

/-- Seed certificate for `x^2 - 10 y^2 = 4`, unit `19 + 6√10`: 1 seed orbit(s), complete. -/
theorem A239365_cert : PerfectPower.QuadOrbit.seedCheck 10 19 6 4 [(2, 0)] 12 = true := by
  decide +kernel

theorem A239365_order : PerfectPower.OEISLib.orderB 10 19 6 [(2, 0)] = true := by
  decide +kernel

/-- **A239365 lists its defining set in increasing order, from its offset.** -/
theorem A239365_enumerates : PerfectPower.OEISLib.Enumerates A239365 1 A239365Set :=
  PerfectPower.OEISLib.setsq_enumerates 10 19 6 4 [(2, 0)] 12 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A239365_cert A239365_order (fun k => ne_of_gt (by positivity)) 1 (by norm_num) 1
    (by decide +kernel) (by decide +kernel) 1

/-- A259131 (generated from its name): «Numbers n such that 13*n^2 + 52 is a square.» -/
def A259131Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 13 * k ^ 2 + 52}

/-- A259131 as the increasing enumeration of `A259131Set` from offset 1. -/
def A259131 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 13 649 180 [(13, 3), (130, 36), (1417, 393)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 13 y^2 = 52`, unit `649 + 180√13`: 3 seed orbit(s), complete. -/
theorem A259131_cert : PerfectPower.QuadOrbit.seedCheck 13 649 180 52 [(13, 3), (130, 36), (1417, 393)] 1298 = true := by
  decide +kernel

theorem A259131_order : PerfectPower.OEISLib.orderB 13 649 180 [(13, 3), (130, 36), (1417, 393)] = true := by
  decide +kernel

/-- **A259131 lists its defining set in increasing order, from its offset.** -/
theorem A259131_enumerates : PerfectPower.OEISLib.Enumerates A259131 1 A259131Set :=
  PerfectPower.OEISLib.setsq_enumerates 13 649 180 52 [(13, 3), (130, 36), (1417, 393)] 1298 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A259131_cert A259131_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A273052 (generated from its name): «Numbers n such that 7*n^2 + 8 is a square.» -/
def A273052Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 7 * k ^ 2 + 8}

/-- A273052 as the increasing enumeration of `A273052Set` from offset 1. -/
def A273052 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 7 8 3 [(6, 2)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 7 y^2 = 8`, unit `8 + 3√7`: 1 seed orbit(s), complete. -/
theorem A273052_cert : PerfectPower.QuadOrbit.seedCheck 7 8 3 8 [(6, 2)] 8 = true := by
  decide +kernel

theorem A273052_order : PerfectPower.OEISLib.orderB 7 8 3 [(6, 2)] = true := by
  decide +kernel

/-- **A273052 lists its defining set in increasing order, from its offset.** -/
theorem A273052_enumerates : PerfectPower.OEISLib.Enumerates A273052 1 A273052Set :=
  PerfectPower.OEISLib.setsq_enumerates 7 8 3 8 [(6, 2)] 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A273052_cert A273052_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A273053 (generated from its name): «Numbers n such that 15*n^2 + 16 is a square.» -/
def A273053Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 15 * k ^ 2 + 16}

/-- A273053 as the increasing enumeration of `A273053Set` from offset 1. -/
def A273053 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 15 4 1 [(4, 0)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 15 y^2 = 16`, unit `4 + 1√15`: 1 seed orbit(s), complete. -/
theorem A273053_cert : PerfectPower.QuadOrbit.seedCheck 15 4 1 16 [(4, 0)] 4 = true := by
  decide +kernel

theorem A273053_order : PerfectPower.OEISLib.orderB 15 4 1 [(4, 0)] = true := by
  decide +kernel

/-- **A273053 lists its defining set in increasing order, from its offset.** -/
theorem A273053_enumerates : PerfectPower.OEISLib.Enumerates A273053 1 A273053Set :=
  PerfectPower.OEISLib.setsq_enumerates 15 4 1 16 [(4, 0)] 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A273053_cert A273053_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A273054 (generated from its name): «Numbers n such that 19*n^2 + 20 is a square.» -/
def A273054Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 19 * k ^ 2 + 20}

/-- A273054 as the increasing enumeration of `A273054Set` from offset 1. -/
def A273054 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 19 170 39 [(18, 4), (96, 22)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 19 y^2 = 20`, unit `170 + 39√19`: 2 seed orbit(s), complete. -/
theorem A273054_cert : PerfectPower.QuadOrbit.seedCheck 19 170 39 20 [(18, 4), (96, 22)] 174 = true := by
  decide +kernel

theorem A273054_order : PerfectPower.OEISLib.orderB 19 170 39 [(18, 4), (96, 22)] = true := by
  decide +kernel

/-- **A273054 lists its defining set in increasing order, from its offset.** -/
theorem A273054_enumerates : PerfectPower.OEISLib.Enumerates A273054 1 A273054Set :=
  PerfectPower.OEISLib.setsq_enumerates 19 170 39 20 [(18, 4), (96, 22)] 174 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A273054_cert A273054_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A288219 (generated from its name): «a(n) = a(n-1) + a(n-2) for n >= 3, where a(0) = 2, a(1) = 4, a(2) = 7.» -/
def A288219 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | m + 3 => 1 * A288219 (m + 2) + 1 * A288219 (m + 1) + 0

/-- **A288219 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 1). -/
theorem A288219_eq (m : ℕ) : 1 * A288219 (m + 1) + 0 = 2 * PerfectPower.FibOrbit.L (1 * m + 0) + 5 * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.QuadOrbit.rec_unique (f := fun m => 1 * A288219 (m + 1) + 0)
    (g := fun m => 2 * PerfectPower.FibOrbit.L (1 * m + 0) + 5 * PerfectPower.FibOrbit.F (1 * m + 0)) 1 1 0
    (fun m => by
      show 1 * A288219 (m + 3) + 0 = 1 * (1 * A288219 (m + 2) + 0) + 1 * (1 * A288219 (m + 1) + 0) + 0
      simp only [A288219]; ring)
    (fun m => by
      show 2 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + 5 * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (2 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + 5 * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (2 * PerfectPower.FibOrbit.L (1 * m + 0) + 5 * PerfectPower.FibOrbit.F (1 * m + 0)) + 0
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (2) * hX + (5) * hY)
    (by decide +kernel) (by decide +kernel) m

/-- A309330 (generated from its name): «Numbers k such that 10*k^2 + 40 is a square.» -/
def A309330Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = 10 * k ^ 2 + 40}

/-- A309330 as the increasing enumeration of `A309330Set` from offset 1. -/
def A309330 (n : ℕ) : ℤ := PerfectPower.OEISLib.interleave 10 19 6 [(20, 6)] (n - 1 + 0)

/-- Seed certificate for `x^2 - 10 y^2 = 40`, unit `19 + 6√10`: 1 seed orbit(s), complete. -/
theorem A309330_cert : PerfectPower.QuadOrbit.seedCheck 10 19 6 40 [(20, 6)] 38 = true := by
  decide +kernel

theorem A309330_order : PerfectPower.OEISLib.orderB 10 19 6 [(20, 6)] = true := by
  decide +kernel

/-- **A309330 lists its defining set in increasing order, from its offset.** -/
theorem A309330_enumerates : PerfectPower.OEISLib.Enumerates A309330 1 A309330Set :=
  PerfectPower.OEISLib.setsq_enumerates 10 19 6 40 [(20, 6)] 38 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A309330_cert A309330_order (fun k => ne_of_gt (by positivity)) 0 (by norm_num) 0
    (by decide +kernel) (by decide +kernel) 1

/-- A373566 (generated from its name): «Expansion of x - 1/(x - 1/(x + 1)).» -/
def A373566 : ℕ → ℤ := PerfectPower.OEISLib.gf2 [1, 2, (-1), (-1)] 1 1

/-- **A373566 is an orbit coordinate** of `φ = (1 + √5)/2` (from index 2). -/
theorem A373566_eq (m : ℕ) : 2 * A373566 (m + 2) + 0 = 3 * PerfectPower.FibOrbit.L (1 * m + 0) + 7 * PerfectPower.FibOrbit.F (1 * m + 0) :=
  PerfectPower.OEISLib.gf2_eq [1, 2, (-1), (-1)] 1 1 2 0 2 (fun m => 3 * PerfectPower.FibOrbit.L (1 * m + 0) + 7 * PerfectPower.FibOrbit.F (1 * m + 0))
    (fun m => by
      show 3 * PerfectPower.FibOrbit.L (1 * (m + 2) + 0) + 7 * PerfectPower.FibOrbit.F (1 * (m + 2) + 0) = 1 * (3 * PerfectPower.FibOrbit.L (1 * (m + 1) + 0) + 7 * PerfectPower.FibOrbit.F (1 * (m + 1) + 0)) + 1 * (3 * PerfectPower.FibOrbit.L (1 * m + 0) + 7 * PerfectPower.FibOrbit.F (1 * m + 0)) + 0 * (1 - 1 - 1)
      have hX := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.L_rec (1 * m + 0)).1
      have hY := (PerfectPower.OEISLib.stride_one PerfectPower.FibOrbit.F_rec (1 * m + 0)).1
      rw [show 1 * (m + 2) + 0 = 1 * m + 0 + 2 by ring, show 1 * (m + 1) + 0 = 1 * m + 0 + 1 by ring]
      linear_combination (3) * hX + (7) * hY)
    (fun i hi => by have hi' : i < 6 := hi; interval_cases i <;> decide +kernel) m

end PerfectPower.OEISAuto
