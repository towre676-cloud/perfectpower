import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Reusable, unconditional arithmetic for actual integer-square-root software.
The scaled Newton step is adapted from Mark Dickinson's independent CPython
isqrt proof (mdickinson/snippets, 41ce2d256fef06fb32f24fe7014cfa95173ac5e0).
This module does not assert a theorem about compiled C or Ada machine code.
-/
namespace PerfectPower.ArithmeticWorkflow

theorem square_step (r : ℤ) : (r + 1)^2 = r^2 + 2*r + 1 := by ring

theorem descending_square_step (r : ℤ) : r^2 + (-2*r+1) = (r-1)^2 := by ring

theorem newton_upper (x y q z : ℤ) (hy : 0 ≤ y) (hq : 0 ≤ q) (hz : 0 ≤ z)
    (hfloor : x < q*y+y) (hhalf : q+y ≤ 2*z+1) : x < (z+1)^2 := by
  have hdiff : 0 ≤ 2*z+1-q-y := by omega
  have hsum : 0 ≤ 2*z+3+q+y := by omega
  have hp := mul_nonneg hdiff hsum
  have hs := sq_nonneg (q+1-y)
  have hid : 4*((z+1)^2-x-1) =
      (2*z+1-q-y)*(2*z+3+q+y) + (q+1-y)^2 + 4*(q*y+y-x-1) := by ring
  omega

theorem scaler_le_approx (n m a : ℤ) (hm : 0 < m) (ha : 0 < a)
    (hscale : 4*m^4 ≤ n) (hu : n < 4*m^2*(a+1)^2) : m ≤ a := by
  by_contra h
  have hs : (a+1)^2 ≤ m^2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*m^2 by positivity)
  nlinarith

theorem scaled_newton_lower (n m a q : ℤ) (hm : 0 < m) (ha : 0 < a)
    (hq : 0 ≤ q) (hma : m ≤ a)
    (hl : 4*m^2*(a-1)^2 < n) (hu : n < 4*m^2*(a+1)^2)
    (hf : 4*m*a*q ≤ n) : (m*a+q-1)^2 < n := by
  have hma1 : 1 ≤ m*a := by nlinarith
  have hc : 0 < 4*m*a := by positivity
  have hroot : 0 ≤ m*a+q-1 := by omega
  let c := 4*m*a
  let v := c*(m*a+q-1)
  let w := 4*m^2*a^2+n-4*m^2
  have hv : 0 ≤ v := mul_nonneg (le_of_lt hc) hroot
  have hgap : 0 < (n-4*m^2*(a-1)^2)*(4*m^2*(a+1)^2-n) :=
    mul_pos (by omega) (by omega)
  have hid : 16*m^2*a^2*n-w^2 =
      (n-4*m^2*(a-1)^2)*(4*m^2*(a+1)^2-n) := by dsimp [w]; ring
  have hwv : v ≤ w := by
    have hp := mul_nonneg (show 0 ≤ 4*m by omega) (show 0 ≤ a-m by omega)
    dsimp [v,c,w]
    nlinarith
  have hsq : v^2 ≤ w^2 := by nlinarith
  have hprod : 0 < c^2*(n-(m*a+q-1)^2) := by
    have hid2 : c^2*(n-(m*a+q-1)^2) = 16*m^2*a^2*n-v^2 := by dsimp [c,v]; ring
    omega
  have hnn : 0 ≤ c^2 := sq_nonneg c
  by_contra h
  have hneg : n-(m*a+q-1)^2 ≤ 0 := by omega
  have := mul_nonpos_of_nonneg_of_nonpos hnn hneg
  omega

theorem scaled_newton_step (n m a q : ℤ) (hm : 0 < m) (ha : 0 < a)
    (hq : 0 ≤ q) (hscale : 4*m^4 ≤ n)
    (hl : 4*m^2*(a-1)^2 < n) (hu : n < 4*m^2*(a+1)^2)
    (hfl : 4*m*a*q ≤ n) (hfu : n < 4*m*a*(q+1)) :
    0 < m*a+q ∧ (m*a+q-1)^2 < n ∧ n < (m*a+q+1)^2 := by
  have hma := scaler_le_approx n m a hm ha hscale hu
  have hpos : 0 < m*a+q := by positivity
  have hlow := scaled_newton_lower n m a q hm ha hq hma hl hu hfl
  have hs := sq_nonneg (m*a-q-1)
  have hid : (m*a+q+1)^2-4*m*a*(q+1) = (m*a-q-1)^2 := by ring
  exact ⟨hpos, hlow, by omega⟩


/-- The exact division statement used by the independent CPython isqrt proof.
All divisions are Lean's Euclidean integer division; their divisors are positive. -/
theorem scaled_newton_exact (n m a : ℤ) (hm : 0 < m) (ha : 0 < a)
    (hscale : 4*m^4 ≤ n)
    (hl : (a-1)^2 < n / (4*m^2)) (hu : n / (4*m^2) < (a+1)^2) :
    let b := m*a + n/(4*m*a)
    0 < b ∧ (b-1)^2 < n ∧ n < (b+1)^2 := by
  have hn : 0 ≤ n := le_trans (by positivity) hscale
  have hd : 0 < 4*m^2 := by positivity
  have hc : 0 < 4*m*a := by positivity
  have hdl := Int.mul_ediv_self_le (x := n) (ne_of_gt hd)
  have hdu := Int.lt_mul_ediv_self_add (x := n) hd
  have hmul := mul_le_mul_of_nonneg_left (show (a-1)^2+1 ≤ n/(4*m^2) by omega)
    (le_of_lt hd)
  have hl' : 4*m^2*(a-1)^2 < n := by nlinarith
  have hmul' := mul_le_mul_of_nonneg_left (show n/(4*m^2)+1 ≤ (a+1)^2 by omega)
    (le_of_lt hd)
  have hu' : n < 4*m^2*(a+1)^2 := by nlinarith
  have hfl := Int.mul_ediv_self_le (x := n) (ne_of_gt hc)
  have hfu := Int.lt_mul_ediv_self_add (x := n) hc
  have hq := Int.ediv_nonneg hn (le_of_lt hc)
  apply scaled_newton_step n m a (n/(4*m*a)) hm ha hq hscale hl' hu' hfl
  nlinarith only [hfu]

end PerfectPower.ArithmeticWorkflow
