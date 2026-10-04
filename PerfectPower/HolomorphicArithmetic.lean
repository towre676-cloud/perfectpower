import Mathlib.Tactic

/-! Integer regularity calculations for the cyclic differential-basis constructor.
These prove the valuation arithmetic, not the existence of analytic local parameters. -/
namespace PerfectPower.HolomorphicArithmetic

/-- The ramification gcd divides the remainder in the local order formula. -/
theorem gcd_dvd_remainder (n e j : ℕ) : Nat.gcd n e ∣ (j*e)%n := by
  exact (Nat.dvd_mod_iff (Nat.gcd_dvd_left n e)).mpr
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_right n e) j)

/-- Clearing the positive ramification denominator proves absence of a finite pole. -/
theorem finite_regular_numerator (n e j : ℕ) (hn : 0 < n) :
    j*e + Nat.gcd n e ≤ n*(j*e/n)+n := by
  have hr := Nat.mod_lt (j*e) hn
  have hg : 0 < Nat.gcd n e := Nat.gcd_pos_of_pos_left e hn
  have hd : Nat.gcd n e ∣ n-(j*e)%n :=
    Nat.dvd_sub (Nat.gcd_dvd_left n e) (gcd_dvd_remainder n e j)
  have hp : 0 < n-(j*e)%n := Nat.sub_pos_of_lt hr
  have hl := Nat.le_of_dvd hp hd
  have heq := Nat.mod_add_div (j*e) n
  omega

/-- A cleared-denominator version of the infinity regularity condition. -/
theorem infinity_regular_iff (n M A delta i j : ℕ) (hn : 0 < n) :
    n*(A+i)+n+delta ≤ j*M ↔ i+1 ≤ (j*M-n*A-delta)/n := by
  have he : n*(A+i)+n+delta = n*A+(i+1)*n+delta := by ring
  rw [he, Nat.le_div_iff_mul_le hn]
  constructor
  · intro h
    omega
  · intro h
    have hp : n ≤ (i+1)*n := by nlinarith
    omega

/-- Multiplying a regular numerator by x^i adds nonnegative finite order. -/
theorem extra_zero_order (base step i : ℤ) (hb : 0 ≤ base) (hs : 0 ≤ step)
    (hi : 0 ≤ i) : 0 ≤ base+step*i := by positivity

def characterDimension (n : ℕ) (es : List ℕ) (j : ℕ) : ℕ :=
  (j*es.sum - n*(es.map (fun e => j*e/n)).sum - Nat.gcd n es.sum)/n

def basisDimension (n : ℕ) (es : List ℕ) : ℕ :=
  ((List.range n).map (characterDimension n es)).sum

def ramificationGenus (n : ℕ) (es : List ℕ) : ℕ :=
  ((es.map (fun e => n-Nat.gcd n e)).sum + n-Nat.gcd n es.sum + 2 - 2*n)/2

end PerfectPower.HolomorphicArithmetic
