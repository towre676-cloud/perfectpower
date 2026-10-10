import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact stored-word semantics, dyadic arithmetic and quotient rounding. -/
namespace PerfectPower.CertifiedBinary64
open scoped BigOperators

def dyadic (m e : ℤ) : ℚ := (m:ℚ)*(2:ℚ)^e

def exponent (word : ℕ) := word / 2^52 % 2048
def fraction (word : ℕ) := word % 2^52

def finite (word : ℕ) : Prop := word < 2^64 ∧ exponent word < 2047

def significand (word : ℕ) : ℤ :=
  let m := if exponent word = 0 then fraction word else 2^52+fraction word
  if word < 2^63 then m else -(m:ℤ)

def scale (word : ℕ) : ℤ :=
  if exponent word = 0 then -1074 else (exponent word:ℤ)-1075

def stored (word : ℕ) : ℚ := dyadic (significand word) (scale word)

instance (word : ℕ) : Decidable (finite word) := by unfold finite; infer_instance

def decode (word : ℕ) : Option ℚ := if finite word then some (stored word) else none

theorem decode_finite (word : ℕ) (h : finite word) : decode word=some (stored word) := by
  simp [decode,h]

theorem decode_nonfinite (word : ℕ) (h : ¬finite word) : decode word=none := by
  simp [decode,h]

/-- The integer fields reconstruct every unsigned 64-bit word exactly. -/
theorem fields_reconstruct (word : ℕ) :
    word=(word/2^63)*2^63+exponent word*2^52+fraction word := by
  unfold exponent fraction
  norm_num only [Nat.reducePow] at ⊢
  omega

theorem sign_bound (word : ℕ) (hw : word<2^64) : word/2^63<2 := by
  norm_num only [Nat.reducePow] at hw ⊢
  omega

theorem fraction_bound (word : ℕ) : fraction word<2^52 :=
  Nat.mod_lt _ (by norm_num)

theorem exponent_bound (word : ℕ) : exponent word<2048 :=
  Nat.mod_lt _ (by norm_num)

/-- Shifting powers of two between significand and exponent preserves value. -/
theorem normalize (m e t : ℤ) :
    (m:ℚ)*(2:ℚ)^t*(2:ℚ)^(e-t)=dyadic m e := by
  unfold dyadic
  rw [mul_assoc,← zpow_add₀ (by norm_num : (2:ℚ)≠0)]
  congr 2
  omega

/-- A dyadic root certificate proves an exact rational power. -/
theorem power_sound (m e c k : ℤ) (d : ℕ)
    (hm : m=c^d) (he : e=k*(d:ℤ)) : dyadic m e = (dyadic c k)^d := by
  rw [dyadic,dyadic,hm,he,Int.cast_pow,mul_pow]
  rw [zpow_mul, zpow_natCast]

/-- Exact products can be accumulated as integer significands. -/
theorem product (a b e f : ℤ) :
    dyadic a e * dyadic b f = dyadic (a*b) (e+f) := by
  unfold dyadic
  rw [Int.cast_mul,zpow_add₀ (by norm_num : (2:ℚ)≠0)]
  ring

/-- Alignment to a common scale preserves the complete finite sum. -/
theorem aligned_sum {ι : Type*} (s : Finset ι) (m : ι → ℤ) (shift : ι → ℕ) (E : ℤ) :
    (∑ i ∈ s, dyadic (m i) (E+shift i)) =
      dyadic (∑ i ∈ s, m i*2^(shift i)) E := by
  simp only [dyadic,zpow_add₀ (by norm_num : (2:ℚ)≠0),zpow_natCast,
    Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def roundQuot (n d : ℕ) : ℕ :=
  let q:=n/d
  let r:=n%d
  q + if 2*r>d ∨ (2*r=d ∧ q%2=1) then 1 else 0

theorem round_floor_or_ceil (n d : ℕ) :
    roundQuot n d=n/d ∨ roundQuot n d=n/d+1 := by
  simp only [roundQuot]
  split <;> omega

theorem round_below_half (n d : ℕ) (h : 2*(n%d)<d) : roundQuot n d=n/d := by
  simp only [roundQuot]
  split <;> omega

theorem round_above_half (n d : ℕ) (h : d<2*(n%d)) : roundQuot n d=n/d+1 := by
  simp only [roundQuot]
  split <;> omega

/-- Exact ties select an even integer, at every magnitude. -/
theorem round_tie_even (n d : ℕ) (h : 2*(n%d)=d) : roundQuot n d%2=0 := by
  have hmod := Nat.mod_lt (n/d) (by omega : 0<2)
  simp only [roundQuot]
  split <;> omega

/-- The nearest-integer primitive has at most half a unit of error. -/
theorem round_error (n d : ℕ) (hd : 0<d) :
    |((roundQuot n d:ℕ):ℤ)*(d:ℤ)-(n:ℤ)| * 2 ≤ d := by
  have hr := Nat.mod_lt n hd
  have hdiv := Nat.mod_add_div n d
  have hc : (n:ℤ)=(n%d:ℕ)+ (d:ℤ)*(n/d:ℕ) := by exact_mod_cast hdiv.symm
  simp only [roundQuot]
  generalize hq : n/d=q at *
  generalize hm : n%d=r at *
  split
  · rename_i h
    push_cast
    rw [hc]
    have he : ((q:ℤ)+1)*(d:ℤ)-((r:ℤ)+(d:ℤ)*q) = (d:ℤ)-r := by ring
    rw [he,abs_of_nonneg (by omega)]
    omega
  · rename_i h
    push_cast
    rw [hc]
    have he : ((q:ℤ)+0)*(d:ℤ)-((r:ℤ)+(d:ℤ)*q) = -(r:ℤ) := by ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
    omega

/-- A stored quarter is exactly a rational square. -/
theorem quarter_square : stored 4598175219545276416 = (1/2:ℚ)^2 := by
  norm_num [stored,dyadic,significand,exponent,fraction,scale]

/-- This is the exact stored binary64 value, not decimal 1/10. -/
theorem point_one_exact : stored 4591870180066957722 = (3602879701896397/36028797018963968:ℚ) := by
  norm_num [stored,dyadic,significand,exponent,fraction,scale]

/-- Odd denominator exponent refutes a square for this stored value. -/
theorem point_one_not_square : ¬ ∃ r : ℚ, r^2=stored 4591870180066957722 := by
  rintro ⟨r,h⟩
  rw [point_one_exact] at h
  have hd := congrArg Rat.den h
  have hden : (3602879701896397/36028797018963968:ℚ).den=36028797018963968 := by
    have h := Rat.den_div_eq_of_coprime (a:=3602879701896397) (b:=36028797018963968)
      (by norm_num) (by norm_num [Nat.coprime_iff_gcd_eq_one])
    norm_num only [Int.cast_ofNat] at h ⊢
  rw [Rat.den_pow,hden] at hd
  have hr : (r.den:ℤ)^2=36028797018963968 := by exact_mod_cast hd
  have hn : (0:ℤ)≤r.den := by positivity
  by_cases hs : (r.den:ℤ)≤189812531
  · nlinarith
  · have ht : (189812532:ℤ)≤r.den := by omega
    nlinarith

theorem negative_not_even_power (x : ℚ) (hx : x<0) (k : ℕ) :
    ¬ ∃ r : ℚ, r^(2*k)=x := by
  rintro ⟨r,h⟩
  rw [mul_comm 2 k,pow_mul] at h
  have hp : 0≤(r^k)^2 := sq_nonneg _
  rw [h] at hp
  linarith

theorem infinity_refused : decode 9218868437227405312=none := by
  norm_num [decode,finite,exponent]

theorem negative_zero_exact : decode 9223372036854775808=some 0 := by
  norm_num [decode,finite,stored,dyadic,significand,exponent,fraction,scale]

end PerfectPower.CertifiedBinary64
