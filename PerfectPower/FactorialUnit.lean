import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact factorial units and the residue-block algorithm. No analytic premise. -/
namespace PerfectPower.FactorialUnit
open scoped BigOperators

/-- Product of the positive integers at most n that are not divisible by p. -/
def nonmultiples (p n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if p ∣ i+1 then 1 else i+1

theorem stripped_step (p n : ℕ) (hp : p.Prime) :
    ordCompl[p] n.factorial = nonmultiples p n * ordCompl[p] (n/p).factorial := by
  induction n with
  | zero => simp [nonmultiples]
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.ordCompl_mul, ih]
    unfold nonmultiples
    rw [Finset.prod_range_succ]
    by_cases hd : p ∣ n+1
    · have hs : ordCompl[p] (n+1) = ordCompl[p] ((n+1)/p) := by
        conv_lhs => rw [← Nat.mul_div_cancel' hd]
        rw [Nat.ordCompl_mul]
        simp [hp.factorization, Nat.div_self hp.pos]
      rw [if_pos hd, Nat.succ_div_of_dvd hd, Nat.factorial_succ,
        Nat.ordCompl_mul, hs, Nat.succ_div_of_dvd hd]
      ac_rfl
    · have hs : ordCompl[p] (n+1) = n+1 := by
        simp [Nat.factorization_eq_zero_of_not_dvd hd]
      rw [if_neg hd, Nat.succ_div_of_not_dvd hd, hs]
      ac_rfl

theorem periodic_shift {R : Type*} (f : ℕ → R) (M : ℕ)
    (periodic : ∀ i, f (i+M)=f i) (q i : ℕ) : f (q*M+i)=f i := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul]
    have he : q*M+M+i=(q*M+i)+M := by omega
    rw [he, periodic, ih]

theorem periodic_product {R : Type*} [CommMonoid R] (f : ℕ → R) (M n : ℕ)
    (periodic : ∀ i, f (i+M)=f i) :
    (∏ i ∈ Finset.range n, f i) =
      (∏ i ∈ Finset.range M, f i)^(n/M) * ∏ i ∈ Finset.range (n%M), f i := by
  have hblocks : ∀ q, (∏ i ∈ Finset.range (q*M), f i) =
      (∏ i ∈ Finset.range M, f i)^q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact periodic_shift f M periodic q i
  have hn : n=(n/M)*M+n%M := by rw [Nat.mul_comm, Nat.div_add_mod]
  conv_lhs => rw [hn]
  rw [Finset.prod_range_add, hblocks]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact periodic_shift f M periodic (n/M) i

/-- One prime-free residue factor, indexed from zero. -/
def factor (p M i : ℕ) : ZMod M := if p ∣ i+1 then 1 else (i+1 : ℕ)
/-- Residue product of the first n prime-free factors. -/
def unitPrefix (p M n : ℕ) : ZMod M := ∏ i ∈ Finset.range n, factor p M i

/-- Structurally recursive binary powering; unused fuel is never traversed. -/
def fastPowFuel {R : Type*} [CommMonoid R] (x : R) : ℕ → ℕ → R
  | 0, _ => 1
  | fuel+1, n => if n=0 then 1 else
      let t := fastPowFuel x fuel (n/2)
      t*t*(if n%2=0 then 1 else x)

theorem fastPowFuel_correct {R : Type*} [CommMonoid R] (x : R) (fuel n : ℕ)
    (h : n ≤ fuel) : fastPowFuel x fuel n = x^n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n=0 := by omega
    simp [hn, fastPowFuel]
  | succ fuel ih =>
    by_cases hn : n=0
    · simp [fastPowFuel, hn]
    · rw [fastPowFuel, if_neg hn]
      dsimp only
      rw [ih (n/2) (by omega)]
      by_cases hm : n%2=0
      · rw [if_pos hm, mul_one, ← pow_add]
        congr 1
        omega
      · rw [if_neg hm, ← pow_add, ← pow_succ]
        congr 1
        omega

/-- Binary powering with a sufficient structural fuel bound. -/
def fastPow {R : Type*} [CommMonoid R] (x : R) (n : ℕ) : R := fastPowFuel x n n

theorem fastPow_correct {R : Type*} [CommMonoid R] (x : R) (n : ℕ) :
    fastPow x n = x^n := fastPowFuel_correct x n n (by omega)

theorem factor_periodic (p M : ℕ) (hd : p ∣ M) (i : ℕ) :
    factor p M (i+M) = factor p M i := by
  have he : p ∣ i+M+1 ↔ p ∣ i+1 := by
    have h : i+M+1=(i+1)+M := by omega
    rw [h]
    exact (Nat.dvd_add_iff_left hd).symm
  simp only [factor, he]
  split_ifs
  · rfl
  · simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem block_product (p M n : ℕ) (hd : p ∣ M) :
    unitPrefix p M n = (unitPrefix p M M)^(n/M) * unitPrefix p M (n%M) :=
  periodic_product (factor p M) M n (factor_periodic p M hd)

theorem cast_nonmultiples (p M n : ℕ) :
    (nonmultiples p n : ZMod M) = unitPrefix p M n := by
  simp only [nonmultiples, unitPrefix, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [factor]

/-- Residue-block computation, stopped at zero or exhaustion of structural fuel. -/
def algorithmFuel (p M : ℕ) : ℕ → ℕ → ZMod M
  | 0, _ => 1
  | fuel+1, n => if n=0 then 1 else
      fastPow (unitPrefix p M M) (n/M) * unitPrefix p M (n%M) * algorithmFuel p M fuel (n/p)

theorem algorithmFuel_correct (p M fuel n : ℕ) (hp : p.Prime) (hd : p ∣ M)
    (h : n ≤ fuel) : algorithmFuel p M fuel n = (ordCompl[p] n.factorial : ZMod M) := by
  induction fuel generalizing n with
  | zero =>
    have hn : n=0 := by omega
    simp [algorithmFuel, hn]
  | succ fuel ih =>
    by_cases hn : n=0
    · simp [algorithmFuel, hn]
    · rw [algorithmFuel, if_neg hn, fastPow_correct, ih (n/p) (by
        have := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
        omega),
        ← block_product p M n hd, stripped_step p n hp, Nat.cast_mul,
        cast_nonmultiples]

/-- Factorial-unit computation with sufficient fuel; correctness requires a prime p. -/
def algorithm (p M n : ℕ) : ZMod M := algorithmFuel p M n n

theorem algorithm_correct (p M n : ℕ) (hp : p.Prime) (hd : p ∣ M) :
    algorithm p M n = (ordCompl[p] n.factorial : ZMod M) :=
  algorithmFuel_correct p M n n hp hd (by omega)

theorem prime_power_correct (p depth n : ℕ) (hp : p.Prime) (hdepth : 0 < depth) :
    algorithm p (p^depth) n =
      (ordCompl[p] n.factorial : ZMod (p^depth)) := by
  apply algorithm_correct p (p^depth) n hp
  exact dvd_pow_self p (Nat.ne_of_gt hdepth)

end PerfectPower.FactorialUnit
