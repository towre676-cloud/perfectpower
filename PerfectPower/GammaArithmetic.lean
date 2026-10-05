import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

namespace PerfectPower.GammaArithmetic

theorem gamma_factorial (n : ℕ) : Real.Gamma ((n : ℝ)+1) = (n.factorial : ℝ) :=
  Real.Gamma_nat_eq_factorial n

theorem gamma_fixed_shift (n r : ℕ) :
    Real.Gamma (((n+r : ℕ) : ℝ)+1) / Real.Gamma ((n : ℝ)+1) =
    ((n+1).ascFactorial r : ℝ) := by
  rw [Real.Gamma_nat_eq_factorial,Real.Gamma_nat_eq_factorial]
  have h : ((n+r).factorial : ℝ) = (n.factorial : ℝ)*((n+1).ascFactorial r : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_ascFactorial n r).symm
  rw [h]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem gamma_three_polynomial (n : ℕ) :
    Real.Gamma (((n+3 : ℕ) : ℝ)+1) / Real.Gamma ((n : ℝ)+1) =
    (n : ℝ)^3+6*(n : ℝ)^2+11*(n : ℝ)+6 := by
  rw [gamma_fixed_shift]
  simp only [Nat.ascFactorial_succ,Nat.ascFactorial_zero,Nat.cast_mul,Nat.cast_add,
    Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat]
  ring


theorem central_prime_once (n : ℕ) (hn : n ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2*n ∧ (Nat.centralBinom n).factorization p = 1 := by
  obtain ⟨p,hp,hnp,hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  have hdvd : p ∣ Nat.centralBinom n := by
    simpa [Nat.centralBinom,two_mul] using hp.dvd_choose_add hnp hnp (by omega)
  have hpos := hp.factorization_pos_of_dvd (Nat.centralBinom_pos n).ne' hdvd
  have hsquare : 2*n < p^2 := by
    have := hp.two_le
    nlinarith
  have hle : (Nat.centralBinom n).factorization p ≤ 1 :=
    Nat.factorization_choose_le_one hsquare
  exact ⟨p,hp,hnp,hpn,by omega⟩

theorem central_not_power (n d y : ℕ) (hn : n ≠ 0) (hd : 2 ≤ d) :
    Nat.centralBinom n ≠ y^d := by
  intro h
  obtain ⟨p,_,_,_,hp⟩ := central_prime_once n hn
  rw [h,Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at hp
  have hdiv : d ∣ 1 := ⟨y.factorization p,hp.symm⟩
  have := Nat.le_of_dvd (by decide : 0<1) hdiv
  omega

theorem central_not_int_power (n d : ℕ) (y : ℤ) (hn : n ≠ 0) (hd : 2 ≤ d) :
    (Nat.centralBinom n : ℤ) ≠ y^d := by
  intro h
  have hh := congrArg Int.natAbs h
  simp only [Int.natAbs_natCast,Int.natAbs_pow] at hh
  exact central_not_power n d y.natAbs hn hd hh

theorem central_gamma (n : ℕ) :
    Real.Gamma (((2*n : ℕ) : ℝ)+1) / Real.Gamma ((n : ℝ)+1)^2 =
    (Nat.centralBinom n : ℝ) := by
  rw [Real.Gamma_nat_eq_factorial,Real.Gamma_nat_eq_factorial]
  have hcast : ((2*n).factorial : ℝ) = (Nat.centralBinom n : ℝ)*
      (n.factorial : ℝ)*(n.factorial : ℝ) := by
    exact_mod_cast (by simpa [Nat.centralBinom,two_mul] using
      (Nat.add_choose_mul_factorial_mul_factorial n n).symm)
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [hcast]
  field_simp
  ring

theorem central_gamma_not_int_power (n d : ℕ) (y : ℤ) (hn : n ≠ 0) (hd : 2 ≤ d) :
    Real.Gamma (((2*n : ℕ) : ℝ)+1) / Real.Gamma ((n : ℝ)+1)^2 ≠ (y : ℝ)^d := by
  rw [central_gamma]
  intro h
  exact central_not_int_power n d y hn hd (by exact_mod_cast h)

theorem binomial_denominator (n r : ℕ) :
    (n.choose r : ℝ) = (n.descFactorial r : ℝ)/(r.factorial : ℝ) := by
  have h : (n.descFactorial r : ℝ) = (r.factorial : ℝ)*(n.choose r : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n r
  have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  rw [h]
  field_simp


theorem binomial_polynomial (n r : ℕ) :
    (n.choose r : ℝ) = (descPochhammer ℝ r).eval (n : ℝ)/(r.factorial : ℝ) := by
  rw [descPochhammer_eval_eq_descFactorial]
  exact binomial_denominator n r


theorem factorial_step (n a : ℕ) :
    (a*n).factorial * (a*n+1).ascFactorial a = (a*(n+1)).factorial := by
  simpa only [Nat.mul_add,Nat.mul_one] using Nat.factorial_mul_ascFactorial (a*n) a

theorem prime_exponent_obstruction (N d p : ℕ) (_hd : 2 ≤ d)
    (bad : ¬ d ∣ N.factorization p) : ¬ ∃ y : ℕ, N=y^d := by
  rintro ⟨y,h⟩
  apply bad
  rw [h,Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
  exact dvd_mul_right _ _

theorem legendre_sum (p n b : ℕ) (hp : Nat.Prime p) (bound : Nat.log p n < b) :
    padicValNat p n.factorial = ∑ i ∈ Finset.Ico 1 b, n / p^i := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact padicValNat_factorial bound

theorem recurrence_unique {K : Type*} [Field K] (P Q f g : ℕ → K)
    (nonzero : ∀ n, Q n ≠ 0) (initial : f 0=g 0)
    (hf : ∀ n, Q n*f (n+1)=P n*f n)
    (hg : ∀ n, Q n*g (n+1)=P n*g n) : f=g := by
  funext n
  induction n with
  | zero => exact initial
  | succ n ih =>
      apply mul_left_cancel₀ (nonzero n)
      rw [hf,hg,ih]

open scoped BigOperators
noncomputable def delta {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℕ) (b : J → ℕ) (x : ℝ) : ℤ :=
    (∑ i, ⌊(a i : ℝ)*x⌋) - ∑ j, ⌊(b j : ℝ)*x⌋

theorem delta_periodic {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℕ) (b : J → ℕ) (balanced : (∑ i, a i) = ∑ j, b j) (x : ℝ) :
    delta a b (x+1)=delta a b x := by
  unfold delta
  simp_rw [mul_add,mul_one,Int.floor_add_natCast]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hc : (∑ i, (a i : ℤ)) = ∑ j, (b j : ℤ) := by exact_mod_cast balanced
  rw [hc]
  omega

end PerfectPower.GammaArithmetic
