import Mathlib.NumberTheory.FLT.Polynomial
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace PerfectPower.FunctionFieldPower
open Polynomial

/-- The primitive Fermat curve has only constant polynomial points when the exponent
is at least three and is nonzero in the coefficient field. This uses Mathlib's
Mason-Stothers corollary; no external solver or height certificate. -/
theorem fermat_constants {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) (hn : 3 ≤ n) (hchar : (n : K) ≠ 0)
    (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0) (h : f^n+g^n=1) :
    f=C (f.coeff 0) ∧ g=C (g.coeff 0) := by
  have hn1 : 1 ≤ n := by omega
  have hcop : IsCoprime f g := by
    refine ⟨f^(n-1),g^(n-1),?_⟩
    simpa [← pow_succ, Nat.sub_add_cancel hn1] using h
  have h1 : (1 : K[X]) ≠ 0 := one_ne_zero
  obtain ⟨hd,hg',_⟩ := Polynomial.flt hn hchar hf hg h1 hcop (by simpa using h)
  exact ⟨eq_C_of_natDegree_eq_zero hd,eq_C_of_natDegree_eq_zero hg'⟩

/-- Frobenius is an explicit obstruction to an unqualified finite-list claim. -/
theorem frobenius_family {K : Type*} [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (t : K[X]) :
    t^p+(1-t)^p=1 := by
  have h := add_pow_char t (1-t) p
  simpa using h.symm

/-- Include the zero-coordinate fibres; no nonvanishing input hypotheses remain. -/
theorem fermat_all_constants {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) (hn : 3 ≤ n) (hchar : (n : K) ≠ 0)
    (f g : K[X]) (h : f^n+g^n=1) :
    f=C (f.coeff 0) ∧ g=C (g.coeff 0) := by
  have hn0 : n ≠ 0 := by omega
  by_cases hf : f=0
  · have hg : g^n=1 := by simpa [hf,zero_pow hn0] using h
    have hd := congrArg Polynomial.natDegree hg
    rw [natDegree_pow, natDegree_one] at hd
    have hzero : g.natDegree=0 := (Nat.mul_eq_zero.mp hd).resolve_left hn0
    exact ⟨by simp [hf],eq_C_of_natDegree_eq_zero hzero⟩
  by_cases hg : g=0
  · have hf' : f^n=1 := by simpa [hg,zero_pow hn0] using h
    have hd := congrArg Polynomial.natDegree hf'
    rw [natDegree_pow, natDegree_one] at hd
    have hzero : f.natDegree=0 := (Nat.mul_eq_zero.mp hd).resolve_left hn0
    exact ⟨eq_C_of_natDegree_eq_zero hzero,by simp [hg]⟩
  exact fermat_constants n hn hchar f g hf hg h

def constantPoints (K : Type*) [Field K] [DecidableEq K] [Fintype K] (n : ℕ) :
    Finset (K × K) := Finset.univ.filter fun z => z.1^n+z.2^n=1

theorem complete {K : Type*} [Field K] [DecidableEq K] [Fintype K]
    (n : ℕ) (hn : 3 ≤ n) (hchar : (n : K) ≠ 0) (f g : K[X]) :
    f^n+g^n=1 ↔ ∃ z ∈ constantPoints K n, f=C z.1 ∧ g=C z.2 := by
  constructor
  · intro h
    obtain ⟨hf,hg⟩ := fermat_all_constants n hn hchar f g h
    refine ⟨(f.coeff 0,g.coeff 0),?_,hf,hg⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hf,hg] at h
    apply Polynomial.C_injective
    simpa only [map_pow,map_add,map_one] using h
  · rintro ⟨z,hz,rfl,rfl⟩
    have hz' := (Finset.mem_filter.mp hz).2
    simpa only [← map_pow, ← map_add, map_one] using congrArg (Polynomial.C : K →+* K[X]) hz'

end PerfectPower.FunctionFieldPower

namespace PerfectPower.FunctionFieldPower.Seven
open Polynomial
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def quarticPoints : Finset (ZMod 7 × ZMod 7) := constantPoints (ZMod 7) 4

theorem quartic_list : quarticPoints =
    {(0,1),(0,6),(1,0),(6,0),(3,3),(3,4),(4,3),(4,4)} := by decide +kernel

/-- All polynomial points of the Fermat quartic over F_7[t], including zero fibres. -/
theorem quartic_complete (f g : (ZMod 7)[X]) :
    f^4+g^4=1 ↔ ∃ z ∈ quarticPoints, f=C z.1 ∧ g=C z.2 :=
  complete 4 (by norm_num) (by decide) f g

end PerfectPower.FunctionFieldPower.Seven
