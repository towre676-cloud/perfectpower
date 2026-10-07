import PerfectPower.FixedDivisor

set_option maxHeartbeats 1600000

/-! Exact semantics for F(x)/L on its integer-valued domain. -/
namespace PerfectPower.IntegerValuedPolynomial
open Polynomial PerfectPower.PowerFreeLocal PerfectPower.FixedDivisor

def IntegralAt (f : Polynomial ℤ) (L : ℕ) (x : ℤ) : Prop := (L : ℤ) ∣ f.eval x
noncomputable def quotientValue (f : Polynomial ℤ) (L : ℕ) (x : ℤ) : ℤ := f.eval x / L

theorem integral_everywhere_iff (f : Polynomial ℤ) (L : ℕ) :
    (∀ x : ℤ, IntegralAt f L x) ↔ L ∣ fixedDivisor f :=
  (dvd_fixedDivisor_iff f L).symm

theorem quotient_dvd_iff (f : Polynomial ℤ) (L q : ℕ) (x : ℤ)
    (hx : IntegralAt f L x) :
    (q : ℤ) ∣ quotientValue f L x ↔ ((L*q : ℕ) : ℤ) ∣ f.eval x := by
  simpa only [quotientValue, Nat.cast_mul] using Int.dvd_div_iff_mul_dvd hx

theorem quotient_divisors_iff (f : Polynomial ℤ) (L q : ℕ)
    (hL : L ∣ fixedDivisor f) :
    q ∣ fixedDivisor f / L ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue f L x := by
  rw [Nat.dvd_div_iff_mul_dvd hL, dvd_fixedDivisor_iff]
  constructor
  · intro h x
    apply (quotient_dvd_iff f L q x ((dvd_fixedDivisor_iff f L).mp hL x)).mpr
    exact h x
  · intro h x
    exact (quotient_dvd_iff f L q x ((dvd_fixedDivisor_iff f L).mp hL x)).mp (h x)

theorem quotient_mod_transport (f : Polynomial ℤ) (L q : ℕ)
    (hL : L ∣ fixedDivisor f) (x : ℤ) :
    (q : ℤ) ∣ quotientValue f L x ↔
    (q : ℤ) ∣ quotientValue f L (x % ((L*q : ℕ) : ℤ)) := by
  rw [quotient_dvd_iff f L q x ((dvd_fixedDivisor_iff f L).mp hL x),
    eval_mod_dvd f (L*q) x,
    ← quotient_dvd_iff f L q _ ((dvd_fixedDivisor_iff f L).mp hL _)]

def QuotientAdmissible (f : Polynomial ℤ) (L k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ x : ℤ, IntegralAt f L x ∧ ¬ (p : ℤ)^k ∣ quotientValue f L x

theorem admissible_iff_quotientGcd (f : Polynomial ℤ) (L k : ℕ)
    (hL : L ∣ fixedDivisor f) :
    QuotientAdmissible f L k ↔ PowerFree k (fixedDivisor f / L : ℕ) := by
  classical
  constructor
  · intro h p hp hd
    have hn : p^k ∣ fixedDivisor f / L := by exact_mod_cast hd
    obtain ⟨x, _, hx⟩ := h p hp
    apply hx
    simpa only [Nat.cast_pow] using (quotient_divisors_iff f L (p^k) hL).mp hn x
  · intro h p hp
    by_contra hn
    have he : ∀ x : ℤ, (p : ℤ)^k ∣ quotientValue f L x := by
      intro x
      by_contra hx
      exact hn ⟨x, (dvd_fixedDivisor_iff f L).mp hL x, hx⟩
    apply h p hp
    have hd := (quotient_divisors_iff f L (p^k) hL).mpr
      (by simpa only [Nat.cast_pow] using he)
    exact_mod_cast hd

theorem quotient_obstruction (f : Polynomial ℤ) (L p k : ℕ) (hp : p.Prime)
    (hL : L ∣ fixedDivisor f) (hd : p^k ∣ fixedDivisor f / L) (x : ℤ) :
    ¬ PowerFree k (quotientValue f L x) := by
  intro h
  apply h p hp
  simpa only [Nat.cast_pow] using (quotient_divisors_iff f L (p^k) hL).mp hd x

theorem canonical_coordinate (L : ℕ) (hL : 0 < L) (x : ℤ) :
    x = ((x % (L : ℤ)).toNat : ℤ) + (L : ℤ)*(x/(L : ℤ)) := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))]
  have he := Int.emod_add_ediv x (L : ℤ)
  omega

theorem integer_domain_cover (as : List ℤ) (L : ℕ) (hL : 0 < L) (x : ℤ) :
    IntegralAt (NativePolynomialSquare.polynomial as) L x ↔
    ∃ r ∈ rootResidues as L, ∃ n : ℤ, x = (r : ℤ)+(L : ℤ)*n := by
  constructor
  · intro hx
    refine ⟨(x % (L : ℤ)).toNat, ?_, x/L, canonical_coordinate L hL x⟩
    exact (rootResidues_complete as L hL x).mp
      (by simpa only [IntegralAt, NativePolynomialSquare.polynomial_eval] using hx)
  · rintro ⟨r, hr, n, rfl⟩
    have hd : (L : ℤ) ∣ (NativePolynomialSquare.polynomial as).eval (r : ℤ) := by
      simpa only [rootResidues, Finset.mem_filter, NativePolynomialSquare.polynomial_eval] using
        (Finset.mem_filter.mp hr).2
    have he : (L : ℤ) ∣ (r : ℤ)+(L : ℤ)*n - r := by
      refine ⟨n, ?_⟩
      ring
    have hv := he.trans (Polynomial.sub_dvd_eval_sub _ _ (NativePolynomialSquare.polynomial as))
    change (L : ℤ) ∣ (NativePolynomialSquare.polynomial as).eval ((r : ℤ)+(L : ℤ)*n)
    simpa only [sub_add_cancel] using dvd_add hv hd

theorem chart_eval (f g : Polynomial ℤ) (L r : ℕ)
    (hc : f.comp (C (r : ℤ)+C (L : ℤ)*X) = C (L : ℤ)*g) (n : ℤ) :
    f.eval ((r : ℤ)+(L : ℤ)*n) = (L : ℤ)*g.eval n := by
  have h := congrArg (Polynomial.eval n) hc
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] using h

theorem chart_integral (f g : Polynomial ℤ) (L r : ℕ)
    (hc : f.comp (C (r : ℤ)+C (L : ℤ)*X) = C (L : ℤ)*g) (n : ℤ) :
    IntegralAt f L ((r : ℤ)+(L : ℤ)*n) := ⟨g.eval n, chart_eval f g L r hc n⟩

theorem chart_quotient (f g : Polynomial ℤ) (L r : ℕ) (hL : L ≠ 0)
    (hc : f.comp (C (r : ℤ)+C (L : ℤ)*X) = C (L : ℤ)*g) (n : ℤ) :
    quotientValue f L ((r : ℤ)+(L : ℤ)*n) = g.eval n := by
  rw [quotientValue, chart_eval f g L r hc]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hL)

noncomputable def familyGcd : List (Polynomial ℤ) → ℕ
  | [] => 0
  | f :: fs => Nat.gcd (fixedDivisor f) (familyGcd fs)

theorem dvd_familyGcd_iff (fs : List (Polynomial ℤ)) (q : ℕ) :
    q ∣ familyGcd fs ↔ ∀ f ∈ fs, ∀ n : ℤ, (q : ℤ) ∣ f.eval n := by
  induction fs with
  | nil => simp [familyGcd]
  | cons f fs ih =>
      simp only [familyGcd, Nat.dvd_gcd_iff, dvd_fixedDivisor_iff, ih,
        List.mem_cons, forall_eq_or_imp]

theorem domain_divisors_iff (as : List ℤ) (L q : ℕ) (hL : 0 < L)
    (g : ℕ → Polynomial ℤ)
    (hc : ∀ r ∈ rootResidues as L,
      (NativePolynomialSquare.polynomial as).comp (C (r : ℤ)+C (L : ℤ)*X) = C (L : ℤ)*g r) :
    q ∣ familyGcd ((rootResidues as L).toList.map g) ↔
    ∀ x : ℤ, IntegralAt (NativePolynomialSquare.polynomial as) L x →
      (q : ℤ) ∣ quotientValue (NativePolynomialSquare.polynomial as) L x := by
  rw [dvd_familyGcd_iff]
  constructor
  · intro h x hx
    obtain ⟨r, hr, n, rfl⟩ := (integer_domain_cover as L hL x).mp hx
    rw [chart_quotient _ _ L r (by omega) (hc r hr)]
    exact h (g r) (List.mem_map.mpr ⟨r, Finset.mem_toList.mpr hr, rfl⟩) n
  · intro h f hf n
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    have hm := Finset.mem_toList.mp hr
    have hx := chart_integral _ _ L r (hc r hm) n
    have he := h ((r : ℤ)+(L : ℤ)*n) hx
    simpa only [chart_quotient _ _ L r (by omega) (hc r hm)] using he

theorem familyGcd_congr (fs gs : List (Polynomial ℤ))
    (h : ∀ f, f ∈ fs ↔ f ∈ gs) : familyGcd fs = familyGcd gs := by
  apply Nat.dvd_antisymm
  · apply (dvd_familyGcd_iff gs _).mpr
    intro f hf n
    exact (dvd_familyGcd_iff fs _).mp (dvd_refl _) f ((h f).mpr hf) n
  · apply (dvd_familyGcd_iff fs _).mpr
    intro f hf n
    exact (dvd_familyGcd_iff gs _).mp (dvd_refl _) f ((h f).mp hf) n

theorem quotient_rational_value (f : Polynomial ℤ) (L : ℕ) (hL : L ≠ 0)
    (x : ℤ) (hx : IntegralAt f L x) :
    ((f.eval x : ℤ) : ℚ) / (L : ℚ) = (quotientValue f L x : ℚ) := by
  apply (div_eq_iff (by exact_mod_cast hL : (L : ℚ) ≠ 0)).mpr
  have h : quotientValue f L x * (L : ℤ) = f.eval x := Int.ediv_mul_cancel hx
  have hc : (quotientValue f L x : ℚ) * (L : ℚ) = ((f.eval x : ℤ) : ℚ) := by
    exact_mod_cast h
  exact hc.symm

theorem quotient_natural_divisors_iff (f : Polynomial ℤ) (L q : ℕ)
    (hL : L ∣ fixedDivisor f) :
    q ∣ fixedDivisor f / L ↔ ∀ x : ℕ, (q : ℤ) ∣ quotientValue f L x := by
  constructor
  · intro h x
    exact (quotient_divisors_iff f L q hL).mp h x
  · intro h
    apply (quotient_divisors_iff f L q hL).mpr
    intro x
    apply (quotient_dvd_iff f L q x ((dvd_fixedDivisor_iff f L).mp hL x)).mpr
    apply dvd_eval_int_of_window f f.natDegree (L*q) (le_refl _) _ x
    intro i _
    exact (quotient_dvd_iff f L q i ((dvd_fixedDivisor_iff f L).mp hL i)).mp (h i)

end PerfectPower.IntegerValuedPolynomial
