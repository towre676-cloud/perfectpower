import PerfectPower.PowerFreeLocal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import PerfectPower.NativePolynomialRoots

set_option maxHeartbeats 1600000

/-! The gcd of degree-plus-one consecutive values controls divisibility at every
integer. The proof uses degree-lowering finite differences, not separability. -/
namespace PerfectPower.FixedDivisor
open Polynomial PerfectPower.PowerFreeLocal

noncomputable def difference (f : Polynomial ℤ) : Polynomial ℤ :=
  f.comp (X + C 1) - f

theorem difference_eval (f : Polynomial ℤ) (x : ℤ) :
    (difference f).eval x = f.eval (x+1) - f.eval x := by
  simp [difference, Polynomial.eval_comp]

theorem difference_degree_le (f : Polynomial ℤ) (d : ℕ) (hd : f.natDegree ≤ d+1) :
    (difference f).natDegree ≤ d := by
  by_cases hf : f.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hf]
    simp [difference]
  · have hn : f ≠ 0 := by intro h; simp [h] at hf
    have hc : f.comp (X+C (1 : ℤ)) ≠ 0 := by
      intro h
      have hh := congrArg Polynomial.natDegree h
      simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C,
        mul_one, Polynomial.natDegree_zero] at hh
      exact hf hh
    have he : (f.comp (X+C (1 : ℤ))).degree = f.degree := by
      rw [Polynomial.degree_eq_natDegree hc, Polynomial.degree_eq_natDegree hn,
        Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    have hlc : (f.comp (X+C (1 : ℤ))).leadingCoeff = f.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; decide), Polynomial.leadingCoeff_X_add_C]
      simp
    have hl := Polynomial.degree_sub_lt he hc hlc
    by_cases hz : difference f = 0
    · simp [hz]
    · have hlt : (difference f).natDegree < f.natDegree := by
        apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        rw [he, Polynomial.degree_eq_natDegree hn] at hl
        simpa only [difference] using hl
      omega

theorem dvd_eval_nat_of_window (f : Polynomial ℤ) (d : ℕ) (q : ℤ)
    (hd : f.natDegree ≤ d) (h : ∀ i : ℕ, i ≤ d → q ∣ f.eval (i : ℤ)) :
    ∀ n : ℕ, q ∣ f.eval (n : ℤ) := by
  induction d generalizing f with
  | zero =>
      have hf := Polynomial.eq_C_of_natDegree_le_zero hd
      intro n
      have h0 := h 0 (by omega)
      rw [hf] at h0 ⊢
      simpa only [Polynomial.eval_C] using h0
  | succ d ih =>
      have hg : ∀ n : ℕ, q ∣ (difference f).eval (n : ℤ) := by
        apply ih (difference f) (difference_degree_le f d hd)
        intro i hi
        rw [difference_eval]
        have hnext := h (i+1) (by omega)
        exact dvd_sub (by simpa using hnext) (h i (by omega))
      intro n
      induction n with
      | zero => exact h 0 (by omega)
      | succ n ihn =>
          have he := dvd_add (hg n) ihn
          simpa [difference_eval, Nat.cast_add, Nat.cast_one] using he

theorem dvd_eval_int_of_window (f : Polynomial ℤ) (d q : ℕ)
    (hd : f.natDegree ≤ d) (h : ∀ i : ℕ, i ≤ d → (q : ℤ) ∣ f.eval (i : ℤ))
    (x : ℤ) : (q : ℤ) ∣ f.eval x := by
  by_cases hq : q = 0
  · subst q
    have hz := dvd_eval_nat_of_window f d 0 hd h
    have hf : f = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero f
        (f := fun i : Fin (d+2) => (i.val : ℤ))
      · intro a b hab
        apply Fin.ext
        change (a.val : ℤ) = (b.val : ℤ) at hab
        exact_mod_cast hab
      · intro n
        exact zero_dvd_iff.mp (hz n.val)
      · simpa using (show f.natDegree < d+2 by omega)
    simp [hf]
  · have hn : 0 ≤ x % (q : ℤ) := Int.emod_nonneg x (by omega)
    have he : (((x % (q : ℤ)).toNat : ℕ) : ℤ) = x % (q : ℤ) := Int.toNat_of_nonneg hn
    apply (eval_mod_dvd f q x).mpr
    rw [← he]
    exact dvd_eval_nat_of_window f d q hd h _

def valueGcd : List ℤ → ℕ
  | [] => 0
  | z :: zs => Nat.gcd z.natAbs (valueGcd zs)

theorem dvd_valueGcd (zs : List ℤ) (q : ℕ) :
    q ∣ valueGcd zs ↔ ∀ z ∈ zs, (q : ℤ) ∣ z := by
  induction zs with
  | nil => simp [valueGcd]
  | cons z zs ih =>
      simp only [valueGcd, Nat.dvd_gcd_iff, ih, List.mem_cons, forall_eq_or_imp]
      rw [Int.natCast_dvd]

noncomputable def windowGcd (f : Polynomial ℤ) (d : ℕ) : ℕ :=
  valueGcd ((List.range (d+1)).map fun i : ℕ => f.eval (i : ℤ))

theorem dvd_windowGcd_iff (f : Polynomial ℤ) (d q : ℕ) (hd : f.natDegree ≤ d) :
    q ∣ windowGcd f d ↔ ∀ x : ℤ, (q : ℤ) ∣ f.eval x := by
  rw [windowGcd, dvd_valueGcd]
  constructor
  · intro h x
    apply dvd_eval_int_of_window f d q hd _ x
    intro i hi
    apply h (f.eval (i : ℤ))
    exact List.mem_map.mpr ⟨i, (show i ∈ List.range (d+1) from List.mem_range.mpr (by omega)), rfl⟩
  · intro h z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact h _

noncomputable def fixedDivisor (f : Polynomial ℤ) : ℕ := windowGcd f f.natDegree

theorem dvd_fixedDivisor_iff (f : Polynomial ℤ) (q : ℕ) :
    q ∣ fixedDivisor f ↔ ∀ x : ℤ, (q : ℤ) ∣ f.eval x :=
  dvd_windowGcd_iff f f.natDegree q le_rfl

theorem rho_eq_iff_universal (f : Polynomial ℤ) (q : ℕ) (hq : 0 < q) :
    rho f q = q ↔ ∀ x : ℤ, (q : ℤ) ∣ f.eval x := by
  classical
  let s := (Finset.range q).filter fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)
  have hs : s ⊆ Finset.range q := Finset.filter_subset _ _
  constructor
  · intro h x
    have he : s = Finset.range q := Finset.eq_of_subset_of_card_le hs
      (by simpa only [rho, s, Finset.card_range] using h.ge)
    have hn : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ (by omega)
    have hl : (x % (q : ℤ)).toNat < q := by
      have := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < q)
      omega
    have hm : (x % (q : ℤ)).toNat ∈ s := by rw [he]; exact Finset.mem_range.mpr hl
    have hd := (Finset.mem_filter.mp hm).2
    rw [Int.toNat_of_nonneg hn] at hd
    exact (eval_mod_dvd f q x).mpr hd
  · intro h
    have he : s = Finset.range q := by
      apply Finset.Subset.antisymm hs
      intro a ha
      exact Finset.mem_filter.mpr ⟨ha, h _⟩
    change s.card = q
    rw [he, Finset.card_range]

theorem admissible_iff_fixedDivisor (f : Polynomial ℤ) (k : ℕ) :
    LocallyAdmissible f k ↔ PowerFree k (fixedDivisor f : ℤ) := by
  have hbound (q : ℕ) : rho f q ≤ q := by
    simpa [rho] using Finset.card_le_card
      (Finset.filter_subset (fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)) (Finset.range q))
  constructor
  · intro h p hp hd
    have hd' : p^k ∣ fixedDivisor f := by exact_mod_cast hd
    have he := (rho_eq_iff_universal f (p^k) (pow_pos hp.pos _)).mpr
      ((dvd_fixedDivisor_iff f (p^k)).mp hd')
    have := h p hp
    omega
  · intro h p hp
    have hn : rho f (p^k) ≠ p^k := by
      intro he
      apply h p hp
      have hd := (dvd_fixedDivisor_iff f (p^k)).mpr
        ((rho_eq_iff_universal f (p^k) (pow_pos hp.pos _)).mp he)
      exact_mod_cast hd
    have := hbound (p^k)
    omega

theorem windowGcd_eq_fixedDivisor (f : Polynomial ℤ) (d : ℕ) (hd : f.natDegree ≤ d) :
    windowGcd f d = fixedDivisor f := by
  apply Nat.dvd_antisymm
  · apply (dvd_fixedDivisor_iff f _).mpr
    exact (dvd_windowGcd_iff f d _ hd).mp (dvd_refl _)
  · apply (dvd_windowGcd_iff f d _ hd).mpr
    exact (dvd_fixedDivisor_iff f _).mp (dvd_refl _)

theorem fixedDivisor_dvd_eval (f : Polynomial ℤ) (x : ℤ) :
    (fixedDivisor f : ℤ) ∣ f.eval x :=
  (dvd_fixedDivisor_iff f _).mp (dvd_refl _) x

theorem fixedDivisor_shift (f : Polynomial ℤ) (a : ℤ) :
    fixedDivisor (f.comp (X+C a)) = fixedDivisor f := by
  apply Nat.dvd_antisymm
  · apply (dvd_fixedDivisor_iff f _).mpr
    intro x
    have h := fixedDivisor_dvd_eval (f.comp (X+C a)) (x-a)
    simpa [Polynomial.eval_comp] using h
  · apply (dvd_fixedDivisor_iff (f.comp (X+C a)) _).mpr
    intro x
    simpa [Polynomial.eval_comp] using fixedDivisor_dvd_eval f (x+a)

theorem obstruction_of_fixedDivisor (f : Polynomial ℤ) (p k : ℕ) (hp : p.Prime)
    (hd : p^k ∣ fixedDivisor f) (x : ℤ) : ¬ PowerFree k (f.eval x) := by
  intro h
  apply h p hp
  have he := (dvd_fixedDivisor_iff f (p^k)).mp hd x
  simpa only [Nat.cast_pow] using he

theorem powerFree_power_factor_unit (a b : ℤ) (k : ℕ)
    (h : PowerFree k (a^k*b)) : IsUnit a := by
  by_contra hn
  have ha : a.natAbs ≠ 1 := fun he => hn (Int.isUnit_iff_natAbs_eq.mpr he)
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd ha
  have hi : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hd
  apply h p hp
  exact (pow_dvd_pow_of_dvd hi k).trans (dvd_mul_right (a^k) b)

theorem powerFree_repeated_factor (f g h : Polynomial ℤ) (k : ℕ)
    (hf : f = g^k*h) (x : ℤ) (hx : PowerFree k (f.eval x)) :
    g.eval x = 1 ∨ g.eval x = -1 := by
  have hu : IsUnit (g.eval x) := powerFree_power_factor_unit (g.eval x) (h.eval x) k
    (by simpa only [hf, Polynomial.eval_mul, Polynomial.eval_pow] using hx)
  exact Int.isUnit_iff.mp hu

theorem repeated_candidate_complete (f g h : Polynomial ℤ) (as : List ℤ) (k : ℕ)
    (hf : f = g^k*h) (hg : g = NativePolynomialSquare.polynomial as)
    (hv : NativePolynomialSquare.valid as) (hd : 2 ≤ as.length) (x : ℤ)
    (hx : PowerFree k (f.eval x)) :
    x ∈ NativePolynomialRoots.fibre as 1 ∪ NativePolynomialRoots.fibre as (-1) := by
  obtain hp | hn := powerFree_repeated_factor f g h k hf x hx
  · apply Finset.mem_union_left
    apply (NativePolynomialRoots.fibre_complete as 1 x hv hd).mp
    simpa only [hg, NativePolynomialSquare.polynomial_eval] using hp
  · apply Finset.mem_union_right
    apply (NativePolynomialRoots.fibre_complete as (-1) x hv hd).mp
    simpa only [hg, NativePolynomialSquare.polynomial_eval] using hn

end PerfectPower.FixedDivisor
