import PerfectPower.NativePolynomialSquare
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.Int.Basic

set_option maxHeartbeats 1200000

/-! Finite local admissibility from an exact integer Bezout certificate.
Simple-root uniqueness and the root bound are adapted from OpenAI math,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/NumberTheory/PowerFree/Sieve.lean (Apache-2.0).
The resultant interface is replaced by a checked polynomial identity. -/
namespace PerfectPower.PowerFreeLocal
open Polynomial

def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)).card

def LocallyAdmissible (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

def Bezout (f u v : Polynomial ℤ) (R : ℤ) : Prop :=
  u*f + v*f.derivative = C R

theorem derivative_not_dvd_of_bezout (f u v : Polynomial ℤ) (R : ℤ)
    (hbez : Bezout f u v R) {p : ℕ} (hgood : ¬ (p : ℤ) ∣ R) {a : ℤ}
    (ha : (p : ℤ) ∣ f.eval a) : ¬ (p : ℤ) ∣ f.derivative.eval a := by
  have he := congrArg (Polynomial.eval a) hbez
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at he
  intro hd
  apply hgood
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_right ha (u.eval a)) (dvd_mul_of_dvd_right hd (v.eval a))

theorem divided_difference_eval (f : Polynomial ℤ) (a : ℤ) :
    (f /ₘ (X - C a)).eval a = f.derivative.eval a := by
  have h := congrArg (Polynomial.eval a)
    (Polynomial.divByMonic_add_X_sub_C_mul_derivate_divByMonic_eq_derivative f a)
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] using h

theorem eval_sub_eq_mul_divided_difference (f : Polynomial ℤ) (a b : ℤ) :
    f.eval b - f.eval a = (b - a) * (f /ₘ (X - C a)).eval b := by
  have h := congrArg (Polynomial.eval b)
    (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic f a)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.modByMonic_X_sub_C_eq_C_eval] using h.symm

theorem prime_power_root_unique (f : Polynomial ℤ) {p k : ℕ} (hp : p.Prime)
    {a b : ℤ} (ha : (p : ℤ) ^ k ∣ f.eval a) (hb : (p : ℤ) ^ k ∣ f.eval b)
    (hab : (p : ℤ) ∣ b - a) (hd : ¬ (p : ℤ) ∣ f.derivative.eval a) :
    (p : ℤ) ^ k ∣ b - a := by
  let q := f /ₘ (X - C a)
  have hq : ¬ (p : ℤ) ∣ q.eval b := by
    intro hqb
    have hdiff : (p : ℤ) ∣ q.eval b - q.eval a :=
      hab.trans (Polynomial.sub_dvd_eval_sub b a q)
    have hqa : (p : ℤ) ∣ q.eval a := by
      simpa only [sub_sub_cancel] using dvd_sub hqb hdiff
    exact hd (by simpa only [q, divided_difference_eval] using hqa)
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hcop : IsCoprime ((p : ℤ) ^ k) (q.eval b) :=
    (hp'.coprime_iff_not_dvd.mpr hq).pow_left
  apply hcop.dvd_of_dvd_mul_left
  rw [mul_comm, ← eval_sub_eq_mul_divided_difference]
  exact dvd_sub hb ha


theorem map_zmod_ne_zero_of_good (f u v : Polynomial ℤ) (R : ℤ) (hbez : Bezout f u v R)
    {p : ℕ} (hp : ¬ (p : ℤ) ∣ R) :
    f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : f.derivative.map (Int.castRingHom (ZMod p)) = 0 := by
    rw [← Polynomial.derivative_map, hz, Polynomial.derivative_zero]
  have he : (p : ℤ) ∣ f.eval 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrArg (Polynomial.eval (0 : ZMod p)) hz
    simpa [Polynomial.eval_zero] using h
  apply derivative_not_dvd_of_bezout f u v R hbez hp he
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := congrArg (Polynomial.eval (0 : ZMod p)) hd
  simpa [Polynomial.eval_zero] using h

theorem rho_prime_pow_le_degree (f u v : Polynomial ℤ) (R : ℤ) (hbez : Bezout f u v R)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hgood : ¬ (p : ℤ) ∣ R) :
    rho f (p ^ k) ≤ f.natDegree := by
  classical
  letI : Fact (p.Prime) := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := map_zmod_ne_zero_of_good f u v R hbez hgood
  let s := (Finset.range (p ^ k)).filter fun a : ℕ =>
    ((p ^ k : ℕ) : ℤ) ∣ f.eval (a : ℤ)
  have hmap : Set.MapsTo (fun a : ℕ => (a : ZMod p)) (↑s) (↑F.roots.toFinset) := by
    intro a ha
    obtain ⟨_, ha⟩ := Finset.mem_filter.mp ha
    have ha' : (p : ℤ) ∣ f.eval (a : ℤ) :=
      (dvd_pow_self (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using ha)
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hF]
    change F.eval (a : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,
      Polynomial.eval_map, ← Int.cast_natCast a (R := ZMod p)]
    change f.eval₂ (Int.castRingHom (ZMod p))
      ((Int.castRingHom (ZMod p)) (a : ℤ)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (a : ℤ)) p).mpr ha'
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod p)) (↑s) := by
    intro a ha b hb hab
    obtain ⟨ha_lt, ha_root⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb_lt, hb_root⟩ := Finset.mem_filter.mp hb
    rw [Finset.mem_range] at ha_lt hb_lt
    have hab' : (p : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (b : ℤ) p).mp
      simpa only [Int.cast_natCast] using hab
    have ha' : (p : ℤ) ∣ f.eval (a : ℤ) :=
      (dvd_pow_self (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using ha_root)
    have hlarge := prime_power_root_unique f hp
      (by simpa only [Nat.cast_pow] using ha_root)
      (by simpa only [Nat.cast_pow] using hb_root) hab'
      (derivative_not_dvd_of_bezout f u v R hbez hgood ha')
    have hmod : a ≡ b [MOD p ^ k] := by
      apply Int.natCast_modEq_iff.mp
      rw [Int.modEq_iff_dvd]
      simpa only [Nat.cast_pow] using hlarge
    exact hmod.eq_of_lt_of_lt ha_lt hb_lt
  calc
    rho f (p ^ k) = s.card := rfl
    _ ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le


def exceptional (R : ℤ) (d : ℕ) : Finset ℕ :=
  R.natAbs.primeFactorsList.toFinset ∪ Finset.range (d+1)

theorem admissible_iff_finite (f u v : Polynomial ℤ) (R : ℤ) (k : ℕ)
    (hbez : Bezout f u v R) (hR : R ≠ 0) (hk : k ≠ 0) :
    LocallyAdmissible f k ↔
      ∀ p ∈ exceptional R f.natDegree, p.Prime → rho f (p^k) < p^k := by
  constructor
  · intro h p _ hp
    exact h p hp
  · intro h p hp
    by_cases he : p ∈ exceptional R f.natDegree
    · exact h p he hp
    · have hgood : ¬ (p : ℤ) ∣ R := by
        intro hd
        apply he
        apply Finset.mem_union_left
        apply List.mem_toFinset.mpr
        exact (Nat.mem_primeFactorsList_iff_dvd (Int.natAbs_ne_zero.mpr hR) hp).mpr
          (Int.natCast_dvd.mp hd)
      have hlarge : f.natDegree < p := by
        by_contra hl
        apply he
        apply Finset.mem_union_right
        exact Finset.mem_range.mpr (by omega)
      exact (rho_prime_pow_le_degree f u v R hbez hp hk hgood).trans_lt
        (hlarge.trans_le (le_self_pow₀ (by omega) hk))

def rootResidues (as : List ℤ) (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a => (q : ℤ) ∣ NativePolynomialSquare.eval as (a : ℤ)

theorem rho_coefficients (as : List ℤ) (q : ℕ) :
    rho (NativePolynomialSquare.polynomial as) q = (rootResidues as q).card := by
  simp only [rho, rootResidues, NativePolynomialSquare.polynomial_eval]

theorem eval_mod_dvd (f : Polynomial ℤ) (q : ℕ) (x : ℤ) :
    (q : ℤ) ∣ f.eval x ↔ (q : ℤ) ∣ f.eval (x % q) := by
  have hx : (q : ℤ) ∣ x - x % q := by
    exact ⟨x/q, by have := Int.emod_add_ediv x (q : ℤ); omega⟩
  have hf := hx.trans (Polynomial.sub_dvd_eval_sub x (x % q) f)
  constructor
  · intro h; simpa only [sub_sub_cancel] using (dvd_sub h hf)
  · intro h; simpa only [sub_add_cancel] using (dvd_add hf h)

theorem rootResidues_complete (as : List ℤ) (q : ℕ) (hq : 0 < q) (x : ℤ) :
    (q : ℤ) ∣ NativePolynomialSquare.eval as x ↔
      (x % q).toNat ∈ rootResidues as q := by
  have hz : 0 ≤ x % (q : ℤ) := Int.emod_nonneg x (by omega)
  have hl : x % (q : ℤ) < q := Int.emod_lt_of_pos x (by omega)
  have he : ((x % (q : ℤ)).toNat : ℤ) = x % (q : ℤ) := Int.toNat_of_nonneg hz
  rw [← NativePolynomialSquare.polynomial_eval, eval_mod_dvd]
  simp only [rootResidues, Finset.mem_filter, Finset.mem_range, he]
  rw [NativePolynomialSquare.polynomial_eval]
  have hn : (x % (q : ℤ)).toNat < q := by omega
  tauto

def PowerFree (k : ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ)^k ∣ a

theorem fixed_divisor_obstruction (f : Polynomial ℤ) (p k : ℕ) (hp : p.Prime)
    (hfull : rho f (p^k) = p^k) (x : ℤ) : ¬ PowerFree k (f.eval x) := by
  intro h
  apply h p hp
  have hsub : ((Finset.range (p^k)).filter fun a : ℕ =>
      ((p^k : ℕ) : ℤ) ∣ f.eval (a : ℤ)) ⊆ Finset.range (p^k) := Finset.filter_subset _ _
  have heq := Finset.eq_of_subset_of_card_le hsub (by simpa only [rho, Finset.card_range] using hfull.ge)
  have hq : 0 < p^k := pow_pos hp.pos _
  have hz : 0 ≤ x % ((p^k : ℕ) : ℤ) := Int.emod_nonneg _ (by positivity)
  have hl : (x % ((p^k : ℕ) : ℤ)).toNat < p^k := by
    have := Int.emod_lt_of_pos x (by positivity : (0 : ℤ) < (p^k : ℕ)); omega
  have hm : (x % ((p^k : ℕ) : ℤ)).toNat ∈ Finset.range (p^k) := Finset.mem_range.mpr hl
  rw [← heq, Finset.mem_filter] at hm
  have hd := hm.2
  rw [Int.toNat_of_nonneg hz] at hd
  rw [Nat.cast_pow] at hd
  exact_mod_cast (eval_mod_dvd f (p^k) x).mpr (by simpa only [Nat.cast_pow] using hd)

end PerfectPower.PowerFreeLocal
