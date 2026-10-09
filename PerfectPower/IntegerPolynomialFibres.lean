import PerfectPower.PolynomialFibre
import PerfectPower.FastDivisors

/-! Complete integer roots by the integer-root divisibility test. Zero constant
terms are peeled recursively, so zero fibres and repeated roots are retained. -/
namespace PerfectPower.IntegerPolynomialFibres
open PolynomialFibre
open PerfectPower.BoundedNative

def roots : List ℤ → Finset ℤ
  | [] => ∅
  | [_] => ∅
  | [a,b] => if b ∣ -a then {(-a)/b} else ∅
  | a :: b :: c :: as => if a = 0 then insert 0 (roots (b :: c :: as))
      else (FastDivisors.signed a).filter fun x => horner (a :: b :: c :: as) x = 0

theorem root_dvd_constant (a : ℤ) (as : List ℤ) (x : ℤ)
    (h : horner (a :: as) x = 0) : x ∣ a := by
  refine ⟨-horner as x, ?_⟩
  simp only [horner] at h
  nlinarith

theorem complete (as : List ℤ) (hv : valid as) (x : ℤ) :
    horner as x = 0 ↔ x ∈ roots as := by
  induction as with
  | nil => exact False.elim hv
  | cons a as ih =>
    cases as with
    | nil => simpa [roots, horner] using hv
    | cons b bs =>
      cases bs with
      | nil =>
        change b ≠ 0 at hv
        simp only [roots, horner, mul_zero, add_zero]
        constructor
        · intro h
          have hd : b ∣ -a := ⟨x, by nlinarith⟩
          rw [if_pos hd, Finset.mem_singleton]
          have he : -a = x*b := by nlinarith
          rw [he, Int.mul_ediv_cancel _ hv]
        · intro h
          by_cases hd : b ∣ -a
          · rw [if_pos hd] at h
            have he := Int.mul_ediv_cancel' hd
            simp only [Finset.mem_singleton] at h
            rw [h]
            nlinarith
          · simp [hd] at h
      | cons c cs =>
        by_cases ha : a = 0
        · have hi := ih hv
          simp only [roots, ha, if_pos, Finset.mem_insert, horner, zero_add, mul_eq_zero]
          exact or_congr Iff.rfl hi
        · simp only [roots, ha, if_false, Finset.mem_filter]
          constructor
          · intro h
            exact ⟨FastDivisors.mem_signed.mpr ⟨root_dvd_constant a (b::c::cs) x h, ha⟩, h⟩
          · exact fun h => h.2

def subtractConstant : List ℤ → ℤ → List ℤ
  | [], p => [-p]
  | a :: as, p => (a-p) :: as

theorem eval_subtractConstant (as : List ℤ) (p x : ℤ) :
    horner (subtractConstant as p) x = horner as x - p := by
  cases as <;> simp only [subtractConstant, horner] <;> ring

theorem valid_subtractConstant (as : List ℤ) (p : ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) : valid (subtractConstant as p) := by
  cases as with
  | nil => simp at hd
  | cons a as =>
    cases as with
    | nil => simp at hd
    | cons b bs => exact hv

def fibre (as : List ℤ) (p : ℤ) : Finset ℤ := roots (subtractConstant as p)

theorem fibre_complete (as : List ℤ) (p x : ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) : horner as x = p ↔ x ∈ fibre as p := by
  rw [fibre, ← complete _ (valid_subtractConstant as p hv hd), eval_subtractConstant]
  exact sub_eq_zero.symm

def pullback (points : Finset (ℤ × ℤ)) (as : List ℤ) : Finset (ℤ × ℤ) :=
  points.biUnion fun p => (fibre as p.1).image fun x => (x,p.2)

theorem pullback_complete (points : Finset (ℤ × ℤ)) (S : ℤ × ℤ → Prop)
    (complete : ∀ p, p ∈ points ↔ S p) (as : List ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) (p : ℤ × ℤ) :
    p ∈ pullback points as ↔ S (horner as p.1,p.2) := by
  simp only [pullback, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨q,hq,x,hx,he⟩
    have hf := (fibre_complete as q.1 x hv hd).mpr hx
    have hx' := congrArg Prod.fst he
    have hy' := congrArg Prod.snd he
    simp only [Prod.fst, Prod.snd] at hx' hy'
    subst x
    rw [hf, ← hy']
    exact (complete q).mp hq
  · intro h
    exact ⟨(horner as p.1,p.2),(complete _).mpr h,p.1,
      (fibre_complete as _ _ hv hd).mp rfl,Prod.eta p⟩

theorem literal_complete (computed : Finset (ℤ × ℤ)) (points : List (ℤ × ℤ))
    (S : ℤ × ℤ → Prop) (hc : ∀ p, p ∈ computed ↔ S p)
    (he : computed = points.toFinset) (p : ℤ × ℤ) : p ∈ points ↔ S p := by
  rw [← List.mem_toFinset, ← he]
  exact hc p

end PerfectPower.IntegerPolynomialFibres
