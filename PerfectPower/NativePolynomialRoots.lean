import PerfectPower.NativePolynomialSquare
import PerfectPower.FastDivisors

/-! Complete integer roots by the integer-root divisibility test. Zero constant
terms are peeled recursively, so zero fibres and repeated roots are retained. -/
namespace PerfectPower.NativePolynomialRoots
open NativePolynomialSquare

def roots : List ℤ → Finset ℤ
  | [] => ∅
  | a :: as => if a = 0 then insert 0 (roots as)
      else (FastDivisors.signed a).filter fun x => eval (a :: as) x = 0

theorem root_dvd_constant (a : ℤ) (as : List ℤ) (x : ℤ)
    (h : eval (a :: as) x = 0) : x ∣ a := by
  refine ⟨-eval as x, ?_⟩
  simp only [eval] at h
  nlinarith

theorem complete (as : List ℤ) (hv : valid as) (x : ℤ) :
    eval as x = 0 ↔ x ∈ roots as := by
  induction as with
  | nil => exact False.elim hv
  | cons a as ih =>
    by_cases ha : a = 0
    · cases as with
      | nil => exact False.elim (hv ha)
      | cons b bs =>
        have hi := ih hv
        simp only [roots, ha, if_pos, Finset.mem_insert, eval, zero_add, mul_eq_zero]
        exact or_congr Iff.rfl hi
    · simp only [roots, ha, if_false, Finset.mem_filter]
      constructor
      · intro h
        exact ⟨FastDivisors.mem_signed.mpr ⟨root_dvd_constant a as x h, ha⟩, h⟩
      · exact fun h => h.2

def subtractConstant : List ℤ → ℤ → List ℤ
  | [], p => [-p]
  | a :: as, p => (a-p) :: as

theorem eval_subtractConstant (as : List ℤ) (p x : ℤ) :
    eval (subtractConstant as p) x = eval as x - p := by
  cases as <;> simp only [subtractConstant, eval] <;> ring

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
    (hd : 2 ≤ as.length) : eval as x = p ↔ x ∈ fibre as p := by
  rw [fibre, ← complete _ (valid_subtractConstant as p hv hd), eval_subtractConstant]
  exact sub_eq_zero.symm

end PerfectPower.NativePolynomialRoots
