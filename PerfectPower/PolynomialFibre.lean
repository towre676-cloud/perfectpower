import PerfectPower.QueryNative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Abs

namespace PerfectPower.PolynomialFibre

def height : List ℤ → ℤ
  | [] => 0
  | a :: as => |a| + height as

def valid : List ℤ → Prop
  | [] => False
  | [a] => a ≠ 0
  | _ :: b :: bs => valid (b :: bs)

instance (as : List ℤ) : Decidable (valid as) := by
  induction as with
  | nil => exact isFalse id
  | cons a as ih =>
    cases as with
    | nil => exact inferInstanceAs (Decidable (a ≠ 0))
    | cons b bs => exact ih

lemma height_nonneg (as : List ℤ) : 0 ≤ height as := by
  induction as with
  | nil => simp [height]
  | cons a as ih => simp only [height]; positivity

/-- Outside the coefficient height, a polynomial with nonzero leading coefficient
has absolute value at least one. This is an integer Horner form of a root bound. -/
theorem eval_abs_ge_one (as : List ℤ) (x : ℤ) (hv : valid as)
    (hx : height as + 1 ≤ |x|) : 1 ≤ |PerfectPower.BoundedNative.horner as x| := by
  induction as with
  | nil => exact False.elim hv
  | cons a as ih =>
    cases as with
    | nil =>
      change a ≠ 0 at hv
      have := abs_pos.mpr hv
      simpa [PerfectPower.BoundedNative.horner] using (show (1 : ℤ) ≤ |a| by omega)
    | cons b bs =>
      have ht := height_nonneg (b :: bs)
      have ha := abs_nonneg a
      have htail : 1 ≤ |PerfectPower.BoundedNative.horner (b :: bs) x| := ih hv (by
        change |a| + height (b :: bs) + 1 ≤ |x| at hx
        omega)
      have hm : |x| ≤ |x| * |PerfectPower.BoundedNative.horner (b :: bs) x| := by
        simpa using mul_le_mul_of_nonneg_left htail (abs_nonneg x)
      have htri := abs_add (a + x * PerfectPower.BoundedNative.horner (b :: bs) x) (-a)
      have he : (a + x * PerfectPower.BoundedNative.horner (b :: bs) x) + -a = x * PerfectPower.BoundedNative.horner (b :: bs) x := by ring
      rw [he, abs_mul, abs_neg] at htri
      change 1 ≤ |a + x * PerfectPower.BoundedNative.horner (b :: bs) x|
      change |a| + height (b :: bs) + 1 ≤ |x| at hx
      omega

def bound (as : List ℤ) (k : ℤ) : ℤ := height as + |k| + 1

theorem eval_bound (as : List ℤ) (k x : ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) (h : |PerfectPower.BoundedNative.horner as x| ≤ |k|) : |x| ≤ bound as k := by
  cases as with
  | nil => simp at hd
  | cons a as =>
    cases as with
    | nil => simp at hd
    | cons b bs =>
      have ha := abs_nonneg a
      have ht := height_nonneg (b :: bs)
      have hk := abs_nonneg k
      by_contra hn
      have hx : height (b :: bs) + 1 ≤ |x| := by
        change ¬ |x| ≤ |a| + height (b :: bs) + |k| + 1 at hn
        omega
      have htail := eval_abs_ge_one (b :: bs) x hv hx
      have hm : |x| ≤ |x| * |PerfectPower.BoundedNative.horner (b :: bs) x| := by
        simpa using mul_le_mul_of_nonneg_left htail (abs_nonneg x)
      have htri := abs_add (a + x * PerfectPower.BoundedNative.horner (b :: bs) x) (-a)
      have he : (a + x * PerfectPower.BoundedNative.horner (b :: bs) x) + -a = x * PerfectPower.BoundedNative.horner (b :: bs) x := by ring
      rw [he, abs_mul, abs_neg] at htri
      change |a + x * PerfectPower.BoundedNative.horner (b :: bs) x| ≤ |k| at h
      change ¬ |x| ≤ |a| + height (b :: bs) + |k| + 1 at hn
      omega


def fibre (as : List ℤ) (k : ℤ) : List ℤ :=
  (PerfectPower.BoundedNative.interval (-bound as k) (bound as k)).filter
    fun x => decide (PerfectPower.BoundedNative.horner as x = k)

theorem fibre_complete (as : List ℤ) (k x : ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) :
    x ∈ fibre as k ↔ PerfectPower.BoundedNative.horner as x = k := by
  simp only [fibre, List.mem_filter, decide_eq_true_eq, PerfectPower.BoundedNative.mem_interval]
  constructor
  · exact fun h => h.2
  · intro h
    have hb := eval_bound as k x hv hd (by rw [h])
    exact ⟨abs_le.mp hb, h⟩

def pullback (points : List (ℤ × ℤ)) (as : List ℤ) : List (ℤ × ℤ) :=
  points.flatMap fun p => (fibre as p.1).map fun x => (x,p.2)

theorem pullback_complete (points : List (ℤ × ℤ)) (S : ℤ × ℤ → Prop)
    (complete : ∀ p, p ∈ points ↔ S p) (as : List ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) (p : ℤ × ℤ) :
    p ∈ pullback points as ↔ S (PerfectPower.BoundedNative.horner as p.1,p.2) := by
  simp only [pullback, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨q, hq, x, hx, he⟩
    have hf := (fibre_complete as q.1 x hv hd).mp hx
    have hx' := congrArg Prod.fst he
    have hy' := congrArg Prod.snd he
    simp only [Prod.fst, Prod.snd] at hx' hy'
    subst x
    rw [hf, ← hy']
    exact (complete q).mp hq
  · intro h
    refine ⟨(PerfectPower.BoundedNative.horner as p.1,p.2), (complete _).mpr h,
      p.1, (fibre_complete as _ _ hv hd).mpr rfl, ?_⟩
    exact Prod.eta p

end PerfectPower.PolynomialFibre
