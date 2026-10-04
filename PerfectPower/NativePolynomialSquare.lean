import PerfectPower.NativeNearSquare

/-! Effective finite search for square-plus-constant equations of arbitrary degree.
Coefficients are stored in ascending order; a nonzero final coefficient is required. -/
namespace PerfectPower.NativePolynomialSquare

def eval : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: as, x => a + x * eval as x

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
    (hx : height as + 1 ≤ |x|) : 1 ≤ |eval as x| := by
  induction as with
  | nil => exact False.elim hv
  | cons a as ih =>
    cases as with
    | nil =>
      change a ≠ 0 at hv
      have := abs_pos.mpr hv
      simpa [eval] using (show (1 : ℤ) ≤ |a| by omega)
    | cons b bs =>
      have ht := height_nonneg (b :: bs)
      have ha := abs_nonneg a
      have htail : 1 ≤ |eval (b :: bs) x| := ih hv (by
        change |a| + height (b :: bs) + 1 ≤ |x| at hx
        omega)
      have hm : |x| ≤ |x| * |eval (b :: bs) x| := by
        simpa using mul_le_mul_of_nonneg_left htail (abs_nonneg x)
      have htri := abs_add (a + x * eval (b :: bs) x) (-a)
      have he : (a + x * eval (b :: bs) x) + -a = x * eval (b :: bs) x := by ring
      rw [he, abs_mul, abs_neg] at htri
      change 1 ≤ |a + x * eval (b :: bs) x|
      change |a| + height (b :: bs) + 1 ≤ |x| at hx
      omega

def bound (as : List ℤ) (k : ℤ) : ℤ := height as + |k| + 1

theorem eval_bound (as : List ℤ) (k x : ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) (h : |eval as x| ≤ |k|) : |x| ≤ bound as k := by
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
      have hm : |x| ≤ |x| * |eval (b :: bs) x| := by
        simpa using mul_le_mul_of_nonneg_left htail (abs_nonneg x)
      have htri := abs_add (a + x * eval (b :: bs) x) (-a)
      have he : (a + x * eval (b :: bs) x) + -a = x * eval (b :: bs) x := by ring
      rw [he, abs_mul, abs_neg] at htri
      change |a + x * eval (b :: bs) x| ≤ |k| at h
      change ¬ |x| ≤ |a| + height (b :: bs) + |k| + 1 at hn
      omega

def points (as : List ℤ) (k : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-bound as k) (bound as k)).product
    (Finset.Icc (-|k|) |k|)).filter fun z => z.2^2 = (eval as z.1)^2 + k

theorem complete (as : List ℤ) (k : ℤ) (hv : valid as) (hd : 2 ≤ as.length)
    (hk : k ≠ 0) (x y : ℤ) :
    y^2 = (eval as x)^2 + k ↔ (x,y) ∈ points as k := by
  constructor
  · intro h
    obtain ⟨hp, hy⟩ := NativeNearSquare.square_bounds (eval as x) y k hk h
    have hx := eval_bound as k x hv hd hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hx), Finset.mem_Icc.mpr (abs_le.mp hy)⟩, h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

/-- Interpret the same coefficient list as an actual integer polynomial. -/
noncomputable def polynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * polynomial as

theorem polynomial_eval (as : List ℤ) (x : ℤ) : (polynomial as).eval x = eval as x := by
  induction as with
  | nil => simp [polynomial, eval]
  | cons a as ih => simp [polynomial, eval, ih]

theorem polynomial_complete (as : List ℤ) (k : ℤ) (hv : valid as)
    (hd : 2 ≤ as.length) (hk : k ≠ 0) (x y : ℤ) :
    y^2 = ((polynomial as).eval x)^2 + k ↔ (x,y) ∈ points as k := by
  rw [polynomial_eval]
  exact complete as k hv hd hk x y

end PerfectPower.NativePolynomialSquare
