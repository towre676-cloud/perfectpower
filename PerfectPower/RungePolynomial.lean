import PerfectPower.NativePolynomialRoots
import PerfectPower.LinearPerturbation

/-! Effective Runge enumeration from a square-plus-lower-degree decomposition.
All coefficients are ascending integer lists. No analytic height premise. -/
namespace PerfectPower.RungePolynomial
open NativePolynomialSquare

/-- Different polynomial degrees force strict absolute-value domination outside
an explicit coefficient bound. The proof compares Horner tails directly. -/
theorem degree_domination (q r : List ℤ) (x : ℤ) (hq : valid q)
    (hdegree : r.length < q.length) (hx : height q + height r + 1 ≤ |x|) :
    |eval r x| + 1 ≤ |eval q x| := by
  induction q generalizing r with
  | nil => simp at hdegree
  | cons a qs ih =>
    cases r with
    | nil =>
      simpa [eval] using eval_abs_ge_one (a::qs) x hq (by
        simpa [height] using hx)
    | cons b rs =>
      cases qs with
      | nil => simp at hdegree
      | cons c cs =>
        have ha := abs_nonneg a
        have hb := abs_nonneg b
        have hqh := height_nonneg (c::cs)
        have hrh := height_nonneg rs
        have ht := ih rs hq (by simpa using hdegree) (by
          change |a|+height (c::cs)+(|b|+height rs)+1 ≤ |x| at hx
          omega)
        have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg x)
        have htri := abs_add (a+x*eval (c::cs) x) (-a)
        have hid : (a+x*eval (c::cs) x)+ -a=x*eval (c::cs) x := by ring
        rw [hid,abs_mul,abs_neg] at htri
        have hr := abs_add b (x*eval rs x)
        rw [abs_mul] at hr
        change |b+x*eval rs x|+1 ≤ |a+x*eval (c::cs) x|
        change |a|+height (c::cs)+(|b|+height rs)+1 ≤ |x| at hx
        nlinarith

def bound (q r : List ℤ) : ℤ := height q+height r+1

/-- The only solutions outside the interval lie in the exact zero-residual fibre. -/
theorem bound_or_residual_zero (q r : List ℤ) (y x : ℤ) (hq : valid q)
    (hdegree : r.length < q.length) (h : y^2=(eval q x)^2+eval r x) :
    |x| ≤ bound q r ∨ eval r x=0 := by
  by_cases hz : eval r x=0
  · exact Or.inr hz
  left
  have hp := (NativeNearSquare.square_bounds (eval q x) y (eval r x) hz h).1
  by_contra hn
  have hd := degree_domination q r x hq hdegree (by unfold bound at hn; omega)
  omega

/-- A nonzero residual has no roots beyond the same bound, so every solution
has an unconditional coordinate bound. The root branch is retained in enumeration. -/
theorem coordinate_bound (q r : List ℤ) (y x : ℤ) (hq : valid q) (hr : valid r)
    (hdegree : r.length < q.length) (h : y^2=(eval q x)^2+eval r x) :
    |x| ≤ bound q r := by
  rcases bound_or_residual_zero q r y x hq hdegree h with hb | hz
  · exact hb
  · by_contra hn
    have hl : ([] : List ℤ).length < r.length := by
      cases r with
      | nil => exact False.elim hr
      | cons a as => simp
    have hqh := height_nonneg q
    have hd := degree_domination r [] x hr hl (by unfold bound at hn; simp [height]; omega)
    simp [eval, hz] at hd

def coordinates (q r : List ℤ) : Finset ℤ :=
  Finset.Icc (-bound q r) (bound q r) ∪ NativePolynomialRoots.roots r

def points (F q r : List ℤ) : Finset (ℤ × ℤ) :=
  (coordinates q r).biUnion fun x =>
    (LinearPerturbation.squareRoots (eval F x)).image fun y => (x,y)

/-- Complete original, unscaled integer points. The scaling identity is checked
separately and every candidate is filtered on the original equation. -/
theorem complete (F q r : List ℤ) (a : ℤ) (hq : valid q) (hr : valid r)
    (hdegree : r.length < q.length)
    (hidentity : ∀ x : ℤ, a^2*eval F x=(eval q x)^2+eval r x) (x y : ℤ) :
    y^2=eval F x ↔ (x,y) ∈ points F q r := by
  constructor
  · intro h
    have hs : (a*y)^2=(eval q x)^2+eval r x := by rw [← hidentity x,← h]; ring
    have hb := bound_or_residual_zero q r (a*y) x hq hdegree hs
    apply Finset.mem_biUnion.mpr
    refine ⟨x,?_,Finset.mem_image.mpr ⟨y,(LinearPerturbation.squareRoots_complete _ _).mp h,rfl⟩⟩
    rcases hb with hb | hz
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr (abs_le.mp hb))
    · exact Finset.mem_union_right _ ((NativePolynomialRoots.complete r hr x).mp hz)
  · intro h
    obtain ⟨u,_,hu⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hu
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst u; subst v
    exact (LinearPerturbation.squareRoots_complete _ _).mpr hv

/-- Zero residual is an exact-square family and gets a relation, not a finite list. -/
theorem square_family (F q : List ℤ) (a : ℤ) (ha : a ≠ 0)
    (hidentity : ∀ x : ℤ, a^2*eval F x=(eval q x)^2) (x y : ℤ) :
    y^2=eval F x ↔ a*y=eval q x ∨ a*y= -eval q x := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  have hid := hidentity x
  constructor
  · intro h; rw [← hid,← h]; ring
  · intro h
    have ha2 : a^2 ≠ 0 := pow_ne_zero _ ha
    apply mul_left_cancel₀ ha2
    calc a^2*y^2 = (a*y)^2 := by ring
      _ = (eval q x)^2 := h
      _ = a^2*eval F x := hid.symm

end PerfectPower.RungePolynomial
