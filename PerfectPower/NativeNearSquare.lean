import Mathlib.Tactic

/-! An elementary effective Runge family with two rational branches at infinity.
The bounds and finite search are wholly Lean-native; no supplied height premise. -/
namespace PerfectPower.NativeNearSquare

lemma factor_abs_le (u v k : ℤ) (hk : k ≠ 0) (h : u * v = k) : |u| ≤ |k| := by
  have hv : v ≠ 0 := by intro hv; simp [hv] at h; exact hk h.symm
  have hv1 : (1 : ℤ) ≤ |v| := by
    have := abs_pos.mpr hv
    omega
  calc |u| = |u| * 1 := by ring
    _ ≤ |u| * |v| := mul_le_mul_of_nonneg_left hv1 (abs_nonneg u)
    _ = |k| := by rw [← abs_mul, h]

theorem square_bounds (p y k : ℤ) (hk : k ≠ 0) (h : y^2 = p^2+k) :
    |p| ≤ |k| ∧ |y| ≤ |k| := by
  have hf : (y-p)*(y+p)=k := by nlinarith [h]
  have h1 := factor_abs_le (y-p) (y+p) k hk hf
  have h2 := factor_abs_le (y+p) (y-p) k hk (by nlinarith [hf])
  have hp := abs_sub (y+p) (y-p)
  have hy := abs_add (y+p) (y-p)
  have ep : (y+p)-(y-p)=2*p := by ring
  have ey : (y+p)+(y-p)=2*y := by ring
  rw [ep, abs_mul] at hp
  rw [ey, abs_mul] at hy
  norm_num at hp hy
  constructor <;> omega

def xBound (a b k : ℤ) : ℤ := |a|+|b|+|k|+1

theorem quadratic_bound (a b k x : ℤ) (h : |x^2+a*x+b| ≤ |k|) :
    |x| ≤ xBound a b k := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hk := abs_nonneg k
  have hx := abs_nonneg x
  have hax : -(a*x) ≤ |a| * |x| := by simpa [abs_mul] using neg_le_abs (a*x)
  have hbn := neg_le_abs b
  have hf := le_abs_self (x^2+a*x+b)
  have hs : |x|^2=x^2 := by simp only [sq_abs]
  unfold xBound
  by_contra hn
  push_neg at hn
  have hlarge : 1 ≤ |x| := by omega
  have hprod : 0 ≤ (|x|-1)*(|b|+|k|+1) := mul_nonneg (by omega) (by omega)
  have hgap : 0 < |x| * (|x|-|a|-|b|-|k|-1) := mul_pos (by omega) (by omega)
  nlinarith

def equation (a b k x y : ℤ) : Prop := y^2=(x^2+a*x+b)^2+k

instance (a b k x y : ℤ) : Decidable (equation a b k x y) := inferInstanceAs
  (Decidable (y^2=(x^2+a*x+b)^2+k))

def points (a b k : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-xBound a b k) (xBound a b k)).product
    (Finset.Icc (-|k|) |k|)).filter fun z => equation a b k z.1 z.2

theorem complete (a b k : ℤ) (hk : k ≠ 0) (x y : ℤ) :
    equation a b k x y ↔ (x,y) ∈ points a b k := by
  constructor
  · intro h
    obtain ⟨hp,hy⟩ := square_bounds (x^2+a*x+b) y k hk h
    have hx := quadratic_bound a b k x hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩
    · exact Finset.mem_Icc.mpr (abs_le.mp hx)
    · exact Finset.mem_Icc.mpr (abs_le.mp hy)
  · intro h
    exact (Finset.mem_filter.mp h).2

theorem explicit_bounds (a b k x y : ℤ) (hk : k ≠ 0) (h : equation a b k x y) :
    |x| ≤ xBound a b k ∧ |y| ≤ |k| := by
  obtain ⟨hp,hy⟩ := square_bounds (x^2+a*x+b) y k hk h
  exact ⟨quadratic_bound a b k x hp,hy⟩

theorem zero_family (a b x : ℤ) : equation a b 0 x (x^2+a*x+b) := by
  simp [equation]

end PerfectPower.NativeNearSquare
