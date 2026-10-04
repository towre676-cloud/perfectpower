import PerfectPower.NativePolynomialSquare
import PerfectPower.FastDivisors
import Mathlib.Data.Int.Sqrt

namespace PerfectPower.LinearPerturbation

def value (L a b c d x : ℤ) : ℤ := (L*x^2+a*x+b)^2+(c*x+d)
theorem expanded (L a b c d x : ℤ) : value L a b c d x =
    NativePolynomialSquare.eval [b^2+d,2*a*b+c,a^2+2*L*b,2*L*a,L^2] x := by
  simp only [value,NativePolynomialSquare.eval]
  ring

def bound (a b c d : ℤ) : ℤ := |a|+|b|+|c|+|d|+1

theorem coordinate_bound (L a b c d x y : ℤ) (hL : L ≠ 0)
    (hcd : c ≠ 0 ∨ d ≠ 0) (h : y^2=value L a b c d x) :
    |x| ≤ bound a b c d := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hc := abs_nonneg c
  have hd := abs_nonneg d
  have hx := abs_nonneg x
  have hL1 : 1 ≤ |L| := by have := abs_pos.mpr hL; omega
  have hr : |c*x+d| ≤ |c| * |x|+|d| := by
    simpa [abs_mul] using abs_add (c*x) d
  by_cases hz : c*x+d=0
  · have hc0 : c ≠ 0 := by
      rcases hcd with hc0 | hd0
      · exact hc0
      · intro hzero; simp [hzero] at hz; exact hd0 hz
    have hc1 : 1 ≤ |c| := by have := abs_pos.mpr hc0; omega
    have he : |c| * |x|=|d| := by
      have he : c*x = -d := by omega
      simpa [abs_mul] using congrArg abs he
    have hm := mul_le_mul_of_nonneg_right hc1 hx
    unfold bound
    omega
  · have hp := (NativeNearSquare.square_bounds (L*x^2+a*x+b) y (c*x+d) hz h).1
    have he : |L| * |x|^2 ≤ |L*x^2+a*x+b|+|a| * |x|+|b| := by
      have ht := abs_add (L*x^2+a*x+b) (-(a*x+b))
      have ht2 := abs_add (a*x) b
      have hid : (L*x^2+a*x+b)+ -(a*x+b)=L*x^2 := by ring
      rw [hid,abs_mul,abs_neg,abs_pow] at ht
      rw [abs_mul] at ht2
      omega
    have hs : |x|^2 ≤ |L| * |x|^2 := by
      simpa using mul_le_mul_of_nonneg_right hL1 (sq_nonneg |x|)
    unfold bound
    by_contra hn
    have hlarge : 1 ≤ |x| := by omega
    have hgap : 0 < |x| * (|x|-|a|-|b|-|c|-|d|-1) := mul_pos (by omega) (by omega)
    have hex : 0 ≤ (|x|-1)*(|b|+|d|+1) := mul_nonneg (by omega) (by omega)
    nlinarith

def root (n : ℤ) : ℤ := FastDivisors.sqrt n.toNat
lemma root_eq (n : ℤ) : root n=Int.sqrt n := by
  simp [root,FastDivisors.sqrt_eq,Int.sqrt]

def squareRoots (n : ℤ) : Finset ℤ := ({root n,-root n}:Finset ℤ).filter fun y => y^2=n

theorem squareRoots_complete (n y : ℤ) : y^2=n ↔ y ∈ squareRoots n := by
  constructor
  · intro h
    have hr : root n=|y| := by
      rw [root_eq,← h]
      simpa [pow_two] using Int.sqrt_eq y
    apply Finset.mem_filter.mpr
    refine ⟨?_,h⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rw [hr]
    rcases le_or_lt 0 y with hy | hy
    · left; rw [abs_of_nonneg hy]
    · right; rw [abs_of_neg hy]; ring
  · intro h
    exact (Finset.mem_filter.mp h).2

def points (L a b c d : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-bound a b c d) (bound a b c d)).biUnion fun x =>
    (squareRoots (value L a b c d x)).image fun y => (x,y)

theorem complete (L a b c d : ℤ) (hL : L ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0)
    (x y : ℤ) : y^2=value L a b c d x ↔ (x,y) ∈ points L a b c d := by
  constructor
  · intro h
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_Icc.mpr (abs_le.mp (coordinate_bound L a b c d x y hL hcd h)),
      Finset.mem_image.mpr ⟨y,(squareRoots_complete _ _).mp h,rfl⟩⟩
  · intro h
    obtain ⟨u,_,hu⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hu
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst u; subst v
    exact (squareRoots_complete _ _).mpr hv
end PerfectPower.LinearPerturbation
