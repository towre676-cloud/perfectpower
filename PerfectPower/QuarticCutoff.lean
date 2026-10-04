import PerfectPower.SquareLeadingQuartic

/-! A sharper effective quartic cutoff, retaining the zero-perturbation fibre.
The native command supplies an integer cutoff and the kernel checks its inequalities. -/
namespace PerfectPower.QuarticCutoff
open PerfectPower

/-- Quadratic domination replaces a linear-in-height coordinate bound. -/
theorem bound_or_zero (L a b c d B x y : ℤ) (hB : 0 ≤ B)
    (hA : |a|+|c| ≤ |L| *B)
    (hD : (|a|+|c|)*B+|b|+|d| < |L| *B^2)
    (h : y^2=LinearPerturbation.value L a b c d x) :
    |x| ≤ B ∨ c*x+d=0 := by
  by_cases hz : c*x+d=0
  · exact Or.inr hz
  left
  have hp := (NativeNearSquare.square_bounds (L*x^2+a*x+b) y (c*x+d) hz h).1
  have hr : |c*x+d| ≤ |c| *|x|+|d| := by
    simpa [abs_mul] using abs_add (c*x) d
  have he : |L| *|x|^2 ≤ |L*x^2+a*x+b|+|a| *|x|+|b| := by
    have ht := abs_add (L*x^2+a*x+b) (-(a*x+b))
    have ht2 := abs_add (a*x) b
    have hid : (L*x^2+a*x+b)+ -(a*x+b)=L*x^2 := by ring
    rw [hid,abs_mul,abs_neg,abs_pow] at ht
    rw [abs_mul] at ht2
    omega
  by_contra hn
  have hxB : B ≤ |x| := by omega
  have hM := mul_le_mul_of_nonneg_left hxB (abs_nonneg L)
  have hfactor : 0 ≤ |L| *(|x|+B)-(|a|+|c|) := by
    nlinarith [mul_nonneg (abs_nonneg L) hB]
  have hmono := mul_nonneg (show 0 ≤ |x|-B by omega) hfactor
  nlinarith

def zeroRoots (c d : ℤ) : Finset ℤ :=
  ({(-d)/c} : Finset ℤ).filter fun x => c*x+d=0

theorem zeroRoots_complete (c d x : ℤ) (hcd : c ≠ 0 ∨ d ≠ 0) :
    c*x+d=0 ↔ x ∈ zeroRoots c d := by
  constructor
  · intro h
    have hc : c ≠ 0 := by
      intro hc
      have hd : d=0 := by simpa [hc] using h
      tauto
    have hx : x=(-d)/c := Int.eq_ediv_of_mul_eq_right hc (by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_singleton.mpr hx,h⟩
  · exact fun h => (Finset.mem_filter.mp h).2

def points (L u v w z B : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-B) B) ∪ zeroRoots (SquareLeadingQuartic.rc L u v w)
    (SquareLeadingQuartic.rd L u v z)).biUnion fun x =>
      (LinearPerturbation.squareRoots (SquareLeadingQuartic.value L u v w z x)).image fun y => (x,y)

theorem complete (L u v w z B : ℤ) (hB : 0 ≤ B)
    (hA : |SquareLeadingQuartic.qa L u|+|SquareLeadingQuartic.rc L u v w| ≤
      |SquareLeadingQuartic.qL L| *B)
    (hD : (|SquareLeadingQuartic.qa L u|+|SquareLeadingQuartic.rc L u v w|)*B+
      |SquareLeadingQuartic.qb L u v|+|SquareLeadingQuartic.rd L u v z| <
      |SquareLeadingQuartic.qL L| *B^2)
    (hr : SquareLeadingQuartic.rc L u v w ≠ 0 ∨ SquareLeadingQuartic.rd L u v z ≠ 0)
    (x y : ℤ) : y^2=SquareLeadingQuartic.value L u v w z x ↔ (x,y) ∈ points L u v w z B := by
  constructor
  · intro h
    have hs : (SquareLeadingQuartic.scale L*y)^2=LinearPerturbation.value
        (SquareLeadingQuartic.qL L) (SquareLeadingQuartic.qa L u) (SquareLeadingQuartic.qb L u v)
        (SquareLeadingQuartic.rc L u v w) (SquareLeadingQuartic.rd L u v z) x := by
      rw [← SquareLeadingQuartic.scaling_identity,← h]; ring
    have hb := bound_or_zero _ _ _ _ _ B x _ hB hA hD hs
    apply Finset.mem_biUnion.mpr
    refine ⟨x,?_,Finset.mem_image.mpr ⟨y,(LinearPerturbation.squareRoots_complete _ _).mp h,rfl⟩⟩
    rcases hb with hb | hz
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr (abs_le.mp hb))
    · exact Finset.mem_union_right _ ((zeroRoots_complete _ _ x hr).mp hz)
  · intro h
    obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp ha
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst a; subst b
    exact (LinearPerturbation.squareRoots_complete _ _).mpr hb
end PerfectPower.QuarticCutoff
