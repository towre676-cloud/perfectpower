import PerfectPower.LinearPerturbation
namespace PerfectPower.SquareLeadingQuartic
open PerfectPower.LinearPerturbation

def value (L u v w z x : ℤ) : ℤ := L^2*x^4+u*x^3+v*x^2+w*x+z
def scale (L : ℤ) : ℤ := 8*L^3
def qL (L : ℤ) : ℤ := 8*L^4
def qa (L u : ℤ) : ℤ := 4*L^2*u
def qb (L u v : ℤ) : ℤ := 4*L^2*v-u^2
def rc (L u v w : ℤ) : ℤ := (scale L)^2*w-2*qa L u*qb L u v
def rd (L u v z : ℤ) : ℤ := (scale L)^2*z-(qb L u v)^2

theorem scaling_identity (L u v w z x : ℤ) :
    (scale L)^2*value L u v w z x=
      LinearPerturbation.value (qL L) (qa L u) (qb L u v) (rc L u v w) (rd L u v z) x := by
  simp only [value,rc,rd,scale,qL,qa,qb,LinearPerturbation.value]
  ring

def bound (L u v w z : ℤ) : ℤ :=
  LinearPerturbation.bound (qa L u) (qb L u v) (rc L u v w) (rd L u v z)

theorem coordinate_bound (L u v w z x y : ℤ) (hL : L ≠ 0)
    (hr : rc L u v w ≠ 0 ∨ rd L u v z ≠ 0) (h : y^2=value L u v w z x) :
    |x| ≤ bound L u v w z := by
  have hs : (scale L*y)^2=LinearPerturbation.value (qL L) (qa L u) (qb L u v)
      (rc L u v w) (rd L u v z) x := by
    rw [← scaling_identity,← h]; ring
  exact LinearPerturbation.coordinate_bound _ _ _ _ _ x _
    (by unfold qL; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hL)) hr hs

def points (L u v w z : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-bound L u v w z) (bound L u v w z)).biUnion fun x =>
    (squareRoots (value L u v w z x)).image fun y => (x,y)

theorem complete (L u v w z : ℤ) (hL : L ≠ 0)
    (hr : rc L u v w ≠ 0 ∨ rd L u v z ≠ 0) (x y : ℤ) :
    y^2=value L u v w z x ↔ (x,y) ∈ points L u v w z := by
  constructor
  · intro h
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_Icc.mpr (abs_le.mp (coordinate_bound L u v w z x y hL hr h)),
      Finset.mem_image.mpr ⟨y,(squareRoots_complete _ _).mp h,rfl⟩⟩
  · intro h
    obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp ha
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst a; subst b
    exact (squareRoots_complete _ _).mpr hb
end PerfectPower.SquareLeadingQuartic
