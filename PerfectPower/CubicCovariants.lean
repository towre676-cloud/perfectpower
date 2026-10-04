import Mathlib.Tactic

/-! Independent cubic-to-Mordell reduction, using the repository's standard
discriminant sign. It supplies a finite Thue search from an explicitly supplied
Mordell x-bound. It does not prove a general Mordell height bound or modularity. -/
namespace PerfectPower.CubicCovariants

def form (a b c d u v : ℤ) : ℤ := a*u^3+b*u^2*v+c*u*v^2+d*v^3
def discriminant (a b c d : ℤ) : ℤ :=
  b^2*c^2-4*a*c^3-4*b^3*d-27*a^2*d^2+18*a*b*c*d
def hessian (a b c d u v : ℤ) : ℤ :=
  (b^2-3*a*c)*u^2+(b*c-9*a*d)*u*v+(c^2-3*b*d)*v^2
def jacobian (a b c d u v : ℤ) : ℤ :=
  (3*a*u^2+2*b*u*v+c*v^2)*((b*c-9*a*d)*u+2*(c^2-3*b*d)*v)-
  (b*u^2+2*c*u*v+3*d*v^2)*(2*(b^2-3*a*c)*u+(b*c-9*a*d)*v)

theorem syzygy (a b c d u v : ℤ) :
    4*(hessian a b c d u v)^3-(jacobian a b c d u v)^2 =
      27*discriminant a b c d*(form a b c d u v)^2 := by
  unfold hessian jacobian discriminant form
  ring

theorem mordell_forward (a b c d m u v : ℤ) (h : form a b c d u v=m) :
    (4*jacobian a b c d u v)^2 =
      (4*hessian a b c d u v)^3-432*discriminant a b c d*m^2 := by
  have hs := syzygy a b c d u v
  rw [h] at hs
  nlinarith

theorem reduced_quadratic_lower (A B C u v : ℤ)
    (hA : 1 ≤ A) (hB : |B| ≤ A) (hC : A ≤ C) :
    u^2+v^2 ≤ 2*(A*u^2+B*u*v+C*v^2) := by
  have hb := abs_le.mp hB
  have hcross : -A*(u^2+v^2) ≤ 2*B*u*v := by
    rcases le_or_lt 0 (u*v) with h | h
    · nlinarith [sq_nonneg (u-v),mul_nonneg (by omega : 0 ≤ B+A) h]
    · nlinarith [sq_nonneg (u+v),mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ A-B) h.le]
  nlinarith [mul_nonneg (by omega : 0 ≤ A-1) (sq_nonneg u),
    mul_nonneg (by omega : 0 ≤ 2*C-A-1) (sq_nonneg v)]

theorem source_bounds (a b c d L u v : ℤ)
    (hA : 1 ≤ b^2-3*a*c) (hB : |b*c-9*a*d| ≤ b^2-3*a*c)
    (hC : b^2-3*a*c ≤ c^2-3*b*d)
    (hx : 4*hessian a b c d u v ≤ L) : |u| ≤ L ∧ |v| ≤ L := by
  have hs := reduced_quadratic_lower (b^2-3*a*c) (b*c-9*a*d) (c^2-3*b*d) u v hA hB hC
  change u^2+v^2 ≤ 2*hessian a b c d u v at hs
  have hu : |u| ≤ u^2 := by
    have he := sq_abs u
    have hp := abs_nonneg u
    have hi : |u|=0 ∨ 1 ≤ |u| := by omega
    rcases hi with h | h <;> nlinarith
  have hv : |v| ≤ v^2 := by
    have he := sq_abs v
    have hp := abs_nonneg v
    have hi : |v|=0 ∨ 1 ≤ |v| := by omega
    rcases hi with h | h <;> nlinarith
  constructor <;> nlinarith [sq_nonneg u,sq_nonneg v]

def points (a b c d m L : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-L) L).product (Finset.Icc (-L) L)).filter
    fun z => form a b c d z.1 z.2=m

theorem complete_of_mordell_bound (a b c d m L : ℤ)
    (hA : 1 ≤ b^2-3*a*c) (hB : |b*c-9*a*d| ≤ b^2-3*a*c)
    (hC : b^2-3*a*c ≤ c^2-3*b*d)
    (hbound : ∀ X Y : ℤ, Y^2=X^3-432*discriminant a b c d*m^2 → X ≤ L)
    (u v : ℤ) : form a b c d u v=m ↔ (u,v) ∈ points a b c d m L := by
  constructor
  · intro h
    have hx := hbound _ _ (mordell_forward a b c d m u v h)
    obtain ⟨hu,hv⟩ := source_bounds a b c d L u v hA hB hC hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hu),Finset.mem_Icc.mpr (abs_le.mp hv)⟩,h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

/-- Normalizing a sixth-power coefficient changes integrality into explicit
denominator constraints; it is not an integral-point equivalence by itself. -/
theorem sixth_scale (s k X Y : ℤ) (hs : s ≠ 0) (h : Y^2=X^3+s^6*k) :
    ((Y : ℚ)/(s : ℚ)^3)^2=((X : ℚ)/(s : ℚ)^2)^3+k := by
  have hq : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  have hh : (Y : ℚ)^2=(X : ℚ)^3+(s : ℚ)^6*k := by exact_mod_cast h
  field_simp
  nlinarith [hh]

end PerfectPower.CubicCovariants
