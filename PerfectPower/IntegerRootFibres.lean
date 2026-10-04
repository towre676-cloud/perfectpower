import PerfectPower.ExceptionalPowerSearch
namespace PerfectPower.IntegerRootFibres
/-- Integer endpoint subdivision is exact, including the midpoint in the left child. -/
theorem split_interval (a m b x : ℤ) (ham : a ≤ m) (hmb : m ≤ b) :
    (a<x ∧ x≤b) ↔ (a<x ∧ x≤m) ∨ (m<x ∧ x≤b) := by omega

theorem singleton (F : ℤ → ℤ) (a b x : ℤ) (hw : b=a+1) :
    (a<x ∧ x≤b ∧ F x=0) ↔ x=b ∧ F b=0 := by
  constructor
  · rintro ⟨ha,hb,hx⟩
    have he : x=b := by omega
    subst x;exact ⟨rfl,hx⟩
  · rintro ⟨rfl,h⟩;exact ⟨by omega,le_rfl,h⟩

/-- Repeated roots, a half-integer root, and a root-free quadratic are separated natively. -/
theorem repeated_root (A x : ℤ) : (x-A)^3*(2*x+1)*(x^2+1)=0 ↔ x=A := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have hz : x-A=0 := (pow_eq_zero h)
        omega
      · omega
    · nlinarith [sq_nonneg x]
  · intro h;subst x;norm_num

/-- The original square-plus-offset equation has exactly the factor-pair equation. -/
theorem factor_pair (p y k : ℤ) : y^2=p^2+k ↔ (y-p)*(y+p)=k := by
  constructor <;> intro h <;> nlinarith

theorem giant_fibres (x y : ℤ) :
    y^2=((x-1)*(x-10^100))^2+1 ↔
      (x=1 ∨ x=10^100) ∧ (y=1 ∨ y= -1) :=
  ExceptionalPowerSearch.distant_complete _ _ _
end PerfectPower.IntegerRootFibres
