import PerfectPower.IntegerValuedPolynomial
import PerfectPower.ResidueAtlasIntersectionFactored

namespace PerfectPower.IntegerValuedPowerCharts
open Polynomial PerfectPower.IntegerValuedPolynomial PerfectPower.PowerFreeLocal

def PowerAt (f : Polynomial ℤ) (L : ℕ) (k : ℤ) (d : ℕ) (x y : ℤ) : Prop :=
  IntegralAt f L x ∧ quotientValue f L x + k = y^d

/-- Clearing a positive denominator retains the entire integral domain. -/
theorem cleared_power_iff (f : Polynomial ℤ) (L : ℕ) (k : ℤ) (d : ℕ)
    (hL : L ≠ 0) (x y : ℤ) :
    PowerAt f L k d x y ↔ f.eval x + (L : ℤ)*k = (L : ℤ)*y^d := by
  have hn : (L : ℤ) ≠ 0 := by exact_mod_cast hL
  constructor
  · rintro ⟨hx,he⟩
    have hm : (L : ℤ)*quotientValue f L x = f.eval x :=
      Int.mul_ediv_cancel' hx
    rw [← hm]
    linear_combination (L : ℤ)*he
  · intro he
    have hx : IntegralAt f L x := ⟨y^d-k,by linear_combination he⟩
    refine ⟨hx,?_⟩
    apply mul_left_cancel₀ hn
    have hm : (L : ℤ)*quotientValue f L x = f.eval x := Int.mul_ediv_cancel' hx
    linear_combination he + hm

/-- The rational polynomial equation agrees exactly with the domain-aware
integer quotient equation once the numerator identity is proved. -/
theorem rational_power_iff (f : Polynomial ℤ) (Q : Polynomial ℚ) (L : ℕ)
    (k : ℤ) (d : ℕ) (hL : L ≠ 0)
    (hc : Q*C (L : ℚ)=f.map (Int.castRingHom ℚ)) (x y : ℤ) :
    Q.eval (x : ℚ)+(k : ℚ)=(y : ℚ)^d ↔ PowerAt f L k d x y := by
  have hn : (L : ℚ) ≠ 0 := by exact_mod_cast hL
  have he : Q.eval (x : ℚ)*(L : ℚ)=((f.eval x : ℤ) : ℚ) := by
    simpa using congrArg (Polynomial.eval (x : ℚ)) hc
  rw [cleared_power_iff f L k d hL]
  constructor
  · intro h
    have hi : ((f.eval x : ℤ) : ℚ)+(L : ℚ)*(k : ℚ)=(L : ℚ)*(y : ℚ)^d := by
      linear_combination (L : ℚ)*h-he
    exact_mod_cast hi
  · intro h
    have hi : ((f.eval x : ℤ) : ℚ)+(L : ℚ)*(k : ℚ)=(L : ℚ)*(y : ℚ)^d := by exact_mod_cast h
    apply mul_left_cancel₀ hn
    linear_combination hi+he

/-- Exact equation transport, including zero and both signs of the power root. -/
theorem chart_power_iff (f g : Polynomial ℤ) (L r : ℕ) (k : ℤ) (d : ℕ)
    (hL : L ≠ 0)
    (hc : f.comp (C (r : ℤ)+C (L : ℤ)*X) = C (L : ℤ)*g) (n y : ℤ) :
    PowerAt f L k d ((r : ℤ)+(L : ℤ)*n) y ↔ g.eval n+k=y^d := by
  simp only [PowerAt,chart_integral f g L r hc n, true_and,
    chart_quotient f g L r hL hc n]

/-- Complete union of the denominator residue charts for the original equation. -/
theorem power_cover (as : List ℤ) (L : ℕ) (hL : 0<L) (k : ℤ) (d : ℕ)
    (g : ℕ → Polynomial ℤ)
    (hc : ∀ r ∈ rootResidues as L,
      (PerfectPower.NativePolynomialSquare.polynomial as).comp
        (C (r : ℤ)+C (L : ℤ)*X) = C (L : ℤ)*g r) (x y : ℤ) :
    PowerAt (PerfectPower.NativePolynomialSquare.polynomial as) L k d x y ↔
      ∃ r ∈ rootResidues as L, ∃ n : ℤ,
        x=(r : ℤ)+(L : ℤ)*n ∧ (g r).eval n+k=y^d := by
  constructor
  · rintro ⟨hx,he⟩
    obtain ⟨r,hr,n,rfl⟩ := (integer_domain_cover as L hL x).mp hx
    exact ⟨r,hr,n,rfl,(chart_power_iff _ _ L r k d (by omega) (hc r hr) n y).mp ⟨hx,he⟩⟩
  · rintro ⟨r,hr,n,rfl,he⟩
    exact (chart_power_iff _ _ L r k d (by omega) (hc r hr) n y).mpr he

/-- Source-coordinate intervals pull back without losing a signed endpoint. -/
theorem chart_interval (L r lo hi n : ℤ) (hL : 0<L) :
    lo ≤ r+L*n ∧ r+L*n ≤ hi ↔
      -((r-lo)/L) ≤ n ∧ n ≤ (hi-r)/L := by
  rw [neg_le, Int.le_ediv_iff_mul_le hL, Int.le_ediv_iff_mul_le hL]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith

/-- A modular cover of each chart preserves every original source solution. -/
theorem chart_modular_survives (g : Polynomial ℤ) (k : ℤ) (d : ℕ)
    (m : ℤ) (cover : PerfectPower.ResidueAtlas.AtlasPacket
      (fun n y => g.eval n+k-y^d) m) (n y : ℤ)
    (he : g.eval n+k=y^d) : (n%m,y%m) ∈ cover.roots := by
  apply cover.source_survives
  exact sub_eq_zero.mpr he

end PerfectPower.IntegerValuedPowerCharts
