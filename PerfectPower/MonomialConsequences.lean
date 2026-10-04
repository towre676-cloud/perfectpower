import Mathlib.Tactic

/-! Exact algebra recovered from the August multiplicative system.
Nonzero denominators and the scope of necessary consequences are explicit. -/
namespace PerfectPower.MonomialConsequences

/-- The first historical elimination consequence, without cancelling zero factors. -/
theorem eliminate_K (T K P tau R : ℚ)
    (h1 : T^6*K^3=P^4) (h2 : K^18*tau=R^9) :
    T^36*R^9=P^24*tau := by
  calc
    T^36*R^9 = (T^6)^6*(K^18*tau) := by rw [h2]; ring
    _ = (T^6*K^3)^6*tau := by ring
    _ = P^24*tau := by rw [h1]; ring

/-- The second elimination consequence, also valid at zero. -/
theorem eliminate_E (E tau g a zeta : ℚ)
    (h3 : E^60=tau^5*g^24) (h4 : a^5=zeta*E^2) :
    a^150=zeta^30*tau^5*g^24 := by
  calc
    a^150 = (a^5)^30 := by ring
    _ = zeta^30*E^60 := by rw [h4]; ring
    _ = zeta^30*tau^5*g^24 := by rw [h3]; ring

/-- The precise modulus-three obstruction, in prime-exponent coordinates. -/
theorem cube_compatibility_valuation (K tau R E g b2 b3 : ℤ)
    (h2 : 18*K+tau-9*R=b2) (h3 : 60*E-5*tau-24*g=b3) :
    3 ∣ b3-b2 := by
  refine ⟨20*E-2*tau-8*g-6*K+3*R, ?_⟩
  omega

/-- The rational ratio forced by the two middle equations is an explicit cube. -/
theorem ratio_cube (K tau R E g : ℚ)
    (hK : K ≠ 0) (ht : tau ≠ 0) (hg : g ≠ 0) :
    (E^60/(tau^5*g^24))/(K^18*tau/R^9) =
      (E^20*R^3/(tau^2*g^8*K^6))^3 := by
  field_simp
  ring

theorem middle_equations_force_cube (K tau R E g c2 c3 : ℚ)
    (hK : K ≠ 0) (ht : tau ≠ 0) (hR : R ≠ 0) (hg : g ≠ 0)
    (h2 : K^18*tau=c2*R^9) (h3 : E^60=c3*tau^5*g^24) :
    ∃ q : ℚ, c3/c2=q^3 := by
  have hc2 : c2=K^18*tau/R^9 := (eq_div_iff (pow_ne_zero _ hR)).mpr h2.symm
  have hc3 : c3=E^60/(tau^5*g^24) :=
    (eq_div_iff (mul_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ hg))).mpr (by
      simpa [mul_assoc] using h3.symm)
  refine ⟨E^20*R^3/(tau^2*g^8*K^6), ?_⟩
  rw [hc2, hc3]
  exact ratio_cube K tau R E g hK ht hg

/-- The entire recovered integer exponent image has exactly one compatibility condition. -/
theorem exponent_image_iff (b1 b2 b3 b4 : ℤ) :
    (∃ T K P tau R E g a zeta : ℤ,
      6*T+3*K-4*P=b1 ∧ 18*K+tau-9*R=b2 ∧
      60*E-5*tau-24*g=b3 ∧ -2*E+5*a-zeta=b4) ↔ 3 ∣ b3-b2 := by
  constructor
  · rintro ⟨T,K,P,tau,R,E,g,a,zeta,_,h2,h3,_⟩
    exact cube_compatibility_valuation K tau R E g b2 b3 h2 h3
  · rintro ⟨w,hw⟩
    let r := 2*b2+w-30*b1
    refine ⟨b1,b1,2*b1,b2-18*b1+9*r,r,0,-2*r,0,-b4,?_,?_,?_,?_⟩ <;>
      dsimp [r] <;> omega

/-- A concrete positive-integer relation from the new whole-query examples. -/
theorem signed_product_complete (x y : ℤ) :
    (0 < x ∧ 0 < y ∧ 27*x^2=4*y^3 ∧ x*y=6) ↔ x=2 ∧ y=3 := by
  constructor
  · rintro ⟨hx,hy,hpower,hproduct⟩
    have hxb : x ≤ 6 := by
      have h := mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ y-1 by omega)
      nlinarith
    have hyb : y ≤ 6 := by
      have h := mul_nonneg (show 0 ≤ y by omega) (show 0 ≤ x-1 by omega)
      nlinarith
    interval_cases x <;> interval_cases y <;> norm_num at *
  · rintro ⟨rfl,rfl⟩
    norm_num

end PerfectPower.MonomialConsequences
