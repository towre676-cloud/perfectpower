import PerfectPower.StructuralCertificates
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval

namespace PerfectPower.TwoDescentBridges

/-- A rational square root of an integer is itself integral. -/
theorem rational_square_root_integral (z : ℚ) (k : ℤ) (hz : z^2=(k:ℚ)) :
    ∃ w : ℤ, (w:ℚ)=z := by
  have hd : z.den^2=1 := by rw [← Rat.den_pow, hz]; simp
  have hone : z.den=1 := by nlinarith [Rat.pos z]
  refine ⟨z.num, ?_⟩
  have he := Rat.num_div_den z
  simpa [hone] using he

/-- Primitive quartic support cannot acquire primes from the denominator. -/
theorem primitive_support (d a b u v w : ℤ) (hd : Squarefree d)
    (hcop : IsRelPrime u v)
    (he : d*w^2=d^2*u^4+a*d*u^2*v^2+b*v^4) : d ∣ b := by
  let g := gcd d v
  have hgd : g ∣ d := gcd_dvd_left d v
  have hgv : g ∣ v := gcd_dvd_right d v
  have hgs : Squarefree g := hd.squarefree_of_dvd hgd
  have hg : g ≠ 0 := by
    intro hg
    have := hgd
    rw [hg, zero_dvd_iff] at this
    exact hd.ne_zero this
  obtain ⟨D,hD⟩ := hgd
  obtain ⟨V,hV⟩ := hgv
  have hg2 : g*g ∣ d*w^2 := by
    rw [he,hD,hV]
    refine ⟨D^2*u^4+a*g*D*u^2*V^2+b*g^2*V^4, ?_⟩
    ring
  have hgw2 : g ∣ w^2 := Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hd hg2
  have hgw : g ∣ w := (hgs.dvd_pow_iff_dvd (by decide : (2:ℕ) ≠ 0)).mp hgw2
  obtain ⟨W,hW⟩ := hgw
  have hrel : IsRelPrime g D := IsRelPrime.of_squarefree_mul (by rwa [← hD])
  have hcanc : g*D*W^2=D^2*u^4+a*g*D*u^2*V^2+b*g^2*V^4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg)
    calc
      g^2*(g*D*W^2) = d*w^2 := by rw [hD,hW]; ring
      _ = d^2*u^4+a*d*u^2*v^2+b*v^4 := he
      _ = g^2*(D^2*u^4+a*g*D*u^2*V^2+b*g^2*V^4) := by rw [hD,hV]; ring
  have hgu4 : g ∣ u^4 := by
    have hprod : g ∣ D^2*u^4 := by
      refine ⟨D*W^2-a*D*u^2*V^2-b*g*V^4, ?_⟩
      linear_combination -hcanc
    exact hrel.pow_right.dvd_of_dvd_mul_left hprod
  have hgu : g ∣ u := (hgs.dvd_pow_iff_dvd (by decide : (4:ℕ) ≠ 0)).mp hgu4
  have hunit : IsUnit g := hcop hgu ⟨V,hV⟩
  have hdv : IsRelPrime d v := by
    intro t htd htv
    exact isUnit_of_dvd_unit (dvd_gcd htd htv) hunit
  have hdbv : d ∣ b*v^4 := by
    refine ⟨w^2-d*u^4-a*u^2*v^2, ?_⟩
    linear_combination -he
  exact hdv.pow_right.dvd_of_dvd_mul_right hdbv

/-- Recover the integral quartic and original y sign on a primitive squareclass chart. -/
theorem point_to_primitive_cover (a b d u v : ℤ) (x y : ℚ)
    (hd : Squarefree d) (hu : u ≠ 0) (hv : v ≠ 0) (hcop : IsRelPrime u v)
    (hx : x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2)
    (hp : y^2=x*(x^2+(a:ℚ)*x+b)) :
    d ∣ b ∧ ∃ w : ℤ,
      w^2=d*u^4+a*u^2*v^2+(b/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  have huq : (u:ℚ) ≠ 0 := by exact_mod_cast hu
  have hvq : (v:ℚ) ≠ 0 := by exact_mod_cast hv
  let z : ℚ := y*(v:ℚ)^3/u
  have hz : z^2=(d*(d^2*u^4+a*d*u^2*v^2+b*v^4):ℤ) := by
    dsimp [z]
    simp only [div_pow,mul_pow]
    rw [hp,hx]
    push_cast
    field_simp [huq,hvq]
    ring
  obtain ⟨W,hW⟩ := rational_square_root_integral z _ hz
  have hWi : W^2=d*(d^2*u^4+a*d*u^2*v^2+b*v^4) := by exact_mod_cast (show (W:ℚ)^2=(_ : ℤ) from by rw [hW]; exact hz)
  have hdW : d ∣ W := (hd.dvd_pow_iff_dvd (by decide : (2:ℕ) ≠ 0)).mp ⟨_,hWi⟩
  obtain ⟨w,hw⟩ := hdW
  have he : d*w^2=d^2*u^4+a*d*u^2*v^2+b*v^4 := by
    apply mul_left_cancel₀ hd.ne_zero
    calc
      d*(d*w^2) = W^2 := by rw [hw]; ring
      _ = d*(d^2*u^4+a*d*u^2*v^2+b*v^4) := hWi
  have hdb := primitive_support d a b u v w hd hcop he
  refine ⟨hdb,w,?_,?_⟩
  · apply mul_left_cancel₀ hd.ne_zero
    have hb : d*(b/d)=b := Int.mul_ediv_cancel' hdb
    linear_combination he-v^4*hb
  · have hWq : (d:ℚ)*w=z := by exact_mod_cast (show (d*w:ℚ)=z from by rw [← Int.cast_mul,← hw,hW])
    dsimp [z] at hWq
    field_simp [huq,hvq] at hWq ⊢
    linear_combination -hWq

/-- Every nonzero integer has a signed squarefree representative. -/
theorem integer_squareclass (n : ℤ) (hn : n ≠ 0) :
    ∃ d s : ℤ, Squarefree d ∧ n=d*s^2 := by
  obtain ⟨a,b,ha,hb,he,hs⟩ := Nat.sq_mul_squarefree_of_pos
    (show 0 < n.natAbs by exact Int.natAbs_pos.mpr hn)
  have hez : (b:ℤ)^2*a=|n| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast he
  by_cases h : 0 ≤ n
  · refine ⟨a,b,Int.squarefree_natCast.mpr hs,?_⟩
    rw [abs_of_nonneg h] at hez
    nlinarith
  · refine ⟨-(a:ℤ),b,?_,?_⟩
    · apply Int.squarefree_natAbs.mp
      simpa using hs
    · rw [abs_of_neg (lt_of_not_ge h)] at hez
      nlinarith

/-- Signed squareclass extraction and primitive numerator/denominator normalization. -/
theorem rational_primitive_squareclass (x : ℚ) (hx : x ≠ 0) :
    ∃ d u v : ℤ, Squarefree d ∧ u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧
      x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 := by
  have hn : x.num ≠ 0 := by
    intro h
    apply hx
    rw [← Rat.num_div_den x,h]
    simp
  have hden : (x.den:ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  obtain ⟨d,s,hd,he⟩ := integer_squareclass (x.num*x.den) (mul_ne_zero hn hden)
  let r : ℚ := (s:ℚ)/x.den
  have hdenq : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hxr : x=(d:ℚ)*r^2 := by
    have heq : (x.num:ℚ)*(x.den:ℚ)=(d:ℚ)*(s:ℚ)^2 := by exact_mod_cast he
    rw [← Rat.num_div_den x]
    dsimp [r]
    field_simp [hdenq]
    linear_combination (x.den:ℚ)*heq
  have hr : r ≠ 0 := by intro h; apply hx; simp [h] at hxr; exact hxr
  refine ⟨d,r.num,r.den,hd,?_,?_,?_,?_⟩
  · intro h
    apply hr
    rw [← Rat.num_div_den r,h]
    simp
  · exact_mod_cast Rat.pos r
  · apply IsCoprime.isRelPrime
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa [Int.gcd] using r.reduced
  · calc
      x = (d:ℚ)*r^2 := hxr
      _ = (d:ℚ)*((r.num:ℚ)/(r.den:ℚ))^2 := by rw [Rat.num_div_den]
      _ = _ := by push_cast; rw [div_pow]; ring

/-- Complete arithmetic descent: no squareclass or divisor premise is supplied. -/
theorem rational_point_cover_complete (a b : ℤ) (x y : ℚ) (hx : x ≠ 0)
    (hp : y^2=x*(x^2+(a:ℚ)*x+b)) :
    ∃ d u v w : ℤ, Squarefree d ∧ d ∣ b ∧ u ≠ 0 ∧ 0 < v ∧
      IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧
      w^2=d*u^4+a*u^2*v^2+(b/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by
  obtain ⟨d,u,v,hd,hu,hv,hcop,hrep⟩ := rational_primitive_squareclass x hx
  obtain ⟨hdb,w,hw,hy⟩ := point_to_primitive_cover a b d u v x y hd hu
    (ne_of_gt hv) hcop hrep hp
  exact ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩

/-- Squarefree support passes any finite list of nonunit square-divisor tests. -/
theorem squarefree_no_square_divisors (d : ℤ) (hd : Squarefree d) (tests : List ℤ)
    (htests : ∀ e ∈ tests, 2 ≤ e) : ∀ e ∈ tests, ¬ e*e ∣ d := by
  intro e he hdiv
  have hunit := hd e hdiv
  have hbound := htests e he
  rcases Int.isUnit_iff.mp hunit with h | h <;> omega

/-- Bounded integer divisors and finite square tests exhaust signed squarefree support. -/
theorem squarefree_divisor_table (b : ℤ) (hb : b ≠ 0) (candidates tests : List ℤ)
    (htests : ∀ e ∈ tests, 2 ≤ e)
    (htable : ∀ d ∈ Finset.Icc (-|b|) |b|,
      (∀ e ∈ tests, ¬ e*e ∣ d) → d ∣ b → d ∈ candidates)
    (d : ℤ) (hd : Squarefree d) (hdb : d ∣ b) : d ∈ candidates := by
  have h := Int.natAbs_le_of_dvd_ne_zero hdb hb
  have hcast : (d.natAbs:ℤ) ≤ (b.natAbs:ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs,Int.natCast_natAbs] at hcast
  exact htable d (Finset.mem_Icc.mpr (abs_le.mp hcast))
    (squarefree_no_square_divisors d hd tests htests) hdb

end PerfectPower.TwoDescentBridges
