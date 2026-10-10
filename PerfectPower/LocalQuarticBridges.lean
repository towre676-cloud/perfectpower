import PerfectPower.TwoDescentBridges
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Int.Units

namespace PerfectPower.LocalQuarticBridges

/-- Coprimality of the absolute integer representative supplies a residue unit. -/
theorem integer_unit_of_coprime_abs (n : ℤ) (m : ℕ) (h : n.natAbs.Coprime m) :
    IsUnit (n : ZMod m) := by
  have hu := (ZMod.isUnit_iff_coprime n.natAbs m).mpr h
  by_cases hn : 0 ≤ n
  · have he : (n.natAbs:ZMod m) = (n:ZMod m) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg hn]
    rwa [he] at hu
  · have he : (n.natAbs:ZMod m) = -(n:ZMod m) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hn),Int.cast_neg]
    rw [he] at hu
    simpa using hu.neg

/-- Every primitive integer pair has a unit coordinate modulo any prime power. -/
theorem primitive_units_prime_power (u v : ℤ) (p k : ℕ) (hp : p.Prime)
    (hcop : IsRelPrime u v) : IsUnit (u : ZMod (p^k)) ∨ IsUnit (v : ZMod (p^k)) := by
  by_cases hv : p ∣ v.natAbs
  · have hu : ¬ p ∣ u.natAbs := by
      intro hu
      have hunit : IsUnit (p:ℤ) := hcop
        (Int.natCast_dvd.mpr hu) (Int.natCast_dvd.mpr hv)
      have he : p=1 := by
        have := Int.IsUnit.natAbs_eq hunit
        simpa using this
      exact hp.ne_one he
    exact Or.inl (integer_unit_of_coprime_abs u _
      ((hp.coprime_iff_not_dvd.mpr hu).symm.pow_right k))
  · exact Or.inr (integer_unit_of_coprime_abs v _
      ((hp.coprime_iff_not_dvd.mpr hv).symm.pow_right k))

/-- Quartic homogeneity scales w by the square of the coordinate inverse. -/
theorem scale_cover {R : Type*} [CommRing R] (d a c u v w t : R)
    (hw : w^2=d*u^4+a*u^2*v^2+c*v^4) :
    (t^2*w)^2=d*(t*u)^4+a*(t*u)^2*(t*v)^2+c*(t*v)^4 := by
  linear_combination t^4*hw

/-- Two exhaustive unit charts refute every primitive integral cover. -/
theorem primitive_local_exclusion (d a c : ℤ) (p k : ℕ) (hp : p.Prime)
    (hfirst : ∀ r s : ZMod (p^k), s^2 ≠ (d:ZMod (p^k))*r^4+a*r^2+c)
    (hsecond : ∀ r s : ZMod (p^k), ¬ IsUnit r →
      s^2 ≠ (d:ZMod (p^k))+(a:ZMod (p^k))*r^2+c*r^4)
    (u v w : ℤ) (hcop : IsRelPrime u v) :
    w^2 ≠ d*u^4+a*u^2*v^2+c*v^4 := by
  intro hw
  have hmod : (w:ZMod (p^k))^2=(d:ZMod (p^k))*(u:ZMod (p^k))^4+
      (a:ZMod (p^k))*(u:ZMod (p^k))^2*(v:ZMod (p^k))^2+
      (c:ZMod (p^k))*(v:ZMod (p^k))^4 := by
    have h := congrArg (Int.castRingHom (ZMod (p^k))) hw
    simpa using h
  by_cases hv : IsUnit (v:ZMod (p^k))
  · obtain ⟨t,ht⟩ := isUnit_iff_exists_inv.mp hv
    have hscaled := scale_cover _ _ _ _ _ _ t hmod
    rw [mul_comm t (v:ZMod (p^k)),ht] at hscaled
    exact hfirst (t*u) (t^2*w) (by simpa using hscaled)
  · have hu := (primitive_units_prime_power u v p k hp hcop).resolve_right hv
    obtain ⟨t,ht⟩ := isUnit_iff_exists_inv.mp hu
    have hscaled := scale_cover _ _ _ _ _ _ t hmod
    rw [mul_comm t (u:ZMod (p^k)),ht] at hscaled
    have hnon : ¬ IsUnit (t*(v:ZMod (p^k))) := by
      intro h
      exact hv (isUnit_of_mul_isUnit_right h)
    exact hsecond (t*v) (t^2*w) hnon (by simpa using hscaled)

/-- A finite, computably decidable table supplies the nonunit chart. -/
theorem primitive_local_exclusion_table (d a c : ℤ) (p k : ℕ) (hp : p.Prime)
    (hfirst : ∀ r s : ZMod (p^k), s^2 ≠ (d:ZMod (p^k))*r^4+a*r^2+c)
    (hsecond : ∀ r s : ZMod (p^k), (∃ t : ZMod (p^k), r*t=1) ∨
      s^2 ≠ (d:ZMod (p^k))+(a:ZMod (p^k))*r^2+c*r^4)
    (u v w : ℤ) (hcop : IsRelPrime u v) :
    w^2 ≠ d*u^4+a*u^2*v^2+c*v^4 := by
  apply primitive_local_exclusion d a c p k hp hfirst ?_ u v w hcop
  intro r s hr
  exact (hsecond r s).resolve_left (fun h => hr (isUnit_iff_exists_inv.mpr h))

/-- The second real-place branch: a negative definite quadratic in u²,v². -/
theorem negative_quartic_discriminant (d a c u v : ℚ)
    (hd : d < 0) (hdisc : a^2 < 4*d*c)
    (huv : u ≠ 0 ∨ v ≠ 0) : d*u^4+a*u^2*v^2+c*v^4 < 0 := by
  by_cases hv : v=0
  · have hu : u ≠ 0 := huv.resolve_right (not_not_intro hv)
    have hp : 0 < u^4 := by positivity
    simpa [hv] using mul_neg_of_neg_of_pos hd hp
  · have hp : 0 < v^4 := by positivity
    have hpos : 0 < (4*d*c-a^2)*v^4 := mul_pos (by linarith) hp
    have hs := sq_nonneg (2*d*u^2+a*v^2)
    have he : 4*d*(d*u^4+a*u^2*v^2+c*v^4) =
      (2*d*u^2+a*v^2)^2+(4*d*c-a^2)*v^4 := by ring
    have hprod : 0 < 4*d*(d*u^4+a*u^2*v^2+c*v^4) := by linarith
    nlinarith

/-- Both real obstruction branches refute a nonzero primitive rational chart. -/
theorem primitive_real_exclusion (d a c u v w : ℤ)
    (hd : d < 0) (hc : c < 0) (ha : a ≤ 0 ∨ a^2 < 4*d*c) (hu : u ≠ 0) :
    w^2 ≠ d*u^4+a*u^2*v^2+c*v^4 := by
  intro hw
  have hdq : (d:ℚ) < 0 := by exact_mod_cast hd
  have hcq : (c:ℚ) < 0 := by exact_mod_cast hc
  have huq : (u:ℚ) ≠ 0 := by exact_mod_cast hu
  have hn : (d:ℚ)*(u:ℚ)^4+(a:ℚ)*(u:ℚ)^2*(v:ℚ)^2+(c:ℚ)*(v:ℚ)^4 < 0 := by
    rcases ha with ha | ha
    · exact PerfectPower.StructuralCertificates.negative_quartic_of_nonpositive_middle
        _ _ _ _ _ hdq hcq (by exact_mod_cast ha) (Or.inl huq)
    · exact negative_quartic_discriminant _ _ _ _ _ hdq
        (by exact_mod_cast ha) (Or.inl huq)
  have he : (w:ℚ)^2=(d:ℚ)*(u:ℚ)^4+(a:ℚ)*(u:ℚ)^2*(v:ℚ)^2+(c:ℚ)*(v:ℚ)^4 := by
    exact_mod_cast hw
  nlinarith [sq_nonneg (w:ℚ)]

end PerfectPower.LocalQuarticBridges
