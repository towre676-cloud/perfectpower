import Mathlib

namespace PerfectPower.PolyhedralVoronoi

/-- A rational triangle's checked gradient inequality controls every affine direction.
No heat-field approximation or square-root oracle appears in this implication. -/
theorem triangle_gradient (A B C u v a b : ℝ) (hA : 0 < A)
    (hdet : 0 < A*B-C^2) (hg : B*u^2-2*C*u*v+A*v^2 ≤ A*B-C^2) :
    (u*a+v*b)^2 ≤ A*a^2+2*C*a*b+B*b^2 := by
  let q := A*a^2+2*C*a*b+B*b^2
  let g := B*u^2-2*C*u*v+A*v^2
  let det := A*B-C^2
  have hq : 0 ≤ q := by
    have hi : A*q=(A*a+C*b)^2+det*b^2 := by dsimp [q,det];ring
    have hh := mul_nonneg hdet.le (sq_nonneg b)
    change 0 ≤ det*b^2 at hh
    nlinarith [sq_nonneg (A*a+C*b)]
  have hid : g*q-det*(u*a+v*b)^2=((C*u-A*v)*a+(B*u-C*v)*b)^2 := by
    dsimp [g,q,det];ring
  have hm := mul_nonneg (sub_nonneg.mpr hg) hq
  change 0 ≤ (det-g)*q at hm
  change 0 < det at hdet
  have hs := sq_nonneg ((C*u-A*v)*a+(B*u-C*v)*b)
  change (u*a+v*b)^2 ≤ q
  nlinarith

/-- The exact U+2r<L test assigns a whole metric ball strictly to one site. -/
theorem patch_winner {X : Type*} [PseudoMetricSpace X] (p z s t : X) (U L r : ℝ)
    (hz : dist p z ≤ r) (hs : dist p s ≤ U) (ht : L ≤ dist p t)
    (hsep : U+2*r<L) : dist z s < dist z t := by
  have h1 := dist_triangle z p s
  have h2 := dist_triangle p z t
  rw [dist_comm z p] at h1
  linarith

/-- Any equal-distance boundary point must stay outside every certified strict patch. -/
theorem tie_excluded {X : Type*} [PseudoMetricSpace X] (p z s t : X) (U L r : ℝ)
    (hz : dist p z ≤ r) (hs : dist p s ≤ U) (ht : L ≤ dist p t)
    (hsep : U+2*r<L) : dist z s ≠ dist z t := ne_of_lt (patch_winner p z s t U L r hz hs ht hsep)

/-- A certified nonnegative upper square root gives an upper bound on Euclidean length. -/
theorem sqrt_upper (q u : ℝ) (hu : 0 ≤ u) (hq : q ≤ u^2) : Real.sqrt q ≤ u := by
  exact (Real.sqrt_le_left hu).mpr hq

end PerfectPower.PolyhedralVoronoi
