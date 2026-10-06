import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact division fibres and the elliptic halving polynomial

The group statements apply to the actual elliptic point group, without a
rank, finiteness or torsion-classification premise. The coordinate statements
prove the algebra used by `elliptic_arithmetic.py`; they do not verify its
parser, root search or interpreter.
-/

namespace PerfectPower.EllipticDivision

section Group
variable {G : Type*} [AddCommGroup G]

/-- The kernel of multiplication by `n`. -/
def divisionKernel (n : ℤ) : AddSubgroup G where
  carrier := {T | n • T = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all [smul_add]
  neg_mem' := by intro a ha; simp_all

@[simp] theorem mem_divisionKernel (n : ℤ) (T : G) :
    T ∈ divisionKernel n ↔ n • T = 0 := Iff.rfl

/-- Subtracting any anchor identifies a division fibre with the kernel. -/
theorem fibre_iff (n : ℤ) (P H Q : G) (hH : n • H = P) :
    n • Q = P ↔ n • (Q - H) = 0 := by
  rw [smul_sub, hH, sub_eq_zero]

/-- This includes the fibre over infinity (`P = 0`) and every exceptional point. -/
theorem fibre_eq_coset (n : ℤ) (P H Q : G) (hH : n • H = P) :
    n • Q = P ↔ ∃ T ∈ divisionKernel (G := G) n, Q = H + T := by
  constructor
  · intro hQ
    exact ⟨Q - H, (fibre_iff n P H Q hH).mp hQ, by abel⟩
  · rintro ⟨T, hT, rfl⟩
    change n • T = 0 at hT
    simp [smul_add, hH, hT]

/-- A genuine equivalence, hence a nonempty fibre has exactly the kernel's size. -/
def fibreEquiv (n : ℤ) (P H : G) (hH : n • H = P) :
    {Q : G // n • Q = P} ≃ divisionKernel (G := G) n where
  toFun Q := ⟨Q.1 - H, (fibre_iff n P H Q.1 hH).mp Q.2⟩
  invFun T := ⟨H + T.1, by
    have hT : n • T.1 = 0 := T.2
    simp [smul_add, hH, hT]⟩
  left_inv Q := by apply Subtype.ext; dsimp; abel
  right_inv T := by apply Subtype.ext; dsimp; abel

/-- A complete torsion list gives a complete division list, with no search bound. -/
theorem fibre_list_complete (n : ℤ) (P H : G) (hH : n • H = P)
    (L : List G) (hL : ∀ T, n • T = 0 ↔ T ∈ L) (Q : G) :
    n • Q = P ↔ Q ∈ L.map (fun T => H + T) := by
  rw [fibre_eq_coset n P H Q hH, List.mem_map]
  constructor
  · rintro ⟨T, hT, hQ⟩
    exact ⟨T, (hL T).mp hT, hQ.symm⟩
  · rintro ⟨T, hT, hQ⟩
    exact ⟨T, (hL T).mpr hT, hQ.symm⟩

/-- Distinct kernel elements produce distinct halves. -/
theorem translate_injective (H : G) : Function.Injective (fun T : G => H + T) := by
  intro T U h
  exact add_left_cancel h

/-- Multiplication fibres transport exactly through any additive isomorphism. -/
theorem transport_fibre {G' : Type*} [AddCommGroup G'] (e : G ≃+ G')
    (n : ℤ) (Q P : G) : n • e Q = e P ↔ n • Q = P := by
  rw [← map_zsmul e, e.injective.eq_iff]

end Group

section Coordinates
variable {F : Type*} [Field F]

/-- The completed-square cubic, retaining its quadratic coefficient. -/
def cubic (A B C x : F) : F := x ^ 3 + A * x ^ 2 + B * x + C

/-- Numerator of `x([2]H) - u`, after multiplying by `4Y²`. -/
def halvingPolynomial (A B C u x : F) : F :=
  x ^ 4 - 4 * u * x ^ 3 + (-2 * B - 4 * u * A) * x ^ 2 +
    (-8 * C - 4 * u * B) * x + B ^ 2 - 4 * A * C - 4 * u * C

/-- The exact quartic identity, valid in every characteristic. -/
theorem halving_identity (A B C u x : F) :
    (3 * x ^ 2 + 2 * A * x + B) ^ 2 -
      4 * cubic A B C x * (A + 2 * x + u) = halvingPolynomial A B C u x := by
  unfold cubic halvingPolynomial
  ring

/-- Nonexceptional doubling is equivalent to the solver's quartic equation.
The explicit `2Y ≠ 0` condition excludes branch points and characteristic two. -/
theorem doubling_x_iff (A B C u x Y : F) (hY : Y ^ 2 = cubic A B C x)
    (hden : 2 * Y ≠ 0) :
    ((3 * x ^ 2 + 2 * A * x + B) / (2 * Y)) ^ 2 - A - 2 * x = u ↔
      halvingPolynomial A B C u x = 0 := by
  have hsq : (2 * Y) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  rw [div_pow]
  constructor
  · intro h
    have he : (3 * x ^ 2 + 2 * A * x + B) ^ 2 =
        (A + 2 * x + u) * (2 * Y) ^ 2 := by
      apply (div_eq_iff hsq).mp
      linear_combination h
    rw [← halving_identity, ← hY]
    linear_combination he
  · intro h
    rw [← halving_identity, ← hY] at h
    have he : (3 * x ^ 2 + 2 * A * x + B) ^ 2 / (2 * Y) ^ 2 =
        A + 2 * x + u := by
      apply (div_eq_iff hsq).mpr
      linear_combination h
    linear_combination he

/-- Denominator-free generalized Weierstrass normalization. -/
theorem complete_square_identity (a1 a2 a3 a4 a6 x y : F) :
    (2 * y + a1 * x + a3) ^ 2 -
      (4 * x ^ 3 + (a1 ^ 2 + 4 * a2) * x ^ 2 +
        2 * (2 * a4 + a1 * a3) * x + a3 ^ 2 + 4 * a6) =
      4 * (y ^ 2 + a1 * x * y + a3 * y -
        (x ^ 3 + a2 * x ^ 2 + a4 * x + a6)) := by ring

theorem complete_square_iff (a1 a2 a3 a4 a6 x y : F) (h4 : (4 : F) ≠ 0) :
    (2 * y + a1 * x + a3) ^ 2 =
      4 * x ^ 3 + (a1 ^ 2 + 4 * a2) * x ^ 2 +
        2 * (2 * a4 + a1 * a3) * x + a3 ^ 2 + 4 * a6 ↔
      y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6 := by
  rw [← sub_eq_zero, complete_square_identity, mul_eq_zero]
  simp [h4, sub_eq_zero]

/-- Short-form translation retains both the equation and original coordinate. -/
theorem short_translation_identity (A B C x : F) (h3 : (3 : F) ≠ 0) :
    cubic A B C x =
      (x + A / 3) ^ 3 + (B - A ^ 2 / 3) * (x + A / 3) +
        C - A * B / 3 + 2 * A ^ 3 / 27 := by
  unfold cubic
  have h27 : (27 : F) ≠ 0 := by
    have h := pow_ne_zero 3 h3
    convert h using 1
    norm_num
  have h19683 : (19683 : F) ≠ 0 := by
    have h := pow_ne_zero 3 h27
    convert h using 1
    norm_num
  field_simp [h3, h27, h19683]
  ring_nf
  simp [mul_assoc, h19683]

end Coordinates

section RationalRoots
open Polynomial

/-- Exact integer scaling of a rational root, with the monic integral
polynomial and its coefficient identity supplied as checkable data. -/
theorem scaled_root_integral (f : Polynomial ℚ) (g : Polynomial ℤ)
    (D r : ℚ) (hg : g.Monic)
    (hmap : g.map (Int.castRingHom ℚ) = f.scaleRoots D) (hr : f.eval r = 0) :
    ∃ z : ℤ, D * r = z := by
  have hz : aeval (D * r) g = 0 := by
    change g.eval₂ (Int.castRingHom ℚ) (D * r) = 0
    rw [← eval_map, hmap]
    simpa using scaleRoots_eval₂_eq_zero (RingHom.id ℚ) hr
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hg hz
  exact ⟨z, hz⟩

/-- A complete integer root list transports to a complete rational root list.
This does not assume or formalize a particular root-search algorithm. -/
theorem rational_root_list_complete (f : Polynomial ℚ) (g : Polynomial ℤ)
    (D : ℚ) (hD : D ≠ 0) (hg : g.Monic)
    (hmap : g.map (Int.castRingHom ℚ) = f.scaleRoots D)
    (L : List ℤ) (hL : ∀ z : ℤ, g.eval z = 0 ↔ z ∈ L) (r : ℚ) :
    f.eval r = 0 ↔ r ∈ L.map (fun z : ℤ => (z : ℚ) / D) := by
  have he : (g.map (Int.castRingHom ℚ)).eval (D * r) = D ^ f.natDegree * f.eval r := by
    rw [hmap]
    exact scaleRoots_eval₂_mul (RingHom.id ℚ) r D
  constructor
  · intro hr
    obtain ⟨z, hz⟩ := scaled_root_integral f g D r hg hmap hr
    have hgzero : g.eval z = 0 := by
      have hq : (g.map (Int.castRingHom ℚ)).eval (z : ℚ) = 0 := by
        rw [← hz, he, hr, mul_zero]
      rw [eval_map] at hq
      change g.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) z) = 0 at hq
      rw [eval₂_at_apply] at hq
      change ((g.eval z : ℤ) : ℚ) = 0 at hq
      exact_mod_cast hq
    apply List.mem_map.mpr
    exact ⟨z, (hL z).mp hgzero, (eq_div_iff hD).mpr (by simpa [mul_comm] using hz) |>.symm⟩
  · intro hm
    obtain ⟨z, hz, hr⟩ := List.mem_map.mp hm
    have hzq : D * r = (z : ℚ) := by rw [← hr]; field_simp
    have hgzero := (hL z).mpr hz
    have hq : (g.map (Int.castRingHom ℚ)).eval (D * r) = 0 := by
      rw [hzq, eval_map]
      change g.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) z) = 0
      rw [eval₂_at_apply]
      simpa using congrArg (Int.castRingHom ℚ) hgzero
    rw [he, mul_eq_zero] at hq
    exact hq.resolve_left (pow_ne_zero _ hD)

end RationalRoots
end PerfectPower.EllipticDivision
