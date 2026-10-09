import PerfectPower.EllipticDivision
import PerfectPower.BoundedNative
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.Linarith

namespace PerfectPower.MordellParity
open WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F]

/-- The completed-square model y²=x³+Ax²+Bx+C. -/
def completed (A B C : F) : Affine F :=
  (⟨0, A, 0, B, C⟩ : WeierstrassCurve F).toAffine

/-- The completed model has the declared cubic equation. -/
theorem equation_completed (A B C x y : F) :
    (completed A B C).Equation x y ↔ y ^ 2 = EllipticDivision.cubic A B C x := by
  rw [equation_iff']
  simp [completed, EllipticDivision.cubic, sub_eq_zero]

/-- A point doubles to zero exactly when it equals its negation. -/
theorem double_eq_zero_iff {W : Affine F} (P : W.Point) :
    (2 : ℤ) • P = 0 ↔ P = -P := by
  rw [show (2 : ℤ) • P = P + P by simp [two_smul], add_eq_zero_iff_eq_neg]

/-- Branch points are exactly the nonzero two-torsion points when 2 is invertible. -/
theorem affine_two_torsion_iff (A B C x y : F)
    (h : (completed A B C).Nonsingular x y) (h2 : (2 : F) ≠ 0) :
    (2 : ℤ) • Point.some h = 0 ↔ y = 0 := by
  rw [double_eq_zero_iff, Point.neg_some, Point.some.injEq]
  simp only [completed, negY, zero_mul, sub_zero, neg_zero, zero_add, true_and]
  constructor
  · intro hy
    have hz : (2 : F) * y = 0 := by linear_combination hy
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro hy
    simp [hy]

/-- Every nonzero two-torsion point yields a rational cubic root in characteristic zero. -/
theorem two_torsion_root (A B C x y : F)
    (h : (completed A B C).Nonsingular x y) (h2 : (2 : F) ≠ 0)
    (ht : (2 : ℤ) • Point.some h = 0) : EllipticDivision.cubic A B C x = 0 := by
  have hy := (affine_two_torsion_iff A B C x y h h2).mp ht
  have he := (equation_completed A B C x y).mp h.1
  simpa [hy] using he.symm

/-- The x-coordinate in Mathlib's doubling formula is the halving quartic. -/
theorem actual_doubling_x_iff (A B C u x y : F)
    (h : (completed A B C).Nonsingular x y) (hden : 2 * y ≠ 0) :
    (completed A B C).addX x x ((completed A B C).slope x x y y) = u ↔
      EllipticDivision.halvingPolynomial A B C u x = 0 := by
  have hy : y ≠ (completed A B C).negY x y := by
    intro he
    apply hden
    simp only [completed, negY, zero_mul, sub_zero] at he
    linear_combination he
  rw [slope_of_Y_ne rfl hy]
  have hs : y - (completed A B C).negY x y = 2 * y := by
    simp [completed, negY]
    ring
  rw [hs]
  have he := (equation_completed A B C x y).mp h.1
  convert EllipticDivision.doubling_x_iff A B C u x y he hden using 1
  simp only [addX, completed, zero_mul, mul_zero, sub_zero, add_zero]
  ring_nf

/-- Every half of a nonzero affine target supplies a root of its halving quartic. -/
theorem half_supplies_quartic_root (A B C u v : ℚ)
    (hp : (completed A B C).Nonsingular u v)
    (Q : (completed A B C).Point) (hQ : (2 : ℤ) • Q = Point.some hp) :
    ∃ x, EllipticDivision.halvingPolynomial A B C u x = 0 := by
  cases Q with
  | zero =>
    change (2 : ℤ) • (0 : (completed A B C).Point) = Point.some hp at hQ
    rw [zsmul_zero] at hQ
    exact False.elim (Point.some_ne_zero hp hQ.symm)
  | @some x y h =>
    have hy : y ≠ 0 := by
      intro hy
      have ht := (affine_two_torsion_iff A B C x y h (by norm_num)).mpr hy
      rw [ht] at hQ
      exact Point.some_ne_zero hp hQ.symm
    have hn : y ≠ (completed A B C).negY x y := by
      simp only [completed, negY, zero_mul, sub_zero, neg_zero, zero_add]
      intro he
      apply hy
      linear_combination (1 / 2 : ℚ) * he
    rw [two_zsmul, Point.add_self_of_Y_ne hn, Point.some.injEq] at hQ
    exact ⟨x, (actual_doubling_x_iff A B C u x y h (mul_ne_zero (by norm_num) hy)).mp hQ.1⟩

/-- A root-free quartic proves an empty actual halving fibre, including branch targets. -/
theorem no_half_of_quartic_root_free (A B C u v : ℚ)
    (hp : (completed A B C).Nonsingular u v)
    (hroot : ∀ x, EllipticDivision.halvingPolynomial A B C u x ≠ 0)
    (Q : (completed A B C).Point) : (2 : ℤ) • Q ≠ Point.some hp := by
  intro hQ
  obtain ⟨x, hx⟩ := half_supplies_quartic_root A B C u v hp Q hQ
  exact hroot x hx

noncomputable def polynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | a::as => Polynomial.C a + Polynomial.X * polynomial as

theorem polynomial_eval (cs : List ℤ) (z : ℤ) :
    (polynomial cs).eval z = BoundedNative.horner cs z := by
  induction cs with
  | nil => simp [polynomial,BoundedNative.horner]
  | cons a as ih => simp [polynomial,BoundedNative.horner,ih]

theorem horner_emod (cs : List ℤ) (z M : ℤ) :
    BoundedNative.horner cs z % M = BoundedNative.horner cs (z%M) % M := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
    simp only [BoundedNative.horner]
    rw [Int.add_emod,Int.mul_emod,ih]
    conv_rhs => rw [Int.add_emod,Int.mul_emod,Int.emod_emod]

def residueFree (cs : List ℤ) (M : ℕ) : Bool :=
  (List.range M).all fun z => decide (BoundedNative.horner cs (z:ℤ) % (M:ℤ) ≠ 0)

theorem integer_root_free (cs : List ℤ) (M : ℕ) (hM : 0 < M)
    (hf : residueFree cs M = true) (z : ℤ) : BoundedNative.horner cs z ≠ 0 := by
  intro hz
  have h0 := Int.emod_nonneg z (show (M:ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos z (show (0:ℤ)<M by omega)
  have hr := of_decide_eq_true (List.all_eq_true.mp hf (z%(M:ℤ)).toNat
    (List.mem_range.mpr (by omega)))
  have he : ((z%(M:ℤ)).toNat:ℤ) = z%(M:ℤ) := Int.toNat_of_nonneg h0
  rw [he,← horner_emod,hz] at hr
  exact hr rfl

/-- A small residue scan proves absence of rational roots after checked monic scaling. -/
theorem rational_root_free (f : Polynomial ℚ) (cs : List ℤ) (q : ℚ)
    (hm : (polynomial cs).Monic)
    (hs : (polynomial cs).map (Int.castRingHom ℚ) = f.scaleRoots q)
    (M : ℕ) (hM : 0 < M) (hf : residueFree cs M = true) (r : ℚ) : f.eval r ≠ 0 := by
  intro hr
  obtain ⟨z,hz⟩ := EllipticDivision.scaled_root_integral f (polynomial cs) q r hm hs hr
  have he : ((polynomial cs).map (Int.castRingHom ℚ)).eval (z:ℚ) = 0 := by
    rw [hs,← hz]
    exact Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id ℚ) hr
  have hi : (polynomial cs).eval z = 0 := by
    have he' : (((polynomial cs).eval z : ℤ):ℚ) = 0 := by
      simpa only [Polynomial.eval_map,Polynomial.eval₂_at_intCast] using he
    exact_mod_cast he'
  exact integer_root_free cs M hM hf z (polynomial_eval cs z ▸ hi)

/-- Root-free branch cubics make doubling injective on the actual rational point group. -/
theorem doubling_injective (A B C : ℚ)
    (hr : ∀ x : ℚ, EllipticDivision.cubic A B C x ≠ 0) :
    Function.Injective (fun P : (completed A B C).Point => (2:ℤ) • P) := by
  have hk : ∀ P : (completed A B C).Point, (2:ℤ) • P=0 → P=0 := by
    intro P hP
    cases P with
    | zero => rfl
    | @some x y h => exact False.elim (hr x (two_torsion_root A B C x y h (by norm_num) hP))
  intro P Q h
  apply sub_eq_zero.mp
  apply hk
  have he := sub_eq_zero.mpr h
  simpa only [two_zsmul] using (show (2:ℤ) • (P-Q)=(2:ℤ) • P-(2:ℤ) • Q by simp only [two_zsmul]; abel).trans he

section Group
variable {G : Type*} [AddCommGroup G]

/-- Parity representatives suffice to close the complete rank-one/rank-two lattice at 2. -/
theorem pair_two_saturated (P Q : G)
    (hi : Function.Injective (fun g : G => (2:ℤ) • g))
    (hp : ∀ g : G, (2:ℤ) • g ≠ P)
    (hq : ∀ g : G, (2:ℤ) • g ≠ Q)
    (hpq : ∀ g : G, (2:ℤ) • g ≠ P+Q)
    (g : G) (m n : ℤ) (hg : (2:ℤ) • g=m • P+n • Q) :
    ∃ a b : ℤ, g=a • P+b • Q := by
  let a := m/2
  let b := n/2
  let t := g-(a • P+b • Q)
  have ht : (2:ℤ) • t=(m%2) • P+(n%2) • Q := by
    have hm : m=2*a+m%2 := by dsimp [a]; omega
    have hn : n=2*b+n%2 := by dsimp [b]; omega
    simp only [t,smul_sub,smul_add,smul_smul,hg]
    conv_lhs => rw [hm,hn,add_smul,add_smul]
    abel
  have hm : m%2=0 ∨ m%2=1 := by omega
  have hn : n%2=0 ∨ n%2=1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · have he : (2:ℤ) • g=(2:ℤ) • (a • P+b • Q) := by
      have hz : (2:ℤ) • t=0 := by simpa [hm,hn] using ht
      simpa only [t,smul_sub,sub_eq_zero] using hz
    exact ⟨a,b,hi he⟩
  · exact False.elim (hq t (by simpa [hm,hn] using ht))
  · exact False.elim (hp t (by simpa [hm,hn] using ht))
  · exact False.elim (hpq t (by simpa [hm,hn] using ht))

theorem cyclic_two_saturated (P : G)
    (hi : Function.Injective (fun g : G => (2:ℤ) • g))
    (hp : ∀ g : G, (2:ℤ) • g ≠ P)
    (g : G) (m : ℤ) (hg : (2:ℤ) • g=m • P) : ∃ a : ℤ, g=a • P := by
  let a := m/2
  let t := g-a • P
  have ht : (2:ℤ) • t=(m%2) • P := by
    have hm : m=2*a+m%2 := by dsimp [a]; omega
    simp only [t,smul_sub,smul_smul,hg]
    conv_lhs => rw [hm,add_smul]
    abel
  have hm : m%2=0 ∨ m%2=1 := by omega
  rcases hm with hm | hm
  · have he : (2:ℤ) • g=(2:ℤ) • (a • P) := by
      have hz : (2:ℤ) • t=0 := by simpa [hm] using ht
      simpa only [t,smul_sub,sub_eq_zero] using hz
    exact ⟨a,hi he⟩
  · exact False.elim (hp t (by simpa [hm] using ht))
end Group
end PerfectPower.MordellParity
