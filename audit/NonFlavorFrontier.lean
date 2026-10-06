import PerfectPower.QuarticCollision
import PerfectPower.NativeRationalRoots
import PerfectPower.EllipticPointDivision
import PerfectPower.FiniteDomainCertificate
import PerfectPower.RectangularDeterminant
import PerfectPower.GeneralCRT
import PerfectPower.FactorialWindow
import Mathlib.Tactic.Linter.Lint

open PerfectPower Polynomial

-- The generator checks fractional roots; its completeness theorem is separate.
example : NativeRationalRoots.roots [-1,0,1] 2 = ({-1/2,1/2} : Finset ℚ) := by
  decide +kernel

-- Zero constants and repeated roots survive native integer enumeration.
example : NativeRationalRoots.roots [0,0,-1,0,1] 1 = ({-1,0,1} : Finset ℚ) := by
  decide +kernel

private theorem monic_cubic : (NativePolynomialSquare.polynomial [0,-1,0,1]).Monic := by
  have he : NativePolynomialSquare.polynomial [0,-1,0,1] = (X : Polynomial ℤ)^3-X := by
    simp [NativePolynomialSquare.polynomial]
    ring
  rw [he]
  exact monic_X_pow_sub (by simp)

-- All rational two-torsion on the actual curve y²=x³-x, including infinity.
example (P : (EllipticPointDivision.completed (0:ℚ) (-1) 0).Point)
    (hΔ : (EllipticPointDivision.completed (0:ℚ) (-1) 0).Δ ≠ 0) :
    (2:ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList 0 (-1) 0 hΔ
      (NativeRationalRoots.roots [0,-1,0,1] 1).toList := by
  apply EllipticPointDivision.native_torsion_complete 0 (-1) 0 hΔ [0,-1,0,1] 1
    (by norm_num) (by decide +kernel) monic_cubic
  simp [NativePolynomialSquare.polynomial, EllipticPointDivision.cubicPolynomial]
  ring

-- A nonmonotone image deduplicates values before computing ranks.
private def squares : FiniteDomainCertificate.Domain :=
  .image (.literal (Finset.Icc (-3) 3)) (fun x => x^2)
example : FiniteDomainCertificate.evaluate squares = ({0,1,4,9}:Finset ℤ) := by decide +kernel
example (y:ℤ) (hy:y ∈ FiniteDomainCertificate.evaluate squares)
    (hr:FiniteDomainCertificate.rank (FiniteDomainCertificate.evaluate squares) y = 2) : y=4 := by
  exact FiniteDomainCertificate.select_unique _ 2 y 4 hy (by decide +kernel) hr (by decide +kernel)

-- Noncoprime congruences combine at the lcm, not the product.
example (x:ℕ) : (x%6=1 ∧ x%9=4) ↔ x%18=13 := by
  have ha : Nat.ModEq 6 13 1 := by decide +kernel
  have hb : Nat.ModEq 9 13 4 := by decide +kernel
  constructor
  · rintro ⟨hx,hy⟩
    exact Nat.mod_lcm (hx.trans ha.symm) (hy.trans hb.symm)
  · intro hx
    have hxmod : Nat.ModEq 18 x 13 := hx
    exact ⟨(hxmod.of_dvd (by decide +kernel : 6∣18)).trans ha,
      (hxmod.of_dvd (by decide +kernel : 9∣18)).trans hb⟩
example : ¬∃ x:ℕ, Nat.ModEq 6 x 1 ∧ Nat.ModEq 9 x 2 := by
  rw [GeneralCRT.compatible_iff]
  decide +kernel

-- The native factorial window has a complete prime-valuation obstruction.
example (N W k p:ℕ) [Fact p.Prime]
    (h:¬ k ∣ padicValNat p (FactorialWindow.window N W)) :
    ¬∃ a:ℕ, a≠0 ∧ FactorialWindow.window N W=a^k := FactorialWindow.not_power p N W k h

-- Rectangular shape: three columns cannot be supported by two rows.
example (M:Matrix (Fin 3) (Fin 2) ℚ) (N:Matrix (Fin 2) (Fin 3) ℚ) :
    (M*N).det=0 := by
  classical
  rw [RectangularDeterminant.det_mul_injective]
  apply Finset.sum_eq_zero
  intro p hp
  have hi := (Finset.mem_filter.mp hp).2
  have hc := Fintype.card_le_of_injective p hi
  norm_num at hc

#print axioms PerfectPower.NativeRationalRoots.roots
#print axioms PerfectPower.NativeRationalRoots.complete
#print axioms PerfectPower.NativeRationalRoots.normalize
#print axioms PerfectPower.NativeRationalRoots.normalize_root_iff
#print axioms PerfectPower.NativeRationalRoots.complete_nonmonic
#print axioms PerfectPower.EllipticPointDivision.completed
#print axioms PerfectPower.EllipticPointDivision.equation_completed
#print axioms PerfectPower.EllipticPointDivision.double_eq_zero_iff
#print axioms PerfectPower.EllipticPointDivision.affine_two_torsion_iff
#print axioms PerfectPower.EllipticPointDivision.two_torsion_root
#print axioms PerfectPower.EllipticPointDivision.actual_doubling_x_iff
#print axioms PerfectPower.EllipticPointDivision.branchPoint
#print axioms PerfectPower.EllipticPointDivision.torsionList
#print axioms PerfectPower.EllipticPointDivision.torsion_list_complete
#print axioms PerfectPower.EllipticPointDivision.cubicPolynomial
#print axioms PerfectPower.EllipticPointDivision.eval_cubicPolynomial
#print axioms PerfectPower.EllipticPointDivision.native_torsion_complete
#print axioms PerfectPower.EllipticPointDivision.native_halves_complete
#print axioms PerfectPower.FiniteDomainCertificate.Domain
#print axioms PerfectPower.FiniteDomainCertificate.meaning
#print axioms PerfectPower.FiniteDomainCertificate.evaluate
#print axioms PerfectPower.FiniteDomainCertificate.evaluate_complete
#print axioms PerfectPower.FiniteDomainCertificate.rank
#print axioms PerfectPower.FiniteDomainCertificate.rank_strict
#print axioms PerfectPower.FiniteDomainCertificate.select_unique
#print axioms PerfectPower.FiniteDomainCertificate.source_select_unique
#print axioms PerfectPower.RectangularDeterminant.det_mul_expansion
#print axioms PerfectPower.RectangularDeterminant.repeated_selection_zero
#print axioms PerfectPower.RectangularDeterminant.det_mul_injective
#print axioms PerfectPower.GeneralCRT.compatible_iff
#print axioms PerfectPower.GeneralCRT.anchor
#print axioms PerfectPower.GeneralCRT.intersection_iff
#print axioms PerfectPower.GeneralCRT.anchor_lt
#print axioms PerfectPower.FactorialWindow.window
#print axioms PerfectPower.FactorialWindow.valuation
#print axioms PerfectPower.FactorialWindow.legendre_window
#print axioms PerfectPower.FactorialWindow.not_power

#print axioms PerfectPower.GeneralCRT.integer_intersection_iff

#lint in PerfectPower.NativeRationalRoots
#lint in PerfectPower.EllipticPointDivision
#lint in PerfectPower.FiniteDomainCertificate
#lint in PerfectPower.RectangularDeterminant
#lint in PerfectPower.GeneralCRT
#lint in PerfectPower.FactorialWindow

#print axioms PerfectPower.QuarticCollision.value
#print axioms PerfectPower.QuarticCollision.collision_identity
#print axioms PerfectPower.QuarticCollision.collision_iff
#print axioms PerfectPower.QuarticCollision.circle_bounds

#lint in PerfectPower.QuarticCollision
