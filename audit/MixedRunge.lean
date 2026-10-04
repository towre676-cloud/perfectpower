import PerfectPower.MixedRunge
import PerfectPower.QuadraticProjection
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PerfectPower

theorem mixed_points_eq : MixedRunge.points = {(-1,-4),(-1,-1),(-1,1),(-1,2)} := by decide

theorem mixed_explicit (x y : ℤ) : MixedRunge.equation x y ↔
    x = -1 ∧ (y = -4 ∨ y = -1 ∨ y = 1 ∨ y = 2) := by
  rw [MixedRunge.complete,mixed_points_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  tauto

example : True := by
  fail_if_success have : MixedRunge.equation (-1) 0 := by decide
  trivial

#print axioms MixedRunge.projection
#print axioms MixedRunge.coordinate_bound
#print axioms MixedRunge.complete
#print axioms mixed_points_eq
#print axioms mixed_explicit
#print axioms QuadraticProjection.roots_iff
