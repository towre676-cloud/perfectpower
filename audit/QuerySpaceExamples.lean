import PerfectPower.CoefficientPowerCharts
import PerfectPower.RecurrenceDomains

namespace PerfectPower.QuerySpaceExamples

/-- A singular denominator can have multiple exact successors. -/
theorem singular_two_successors : ∀ b : ZMod 6,
    2*b=0 ↔ b=0 ∨ b=3 := by decide +kernel

/-- A singular denominator can also have no successor. -/
theorem singular_impossible : ∀ b : ZMod 6, 2*b ≠ 1 := by decide +kernel

def doublingStep (s : ZMod 7 × ZMod 7) : ZMod 7 × ZMod 7 := (s.1+1,2*s.2)

/-- Closed state evolution includes both index phase and sequence value. -/
theorem doubling_formula (n : ℕ) (s : ZMod 7 × ZMod 7) :
    doublingStep^[n] s = (s.1+n,2^n*s.2) := by
  induction n with
  | zero => simp [doublingStep]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [doublingStep,Nat.cast_add,Nat.cast_one,pow_succ]
    ext <;> ring

/-- The entire state, rather than the value alone, closes at period 21. -/
theorem doubling_cycle (s : ZMod 7 × ZMod 7) : doublingStep^[21] s = s := by
  rw [doubling_formula]
  have hc : (21 : ZMod 7) = 0 := by decide +kernel
  have hp : (2 : ZMod 7) ^ 21 = 1 := by decide +kernel
  simp [hc,hp]

/-- Every future hit predicate inherits the verified cycle. -/
theorem doubling_hits (hit : ZMod 7 × ZMod 7 → Prop) (n : ℕ) :
    hit (doublingStep^[n+21] (0,1)) ↔ hit (doublingStep^[n] (0,1)) := by
  simpa using PerfectPower.RecurrenceDomains.hit_period doublingStep (0,1) hit 0 21
    (by simpa using doubling_cycle (0,1)) n

end PerfectPower.QuerySpaceExamples
#print axioms PerfectPower.QuerySpaceExamples.singular_two_successors
#print axioms PerfectPower.QuerySpaceExamples.singular_impossible
#print axioms PerfectPower.QuerySpaceExamples.doubling_formula
#print axioms PerfectPower.QuerySpaceExamples.doubling_cycle
#print axioms PerfectPower.QuerySpaceExamples.doubling_hits
