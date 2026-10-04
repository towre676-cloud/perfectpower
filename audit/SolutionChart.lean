import PerfectPower.NativeSquareChart

open PerfectPower PerfectPower.NativeSquareChart

private def full := chart [-1,0,1] 1 (by decide) (by decide) (by decide)
  (NativeDivisorSquare.values 1) (fun _ h => h)

private def incomplete := chart [-1,0,1] 1 (by decide) (by decide) (by decide)
  {(0,1)} (by decide)

example : full.known = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide
example : full.parameters.card = 2 := by decide
example : full.known.card = 4 := by decide
example : incomplete.known = {(-1,1),(1,1)} := by decide
example : incomplete.residual = {(0,-1)} := by decide
example (z : ℤ × ℤ) : relation [-1,0,1] 1 z ↔
    z ∈ incomplete.known ∨
      (relation [-1,0,1] 1 z ∧ parameter [-1,0,1] z ∈ incomplete.residual) :=
  incomplete.partition z
example (z : ℤ × ℤ) : relation [-1,0,1] 1 z ↔ z ∈ full.known :=
  full.complete (by decide) z
example : full.known.card = ∑ b ∈ full.solved, (full.fibre b).card :=
  full.card_known
example (z : ℤ × ℤ) :
    z ∈ (full.transport (Equiv.prodComm ℤ ℤ)).known ↔ (z.2,z.1) ∈ full.known :=
  full.transport_known (Equiv.prodComm ℤ ℤ) z

example : True := by
  fail_if_success have : full.known.card = full.parameters.card := by decide
  fail_if_success have : incomplete.residual = ∅ := by decide
  trivial

#print axioms SolutionChart.Chart.partition
#print axioms SolutionChart.Chart.known_iff
#print axioms SolutionChart.Chart.complete
#print axioms SolutionChart.Chart.complete_iff
#print axioms SolutionChart.Chart.context_partition
#print axioms SolutionChart.Chart.fibres_disjoint
#print axioms SolutionChart.Chart.card_known
#print axioms SolutionChart.Chart.transport_known
#print axioms NativeSquareChart.fibre_exact
#print axioms NativeSquareChart.full_known
