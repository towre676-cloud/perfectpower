# Geometric Langlands: reusable proof structure

PerfectPower turns searches for whole-number powers into reusable answers with proofs that no solutions were missed. This change makes partial work reusable too: it records which reduced cases are solved, which remain, and how every original solution is recovered. A stopped computation leaves a precise mathematical obligation instead of an ambiguous empty answer.

## Primary sources and reading scope

The source is the authors' [five-paper proof collection](https://people.mpim-bonn.mpg.de/gaitsgde/GLC/). This investigation studied the introductions and dependency structure of all five papers, with selected construction, compatibility, residual-reduction, multiplicity, and arithmetic-scope passages. It is not an independent verification of every technical proof. Related personal notes were not treated as evidence for new mathematics.

| Paper and passages | Mechanism studied | Design inference for this repo |
|---|---|---|
| [I: Construction](https://people.mpim-bonn.mpg.de/gaitsgde/GLC/functor.pdf), introduction and §1.4 | Construct the comparison functor through Whittaker coefficients; formulate categorical equivalence. | State the parameter map and prove coverage. |
| [II: Localization](https://people.mpim-bonn.mpg.de/gaitsgde/GLC/Loc.pdf), introduction §0.2; Theorems 6.1.4, 18.5.2 | Critical local equivalence and compatibility with global localization. | Representation changes must preserve reconstruction. |
| [III: Eisenstein](https://people.mpim-bonn.mpg.de/gaitsgde/GLC/Eis.pdf), introduction §0.2; Theorems 15.1.2, 17.1.2 | Handle the Eisenstein/reducible sector; reverse compatibility needs a separate proof. | Coverage and reconstruction are separate obligations. |
| [IV: Ambidexterity](https://people.mpim-bonn.mpg.de/gaitsgde/GLC/ambidex.pdf), introduction §0.1; Corollary 1.3.10 | Reduce the remaining equivalence to the cuspidal/irreducible sector. | Describe the residual sector exactly. |
| [V: Multiplicity one](https://people.mpim-bonn.mpg.de/gaitsgde/GLC/multone.pdf), §§0.1–0.4, 5.5, 8.10 | Completion reduces to the unit algebra; multiplicities are controlled componentwise. Finite-field arithmetic assumes an additional ℓ-adic conjecture. | Preserve fibre cardinalities; do not assume one lift per parameter or a new integer-point theorem. |

These are engineering inferences, not Geometric Langlands corollaries. The finite-set theorems below follow independently from their stated hypotheses. They do not formalize sheaves, categories, opers or the Langlands equivalence. `Chart.transport` is a source-set equivalence, not categorical ambidexterity. The characteristic-zero theorem does not supply an algorithm for arbitrary integer points.

## Implemented mathematics

`PerfectPower/SolutionChart.lean` defines a finite exhaustive parameter cover with a subset whose source fibres are completely reconstructed. `partition` proves every solution is known or lies over a named residual parameter. `context_partition` retains arbitrary extra source constraints. `complete` closes an empty residual; `complete_iff` proves that completion is equivalent to absence of source solutions over the residual. A nonempty parameter residual can have empty fibres: it is an obligation, not a promised solution.

Distinct parameter fibres are disjoint. `card_known` proves the number of known points equals the sum of fibre cardinalities. `transport_known` preserves membership under a genuine source equivalence. Unlike the existing `Reduction.Exact` partial inverse, this interface explicitly supports multiple source solutions per parameter and unresolved fibres.

`PerfectPower/NativeSquareChart.lean` instantiates the contract for `y² = P(x)² + k`, for any nonconstant integer polynomial and nonzero integer k. The parameter is `(P(x),y)`. Existing divisor theorems prove its finite cover; integer-root theorems prove exact reconstruction for any chosen subset of closed parameters. Closing every parameter recovers the existing complete solver.

For `P(x)=x²−1`, `k=1`, two parameters `(0,−1)` and `(0,1)` each have two lifts: four original points. The Lean audit checks this, a partial chart, coordinate swapping, and rejection of false parameter-count and residual-closure claims.

## Executable partial analysis

```python
from perfectpower.divisor_square import analyse
result = analyse([-1, 0, 1], 1)
assert result['known_cardinality'] == 4
assert result['status'] == 'COMPLETE'
stopped = analyse([1_000_000, 1], 1, fibre_work_limit=10)
assert stopped['status'] == 'PARTIAL'
assert stopped['residual_parameters'] == [(0, -1), (0, 1)]
```

`analyse` completes parameter coverage first; exhausting that budget raises `WorkLimit`. Each polynomial value then gets an independent fibre budget. Exhausting it leaves the entire fibre unresolved. Closed empty fibres count as solved, repeated roots count once, and distinct points retain their multiplicity over parameters.

Python returns `execution_verified=False`: algorithmic status is not an instance-specific Lean certificate. The general contract and concrete audit are independently kernel checked. This patch does not add a certificate emitter for arbitrary partial Python outputs.

Run `bash scripts/check_solution_chart.sh` with the pinned Lean toolchain and dependencies. It builds the two modules, checks the audit and prints theorem axioms, and runs eight Python tests including 100 randomized comparisons with the complete solver. Allowed axioms are `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` is admitted.

## Next extension

The chart can receive proved complete branches from norm/Thue descent and leave unsolved branches as a precise residual. Each integration still requires its own coverage and fibre proofs. That integration is a next step; the present patch supplies the reusable interface and a working arithmetic instance.
