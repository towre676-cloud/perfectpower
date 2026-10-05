# Polynomial capacity: first Lean certificate layer

This follows the parallel polynomial-capacity push at `5cdb3dd`. Thirteen theorems in
`PerfectPower/PolynomialCapacity.lean` formalize its denominator transport,
finite-domain optimizer interpretation, Boolean cell composition and two tied
optimizer examples. All declarations are checked by Lean 4.20.0 and audited for
standard axioms. Run `scripts/check_polynomial_capacity.sh` in the pinned Lake
environment; it also runs the 25 polynomial-capacity Python tests.

## Transport and image

For nonzero integer D and positive exponent d, `denominator_transport` proves
D*y^d=N iff (D*y)^d=D^(d-1)*N. `witness_image` retains exactly the condition
D divides the transformed witness. `positive_denominator_order` proves that a
positive rational denominator preserves objective comparisons. `outer_cancel`
requires injectivity explicitly; shared nonlinear outer maps have no automatic
cancellation rule.

`content_power` proves exact removal of a nonzero perfect-power coefficient
content, including the necessary divisibility and the recovered integer witness.

## Descent certificates and all ties

`minimizers_in_candidates` applies even to infinite domains: a feasible point
outside the candidate predicate must have a strictly better feasible witness.
Then every global minimizer belongs to the candidates. This theorem does not
assert that a minimum exists.

`candidate_lower_bound` uses a finite feasible set and a descent witness for each
noncandidate to turn checked candidate values into a global lower bound.
`optimizer_iff` additionally requires attainment and identifies exactly every
candidate at the minimum value. These statements retain ties because descent
must be strict. `right_descent` and `left_descent` discharge the arithmetic step
from signed forward differences. The certificate producer must still prove that
the neighbor is feasible and that the relevant difference has the required sign.

`quartic_ties` proves that the global integer minima of x²(x−1)² occur exactly
at 0 and 1. `binomial_two_ties` proves the same for x(x−1) on nonnegative integer
indices; division by two preserves these optimizers. Both are direct unconditional
examples, independent of Python or a supplied Sturm certificate.

## Boolean cells

`Formula` represents sign atoms, constants, conjunction, disjunction and negation.
`boolean_cell` proves that any such formula is constant on a cell whenever every
atom has the same certified truth value there as at its sample. It does not prove
that a root-free cell has constant polynomial sign; that is a separate analytic
obligation.

## Remaining obligations

The Python execution still correctly reports `execution_verified: false`.
General Sturm variation, proof-producing sign transcripts, normalized-component
uniqueness,  full decomposition discovery and
unbounded-tail optimizer interpretation remain open. The finite-domain theorem
must not be applied to an infinite feasible set by silently discarding tails.
These thirteen laws are a checked interpretation layer, not a whole-compiler proof.
