# A compositional arithmetic simplifier

PerfectPower now offers one interface for useful exact information even when
complete global integer-point enumeration is unsupported. This is an initial
integrated compiler, not completion of every research direction in the roadmap.

## Public interfaces

`ArithmeticEngine.analyze(coefficients, degree, interval=...)` and
`perfectpower.simplifier.analyze_power` return a global solving result, a complete
necessary residue cover, an optional bounded result, and the residual equation.
A globally unresolved result can coexist with a complete bounded result. Budget
exhaustion never returns a partial list labelled complete. Existing `solve`
results now retain their necessary residue certificate when unresolved.

`answer_points` answers coordinate inequalities, equality, modular predicates,
and uniqueness. Complete bounded answers carry their x interval. Necessary
residue restrictions can establish global modular properties without global
point enumeration. A counterexample is an actual solution in the declared
scope. Empty complete sets are distinguished from unique observables.

`polynomial_pullback(outer, inner, degree)` checks the exact composition and
lifts every complete outer solution through a complete integer-root certificate
for `inner(x)=u`. Inner polynomials must be nonconstant. Missing outer bounds or
exceeded fibre budgets return unresolved. Shared nonlinear outer polynomials
are never cancelled. This accepts supplied decompositions; discovering general
functional decomposition remains open.

`simplify_query` accepts the validated existential QF_NIA fragment already used
by integer projection. Its portfolio composes square–cube parameterization,
other equal-coefficient coprime power relations, acyclic direct definitions,
integer affine lattices, finite positive monomial systems, and the registered
complete finite arithmetic relations. It substitutes into every remaining
assertion and repeats until no cost-accepted dimension reduction applies or the
round budget expires. Branch expansion and output growth are bounded. Final
necessary local filters are explicitly added to supported univariate residual
power relations. Every residual assertion and variable is retained as needed.

`lift_model` reverses the accepted steps and checks every original assertion.
The returned original assignment is a sufficient witness. It rejects assignments
that fail a side condition. Euclidean SMT integer division is evaluated exactly;
division by zero is rejected because its SMT value is underspecified.

`verify_analysis`, `verify_pullback`, and `verify_simplification` replay the
advertised data. These are Python checks, not kernel acceptance. Callers should
verify untrusted serialized results before consuming their deductions. The
SMT relation recognizer uses the existing degree-eight polynomial normalizer;
the coefficient-based arithmetic analysis supports degree 64.

## CLI

Run with `PYTHONPATH=python python -m perfectpower`.

```
analyze-power --coeff '[1,0,0,0,1]' --verify --question '{"coordinate":"x","op":"unique"}'
polynomial-pullback --outer '[1,0,0,0,1]' --inner '[0,1,1]' --verify
simplify-query --script '(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)(assert (= (* x x) (* y y y)))(assert (> x 3))(check-sat)' --model '{"_pp_power":2}' --verify
```

## Lean composition laws

`PerfectPower/ArithmeticSimplifier.lean` proves eight reusable laws. The general
coprime integer-power theorem handles zero and signs through a rational
parameter whose denominator is proved to be one. Arbitrary caller predicates
can be transported through exact parameterizations, direct definitions,
necessary restrictions, and complete polynomial pullbacks. Shared outer fibres
are kept as two variables with an explicit outer equality. Bounded and global
question laws require their appropriate hypotheses.

The eight declarations compile against the pinned Lean/Mathlib toolchain. Seven
use no axioms; coprime-power parameterization uses only `propext`,
`Classical.choice`, and `Quot.sound`. `audit/ArithmeticSimplifier.lean` prints the
exact dependencies, and `scripts/check_arithmetic_simplifier.sh` recompiles and
checks the focused audit. These laws establish mathematical composition given
their premises; they do not prove the Python compiler implementation or turn
Python certificates into automatically accepted Lean proofs.

## Evidence and performance scope

The focused tests check a globally unsupported degree-64 power equation against
an independent exhaustive bounded scan; scope handling; budget rejection;
replay tampering; integer-image obstructions; complete polynomial fibres;
noninjective outer noncancellation; parameter freshness; general coprime powers;
model lifting; and original/reduced query answers with Z3.

`python/benchmark_simplifier.py` records integration measurements separately
from correctness. The coupled square–cube example removes two of three integer
variables. An inconsistent affine subsystem eliminates both variables and
produces false. A residual nonlinear example receives local congruences.
For `y^10=x^64+x+1` on [-1000,1000], global solving remains unresolved while
the bounded answer is complete: 221 wheel candidates lead to three root
extractions across 2001 integers. These are internally constructed examples,
not an independently sourced performance corpus or evidence of general speedup.

## Remaining fronts

Coefficient-bearing infinite monomial families, general norm parameterizations,
automatic polynomial decomposition discovery, compact finite-disjunction model
sharing, full question-directed theorem discovery, general height methods, and
end-to-end kernel certificates for every compiler execution remain open.
Existing exact optimization, observable-machine, and graph-event APIs remain
available through their established CLI routes; no new cross-application
performance claim is made. A general classical Sturm counting theorem and
cyclotomic graph probability derivation also retain their existing open status.
Parallel commit `68b61c4` landed during development and was integrated without
removing its witness-resolvent or connection-reweight interfaces. Seven further
Lean theorems now cover formal-series uniqueness from constant-one denominators,
cross-product equality and all coefficients, the actual all-power formal series over an arbitrary (possibly noncommutative)
ring as both inverse resolvents, plus both sides of the rectangular
Woodbury inverse repair over an arbitrary ring. These require explicit checked
base and defect inverse identities. They do not prove the general determinant
lemma, cyclotomic support-rank formula, Krylov discovery, or every saved numeric
receipt. Four compiled Lean examples also check the coupled system, negative
coprime-power witness, noncancellation and an expanded pullback identity.

The integrated Python test run includes the new parallel tests: 725 tests run,
721 passed, four existing optional Lean tests skipped. The focused Lean audit
checks 19 new theorems (15 reusable statements and four examples), all with only
standard axioms. A full historical repository Lean rebuild was not run locally.
