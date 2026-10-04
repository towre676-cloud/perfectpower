# Arithmetic information compiler

The compiler asks which arithmetic readouts suffice for the caller's target on an explicitly finite domain. It constructs every pair of states with different target labels. An observation covers a pair exactly when its readouts differ. A sufficient observation set covers all disagreeing pairs. This is a weighted set-cover problem, solved exhaustively under explicit pair and subset budgets. A completed search returns an optimum among the supplied observations, using additive integer costs, with a decoder from readouts to target labels. Existing observations are sunk costs. Ties use fewer additional observations and declaration order. Budget exhaustion raises rather than returning an alleged optimum.

This transfers Formation's shadow/lift distinction, WIND's ambiguity pairs, and Wilson's task-specific decoding into the integer package. It does not require reconstruction of the full arithmetic state. `ambiguity(existing)` returns two actual domain states with equal existing readouts and unequal target labels, together with every available observation separating that pair. `compile(existing)` covers all disagreeing pairs, not merely the first witness. If the supplied observations cannot suffice, the result is `UNSEPARABLE` with a collision surviving all observations.

## Execution and scope

`python/perfectpower/information.py` is exact Python, not verified execution or a new Lean theorem. The caller supplies hashable states, deterministic hashable target labels, and deterministic observations; each is evaluated once. Sufficiency and optimality refer exclusively to the enumerated states, target, observations and declared costs. A residue decoder learned on a bounded interval cannot be extended to all integers. Observations have no implicit mathematical cost model: the caller must specify meaningful costs. Planning is quadratic in the number of states and exponential in the number of candidate observations. Limits are part of the API.

The installed CLI is:

```sh
perfectpower information --coeff=-2,0,0,1 --d 2 --lo -100 --hi 101 --moduli 2,3,5,7,11,13
```

This computes exact square membership for x³−2 on the stated interval, then chooses a minimal residue decoder from the supplied moduli. It reports moduli 11 and 13 as sufficient on those 201 integers. That is a finite decoder, not a claim that these congruences establish the global Mordell solution theorem, nor a faster solver: exact target labels were computed first.

## Integration with signed unit sieves

`orbit_lattice.information_plan` consumes the existing `allowed` conditions and full matrix periods. It evaluates plane, affine lattice, and optional extra divisibility readouts on all exponent residue classes. Negative exponents retain the existing interpretation by reduction modulo certified matrix periods. For D=72, units (−1,−3,1) and (−1,0,2), seed (−3,−3,1), modulus 9, leading coefficient −3 and plane (0,1,0), both periods are 18. Across 324 residue classes, 108 pass the combined condition. The plane test alone suffices; the lattice readout adds no information for this particular finite target. No global exponent bound is supplied or inferred. Matveev and other global premises remain separate.

## Transport domains and counts

`AffineTransport` implements diagonal rational affine maps using exact `Fraction` arithmetic. `pullback` requires integral source coordinates. `first.then(after)` means after composed with first, in execution order. `pullback_chain` additionally requires an integral intermediate coordinate. This distinction is essential: x↦x/2↦2(x/2) has identity composite, but odd integral x pass through a nonintegral intermediate. A composite inverse alone would lose that restriction. The API does not claim to cover arbitrary matrices, nonlinear maps, curve residual identities, or all localization worlds.

Finite multiplicity measures retain counts under merging maps. This module explicitly defines Δ_f = f#μ − ν for supplied source and target measures. For an intermediate measure ν and target ω, linear pushforward gives Δ_(g∘f) = g#Δ_f + Δ_g. `push_counts` allows signed defect measures; `transport_defect` requires nonnegative integer input multiplicities. This finite, explicit definition recovers the older transport-defect idea without presuming the missing archive's definitions. Repeated representatives are never silently discarded.

## Existing solution charts

`compile_square_query` consumes `divisor_square.analyse` for y²=P(x)²+k. A known point satisfying the caller's predicate yields SAT even when other fibres are unresolved. No satisfying known point yields UNSAT only when the complete chart has no residual parameters. Otherwise it yields UNRESOLVED with the original residual parameters. Predicates are caller-supplied exact Python functions, not parsed SMT or proof-producing Lean formulas. Existing theorem contracts are preserved as references, with `execution_verified=False`.

## Reproduction and validation

Run `PYTHONPATH=python python python/information_receipt.py` to reproduce the integration receipt. Run `PYTHONPATH=python python -m unittest discover -s python/tests` for the package suite. The new tests compare weighted optima with an independent partition-based exhaustive search on 80 deterministic random fixtures, test actual ambiguity witnesses, merging multiplicities and the defect composition identity, noncommuting affine execution order, intermediate integrality, exact chart residual behavior, and finite polynomial decoding. Existing signed-sieve tests independently compare negative and positive exponent powers to period tables.

The current release intentionally leaves general Baker bounds, arbitrary-polynomial completeness, nonlinear transport compilation, OEIS recurrence discovery, and automatic SMT integration open. The reusable decision and domain layers are implemented rather than those further research programs being declared complete.

Validation on base commit `57435bb`: the full Python suite passed 373 tests with four skips in 41.406 seconds. Two additional tests were then added for the actual D=72 integration and 100 randomized rational transport pairs; the final focused run passed all 24 tests spanning this module, signed unit sieves and solution charts. CLI execution, receipt generation, Python compilation and whitespace checks passed. No Lean files changed and no Lean build was run.
