# Structural mathematics handoff

Read `docs/STRUCTURAL_MATH_MONOGRAPH.md` for mathematics, source recovery, examples and guarantee boundaries. Run `make structural-math` for the focused tests and the reproducible corpus. The new core is standard-library-only.

`python/perfectpower/species.py` owns canonical exponent tuples, occupation coordinates, divisor invariants, integer factorization and bounded count/select/rank. `populations.py` adapts the species engine to the existing catalogue, sampling, partition, export and bounded scalar-optimization interfaces. Restriction and comparison are intentionally rejected for species until their semantics have a dedicated implementation.

`python/perfectpower/inequality_certificates.py` owns rational LDL, polynomial Gram witnesses, constrained lower bounds, quadratic minimizers, real Toeplitz frontiers and linear Lyapunov metrics. It reuses `psg_polynomial.py` and `exact_linear.py`. Source and domain binding are checked during replay. Higher-degree witness discovery and nonlinear contraction are not present.

`python/perfectpower/descent_squareclasses.py` owns signed squarefree divisors, homogeneous covers, finite primitive local charts, real obstructions, point transport and both-sided two-isogeny rank bounds. A local survivor is unresolved. The rank formula uses classical descent, not a compiled Lean theorem; rank zero is exact when the upper bound is zero. Positive bounds are not exact ranks or complete bases.

`structural_math_cli.py` registers the public commands through `__main__.py`. `python/tests/test_structural_math.py` contains independent arithmetic checks and packet-tampering cases. `python/develop_structural_math.py` generates every scientific receipt in `receipts/structural_math/`. No new schema is allowed to claim formal verification without an actual formal acceptance path.

The next useful extensions are complete species-set restriction semantics, rational Gram witness discovery with separately checked output, prime-adic lifting with precise stop conditions, and Lean foundations for the existing rational certificate identities. Keep budgets explicit; never turn state exhaustion or finite local survival into completeness.
