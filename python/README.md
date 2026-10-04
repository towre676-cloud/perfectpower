# `perfectpower` (Python, standard library only)

The package installs from the repository root with `pip install .` and provides the `perfectpower` command. The CLI and the function API are stable within the 0.6 series.

## Function API

| Function | Returns | Status of the result |
|---|---|---|
| `atlas.classify(F, d)` | Type (`power`, `radical`, `pell`, `finite`, `constant`), $t$-profile, growth, exponent, $\kappa$, effectivity | Paper proofs; the finite type rests on Siegel through Theorem G |
| `atlas.structural_hits(F, d, N)` / `structural_count(F, d, N)` | Exact hits or count up to $N$ from the structure theorems | Paper proofs, cross-checked by scans |
| `runge.runge_enumerate(F, d)` | Complete hit list for rigid $F$ | Theorem R plus exact arithmetic |
| `lean_emit.emit(name, F, d)` / `lean_sandwich.emit_sandwich(name, F, d)` | Lean source of a hit-set theorem | Becomes a theorem only once Lean compiles it |
| `compiler.compile_constraint(C)` | A plan for $F(n)=m^d$, a triangular constraint or a quadratic-root constraint: exact reductions, solver, status (`COMPLETE_FINITE`, `STRUCTURED_INFINITE`, `STRUCTURED_FILTERED`, `CLASSIFIED_FINITE`, `NOT_ENUMERATED`), justification, `contains` / `iter_hits` / `count` / `all_hits` / `bounded_evidence` | Reductions: Lean (`Reduction.lean`). Solvers: as cited per plan. Execution: tested, not verified |
| `specialize.specialize(LoopProgram)` | A standalone program replacing a brute-force loop, and the loop itself | Differential tests against the loop |
| `factor.factor_squarefree(f)` | Irreducible factors over $\mathbb Z$ of a squarefree primitive polynomial (Berlekamp–Zassenhaus; each factor verified by exact division) | Exact, tested |
| `galois.galois_profile(F, d)` | Galois orbits of the roots per multiplicity layer (irreducible factors over $\mathbb Q$; groups up to degree 4, root fields), the real unit fields of Pell branches, and the reason for the type | Explanatory; agrees with `classify` on the tests |
| `atlas.integerize(F, d)` | Integer polynomial with the same hits as an integer-valued $F\in\mathbb Q[x]$ | Elementary |
| `atlas.shift_spectrum(S, d)` | Critical shifts and the type of $S+k$ | Finite type rests on Siegel through Theorem G |
| `exponential.exponential_progression(c, a, d)` | Hit progression of $c\,a^n$ | Theorem E |

Coefficients are always low-to-high.

Infinitude and growth labels use exact residue or Pell-orbit arithmetic. The JSON
`kappa` field is a floating-point approximation; if a positive constant is too
small to represent, it is `null` and `kappa_exact` carries the expression instead.
Do not interpret `null` as a zero constant.

## CLI

The CLI exposes these commands:

- `scan`
- `classify`
- `count`
- `enumerate`
- `lean` (with `--method runge|sandwich`)
- `shifts`
- `certificate`, `verify` and `surgery`, kept from v0.5

Each command takes `--coeff` and `--d`. For an end-to-end example, see `docs/TUTORIAL.md`.

## Target-conditioned arithmetic information

`perfectpower.information.InformationProblem` returns ambiguity witnesses and minimum-cost sufficient observation sets on explicitly finite domains, with a target decoder and work budgets. `AffineTransport` preserves rational inverse and intermediate integrality restrictions. `compile_square_query` consumes complete or partial divisor charts without treating unresolved fibres as empty. The `information` CLI compiles bounded polynomial residue decoders. See [the mathematical chapter](../docs/ARITHMETIC_INFORMATION_COMPILER.md) and `python/information_receipt.py` for signed-unit integration and reproducible results. This is exact Python execution, not a Lean certificate or a global exponent bound.

## Covering obstructions and integral presentations

`covering` replays Fisher's explicit 571a1 example using exact cubic-algebra identities, local witnesses, Hensel lifting and Hilbert symbols; global interpretation is source-backed, not Lean-certified. Its two-isogeny covering functions check rational point maps. `integral_lattice` computes determinantal divisors, Smith factors, prime-power lengths and inverse-image congruences; `orbit_lattice.order_image_allowed` integrates those congruences with the existing unit sieve. `decomposition` checks supplied compositions without unjustified outer cancellation. Console commands are `covering-replay` and `lattice`. See [the complete mathematical chapter](../docs/COVERING_LATTICE_MONOGRAPH.md) and `python/covering_lattice_receipt.py`.

The compiler now recognizes effective quartic linear perturbations and square-leading quartics with nonzero normalized remainder. `python -m perfectpower solve --expr='n**4+n**3+n**2+n+1' --d=2 --N=1000000` returns the complete positive-input answer. `python -m perfectpower lean --coeff=1,1,1,1,1 --d=2 --name=repunit` emits a kernel-checked native point theorem. See `docs/QUARTIC_EFFECTIVE_SOLVER_MONOGRAPH.md` and the two new check scripts.


### Complete integer lifts and query projection

`integer_lifting.solve_integer(A,b)` returns every integer solution as a particular vector plus a saturated integer kernel, or a concrete divisibility/image obstruction. `integral_task_section`, `integral_intertwiners` and `compare_column_lattices` use the same replayable unimodular certificates. These are exact Python calculations, not new Lean proofs.

```sh
PYTHONPATH=python python -m perfectpower integer-lift --matrix '[[2,3]]' --vector '[1]'
PYTHONPATH=python python -m perfectpower integral-task-section --carrier '[[2,3]]' --target '[[1,5]]'
PYTHONPATH=python python -m perfectpower integer-project source.smt2 --output projected.smt2 --certificate-output certificate.json
python python/recover_integer_lifting.py --z3
```

The query route eliminates direct affine equalities over the integers and preserves every residual constraint. Its model-lifting API reconstructs original coordinates from fresh integer parameters. See [the complete explanation](../docs/INTEGER_LIFTING_MONOGRAPH.md).
The divisor-sum application is available through `python -m perfectpower divisor-sum --factors '[[2,1],[11,1]]'` and `python -m perfectpower sigma-quartic --shift 0`. Rebuild the full results collection from the repository root with `PYTHONPATH=python python python/build_divisor_sum_atlas.py`. See `docs/DIVISOR_SUM_RESULTS_MONOGRAPH.md` for global-versus-bounded scope and proof status.

`branched-geometry --coeff=0,-1,0,0,0,1 --d=2 --connection --cells` computes normalization invariants, an exact faithful connection Laplacian and a canonical cell model. `--k` shifts the constant coefficient. Topology supports exponents through 64; exact cyclotomic matrices have an explicit smaller work limit. See [the monograph](../docs/BRANCHED_GEOMETRY_MONOGRAPH.md) and `python/build_branched_geometry.py` for the full atlas.
