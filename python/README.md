# `perfectpower` (Python, standard library only)

`CompletionPlanner` compiles `allocation` or `words` specifications and exposes `count`, `completions(prefix)`, `select(rank)`, `rank(point)`, `sample`, `optimize` and `page`. Set `optimal=True` on rank/selection/sample/page to use the complete global maximizer population. Resource allocations support several capacity intervals, bounded quantity/residue domains and optional finite compatibility machines; ordered action words have positive costs and an exact budget. The planner automatically selects a supported route or raises a work-limit error. `with_resources` reuses compatible DP entries in a new immutable definition. Register catalogue kind `completion_planner`, or run `python -m perfectpower plan examples/planning/petersen_6.json`. See [the planner account](../docs/COMPLETION_PLANNING_MONOGRAPH.md) for the schemas and benchmark scope.

Exact implementation families, three transport semirings, future-state quotients, cross-model equivalence, polynomial charts and optimal resettable diagnosis are available through the six `soe-*` commands. See `docs/SOE_BRIDGE_MONOGRAPH.md` in the source checkout; reproduce with `make soe-bridge`.

`perfectpower.psg_algebra` supplies `quadratic_reduce`, `check_quadratic`, `reconstruct_quadratic`, `darboux_certificate`, `check_darboux`, `ideal_certificate`, `dependency_profile`, `observable_fibre` and `affine_norm_population`. `psg_jets` supplies exact finite composition, curvature jets, Schröder residuals and `differential_model_space`. The [PSG guide](../docs/PSG_STRUCTURAL_MONOGRAPH.md) records exact domains, singular branches and current proof status. For example, `python -m perfectpower psg-norm --variables x,y --A '2*x+1' --B y --D 2 --norm -1 --cutoff 30` returns the complete original integer population within `abs(y)<=30`.

`perfectpower.population_algebra.PopulationComparison` compares two predicates inside one supported finite `ExactPopulation` universe. Use `summary()`, `count(part)`, `select(part, rank)`, `locate(parameter=...)` or `locate(x=..., y=...)`, `transport(source, rank, target)`, `classify(record, source=...)`, `page`, `sample`, `optimize` and `evidence`. Parts are `universe`, `left`, `right`, `both`, `left_only`, `right_only`, `neither`, `union` and `symmetric_difference`. Original coordinates or parameters determine identity; ordinal ranks and projected values do not. See the [population algebra monograph](../docs/POPULATION_ALGEBRA_MONOGRAPH.md) for the exact contracts and examples. Register catalogue kind `population_comparison`, or run `python -m perfectpower population-compare --spec receipts/population_algebra/huge-curve-spec.json --transport '["right_only",0,"universe"]'`. The local HTTP service exposes the source checkout's walkthrough at `/atlas` and retains raw integer response digits.

The [semilinear and curve-query guide](../docs/SEMILINEAR_CAPACITY_MONOGRAPH.md) documents the newest complete-domain interfaces. `perfectpower.semilinear_domains` supplies `semilinear_domain`, `count_domain`, `select` and `optimize_semilinear` for Boolean polynomial/modular predicates. `perfectpower.curve_queries.query_curve` counts and optimizes supported signed power curves in their original coordinates. `perfectpower.arithmetic_families.family_points` evaluates every original integer fibre of a composed generator at one parameter. Each layer has an exact evidence-replay function; Python execution remains unverified.

`perfectpower.query_space.CurveSpace` compiles a coefficient-bearing power family once and supports repeated `query` and cached `evaluate` calls. `perfectpower.recurrence_domains` provides modular recurrence orbits, exact hit counts, rank selection and polynomial index optimization, retaining singular denominators explicitly. See the [query-space guide](../docs/QUERY_SPACE_MONOGRAPH.md).

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

## Positive geometry extension

New console routes are `collision-atlas`, `associahedron`, `legendre`, `branch-form`, `connection-polytope`, `descartes-orbit`, `period-normalize` and `branch-signs`. Exact rational inputs may be strings such as `"2/7"`; floats are rejected in this extension. The connection route supports loops, parallel edges, zero-weight outages and a `--costs` minimum-cost basis route that avoids enumerating every maximal minor. See [the monograph](../docs/POSITIVE_GEOMETRY_MONOGRAPH.md) for complete conventions and examples. The standalone corpus builder is `python/build_positive_geometry.py`, and `scripts/check_positive_geometry.sh` runs the focused mathematical checks and rebuilds all records.

`python -m perfectpower branched-geometry --coeff=0,-1,0,0,0,1 --d=2 --differentials` constructs the explicit component basis. `python -m perfectpower legendre-period-bounds --lambda 1/2 --terms 80` encloses normalized Legendre periods with exact rational tail bounds. `python python/build_holomorphic_basis.py` rebuilds both atlas links, bases and interval receipts. See docs/HOLOMORPHIC_BASIS_MONOGRAPH.md for valuations, conventions and the formalization boundary.

### Recovered multiplicative constraints

Rows of `A` encode `product(x[j]**A[i][j]) = rhs[i]`. `monomial.solve_rational_monomial` returns a complete positive-rational multiplicative fibre or a prime-exponent obstruction. `solve_monomial` returns every positive-integer solution when a checked positive row combination bounds the variables; budget failure raises without a partial list. `eliminate_exponents` returns all cancelling row combinations, and distinguishes consequences from complete integer projection.

```sh
PYTHONPATH=python python -m perfectpower monomial-recovery
PYTHONPATH=python python -m perfectpower monomial-solve --matrix '[[2,3]]' --rhs '[557256278016]'
PYTHONPATH=python python -m perfectpower monomial-rational --matrix '[[2,-3],[1,1]]' --rhs '["4/27",6]'
PYTHONPATH=python python -m perfectpower monomial-project source.smt2 --output projected.smt2
python python/recover_monomial.py --z3
```

These are exact Python calculations, with stated positive domains; new Lean proofs are not claimed. See [the monograph](../docs/MONOMIAL_RECOVERY_MONOGRAPH.md).

The optional analytic backend uses `pip install -r python/requirements-analytic.txt`. `intrinsic-voronoi` computes period-derived torus cells; `analytic-periods` integrates closed lifted cycles with continued logarithms; `conformal-metric` evaluates the original component's differential metric; `conformal-voronoi` constructs a closed hyperelliptic cover mesh and intrinsic heat-distance cells. Run `PYTHONPATH=python python python/build_analytic_geometry.py` to rebuild the examples. See docs/ANALYTIC_GEOMETRY_MONOGRAPH.md for accuracy levels and supported domains.

`certified-voronoi` produces conservative boundary enclosures using rational Lipschitz lower bounds and explicit-path upper bounds. `surface-homology` produces tree/cotree dual cycles and replayable integral symplectic reduction. See `docs/CERTIFIED_SURFACE_GEOMETRY.md` for the exact scope; no smooth-curve or analytic period certification is asserted.

`symplectic-periods --coeff=0,-1,0,0,0,1 --resolution 6` connects the mesh homology basis to actual numerical analytic integration. `integrate-path --coeff=-1,0,0,1 --d 3 --points '[[0.3,0.7],[0.6,0.8]]'` supports a continued open path on a cubic cyclic component. `surface_periods.bergman_metric` and `surface_periods.jacobian_coordinates` use the computed A-normalization. See `docs/SYMPLECTIC_ANALYTIC_MONOGRAPH.md` for the exact scope and generated six-curve corpus.
### Algebraic curve execution and differential extensions

`DifferentialExtension` in `perfectpower.differential_extensions` compiles squarefree finite étale algebras over one through three rational parameters. It exposes exact algebraic derivatives, trace/norm/minimal polynomials, fixed-algebra multiplication and cyclic scalar Hilbert–90. `tensor_primitive` retains a complete tensor product and returns generator-recovery identities. A nonunit has a factor witness; irreducibility is not assumed.

`CurveFamily` now exposes `algebraic_local_chart`, `algebraic_degenerations`, `resonant_frobenius`, `node_branches`, `ramified_scaling_chart` and `cyclic_projector_obstruction`. Algebraic parameters use `{"modulus": [...], "element": [...]}`; the element is optional and defaults to the algebra generator. Coefficients are constant-first. Formal local precision, ramification and algebra budgets are explicit.

`SymmetryCurve` in `perfectpower.symmetry_quotients` verifies supplied finite Möbius actions on degree-3-through-8 hyperelliptic polynomials. Its `quotient`, `projectors`, `observable` and `involution_decomposition` operations return actual quotient equations, independent differential systems and, for complementary double covers, specific Jacobian isogeny certificates. The latter supplies the degree and kernel annihilator, not explicit torsion generators or integral markings.

```sh
PYTHONPATH=python python python/develop_algebraic_curve_extensions.py
PYTHONPATH=python python -m perfectpower service \
  --database /tmp/pp-algebraic.sqlite \
  < receipts/algebraic_curve_extensions/service_requests.jsonl
```

The catalogue kinds are `differential_extension` and `symmetry_curve`; the service also exposes standalone `tensor_primitive`. See the [complete mathematical derivations](../docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.md), [receipt workbench](../docs/algebraic_curve_workbench.html), and [handoff guide](../CLAUDE_CODE_ALGEBRAIC_CURVES_START_HERE.md).

### Literature-driven curve research

Three new catalogue kinds are `differential_module`, `superelliptic_family` and `binomial_sum`. They provide exact tensor representations, bounded horizontal section/endomorphism searches, matrix descent, coprime superelliptic reduction with retained primitives, rational constant-term compilation and certified named telescopers. See [the complete mathematical/API map](../docs/LITERATURE_CURVE_EXECUTION_MONOGRAPH.md).

The JSONL service also exposes `genus_three_tower`, `richelot`, `formal_two_isogeny`, `branch_braid`, `reflection_kernel`, `root_clusters`, `simultaneous_nodes`, `certified_transport`, `marked_legendre`, `frobenius`, `zeta`, `frobenius_deformation`, `tower_frobenius` and `sunrise`. Each operation accepts keyword arguments through the existing `args` field and returns a scope-bearing receipt. For example `{"op":"formal_two_isogeny","args":{"a":1,"b":2}}` reconstructs and verifies the full rational map, and `{"op":"frobenius","args":{"coefficients":[1,1,0,1],"p":5,"precision":2}}` returns an actual cohomological Frobenius matrix modulo 25. `{"op":"sunrise"}` derives the exact relative integral certificate.

Rebuild all twenty-two example receipts with `PYTHONPATH=python python python/literature_curve_corpus.py`. Run the focused suite with `PYTHONPATH=python python -m unittest discover -s python/tests -p test_literature_curve_execution.py`. All core algorithms use the standard library; PDF rendering uses optional ReportLab and Matplotlib.

### Recovered divisor kernels

`divisor_kernel` supplies exact divisor and multiple transforms, their Möbius inverses, matrix-free raw/normalized GCD kernels, complete raw rational/integer affine fibres, sparse divisor feature pairings and the integral tridiagonal inverse `threshold_solve`. Exact inputs accept integers and `Fraction`; numerical mode is explicit. Positivity is checked through the appropriate factorization, with inconclusive signed normalized cases reported honestly.

```sh
PYTHONPATH=python python -m perfectpower divisor-kernel --family sigma --N 4 --vector '[1,0,1,0]'
PYTHONPATH=python python -m perfectpower divisor-kernel --weights '[1,3,4,7]' --rhs '[1,2,3,4]' --domain integer
PYTHONPATH=python python -m perfectpower divisor-kernel --N 12 --degree 0 --normalized --vector '[1,0,0,0,0,0,0,0,0,0,0,0]'
python python/recover_divisor_kernel.py --benchmark
```

The runner replays all 8,358 stored power-hit records and the million-coordinate sigma identity, then constructs their seven-set arithmetic Gram matrix. See [the recovery monograph](../docs/DIVISOR_KERNEL_RECOVERY_MONOGRAPH.md) for proofs, historical corrections and scope. These calculations add no Lean compilation claim.

## Binary invariant contractions and Mordell cover reduction

`perfectpower.binary_invariants` represents homogeneous binary forms with an explicit degree and supplies normalized epsilon contractions, a typed contraction compiler, quartic invariants and covariants, and cubic discriminants. `perfectpower.quartic_cover_reduction` selects strictly smaller integral covering models while retaining their rational charts to the original Mordell curve. Its primitive projective residue masks include infinity, and its native bounded enumeration retains both nonzero ordinate signs. Run `make check-quartic-invariants`; run `python python/develop_quartic_invariants.py --models-only` for the atlas without PARI. See [the monograph](../docs/BINARY_INVARIANTS_MONOGRAPH.md) for the exact scope and the two new frontier witnesses.

`perfectpower.mordell_three_isogeny` supplies the exact degree-three Mordell isogeny, normalized dual, point transport and a direct composed-cover polynomial map. Run `make check-mordell-three-isogeny`. The two-phase partner-search runner retains source cover coordinates before attaching images and independence evidence to the original descent packets. See [the continuation monograph](../docs/MORDELL_ISOGENY_WITNESSES_MONOGRAPH.md).

`perfectpower.mordell_published_witnesses` reads a checksum-pinned Sage numeric dataset through a restricted two-constructor decoder, checks its candidate coordinates exactly and attaches independently verified original-curve rank lower certificates. Run `make check-mordell-published-witnesses`. Reproduce the final five closures with `PYTHONPATH=python python python/develop_mordell_published_witnesses.py --source /path/to/mwMordell10000.sobj`. The retained JSON receipt allows checks without Sage, PARI, network access or the full source dataset. See [the zero-gap monograph](../docs/MORDELL_WITNESS_CLOSURE_MONOGRAPH.md).

The [Mordell completion monograph](../docs/MORDELL_COMPLETION_MONOGRAPH.md) describes all 457 full bases and complete integral lists, their independent census cross-check and the remaining Lean trust boundary.

## Checked nonlinear global and Pell populations

`checked-nonlinear-population` certifies all integer solutions of `y²=U(x)³−2` or `y²=U(x)³−4`, for nonconstant U with ascending integer coefficients. Its finite input intervals come from a proved polynomial fibre bound. For example:

```sh
python -m perfectpower checked-nonlinear-population --coeff '[2,0,1]' --queries '[{"objective":["pow","y",2],"ranks":[0,1,4]}]' --check
python -m perfectpower checked-nonlinear-population --family mordell_minus4 --coeff '[1,0,1]' --domain positive --queries '[{"condition":["le",0,"y"],"objective":"x"}]' --check
python -m perfectpower checked-pell-population --cutoff 1000 --global-ranks '[0,4,8]' --queries '[{"condition":["mod","x",0,2],"objective":"y","ranks":[0,4,5]}]' --check
```

The Pell command covers all nonnegative solutions of `y²=2x²+1` up to the declared input cutoff, including `(0,1)`. Global selections follow the proved increasing recurrence; cutoff minima and local ranks refer to the cutoff population. The Python functions are `nonlinear_population_certificate`/`check_nonlinear_population` and `pell_population_certificate`/`check_pell_population` in their corresponding `checked_*_population` modules. Isolated HTTP operations use `checked_nonlinear_population` and `checked_pell_population`, with keyword arguments under `args`. Kernel checks require Lean 4.20.0 and pinned Mathlib on `LEAN_PATH`. Emission alone does not accept a proposal. See [the mathematical and API monograph](../docs/EXTENDED_POPULATION_MONOGRAPH.md) for scopes and resource limits.

## Broad global families and general Pell access

```sh
python -m perfectpower checked-family-population --coeff '[0,0,1]' --offset 15 --queries '[{"ranks":[0,1,10],"objective":["pow","y",2]}]' --check
python -m perfectpower checked-family-population --family mordell_minus13 --coeff '[16,0,1]' --queries '[{}]' --check
python -m perfectpower checked-family-population --family mordell_descent --offset -9985 --coeff '[5,0,1]' --queries '[{}]' --check
python -m perfectpower checked-pell-family --D 3 --cutoff 100 --domain integer --queries '[{"objective":"y","ranks":[0,1,100]}]' --check
python -m perfectpower checked-pell-family --D 2 --cutoff 1000000000000000000000000000000 --global-ranks '[1000]' --global-objective '["add","x","y"]' --check
python -m perfectpower checked-pell-family --D 7 --cutoff 100 --global-objective '["mul",-1,"x"]' --check
```

The finite family interface covers `y²=U(x)²+k` for nonzero k, five classical Mordell sources and the offsets in `data/mordell_descent_sources.json`. Integer fibres use exact divisibility, zero stripping and direct linear recovery. The Pell interface proves its seed fundamental, supports all signs, uses binary powering for global ranks and can return an exact cutoff count without constructing a point list. Its global objectives cover nonnegative polynomial expressions and the unbounded-below expression `-x`. Fundamental-seed certificates and point sizes remain budgeted. See [the family engine monograph](../docs/FAMILY_ENGINE_MONOGRAPH.md) for the exact domains, refusal cases and remaining research.

## Automatic reductions and generalized Pell orbits

`checked-auto-population` recognizes supported original square equations from ascending integer polynomial coefficients. Finite square/cubic pullbacks are globally complete; Pell-type quadratics require an absolute input cutoff. `checked-pell-orbits` handles `y²-D*x²=norm` with all checked terminal seeds, signed finite queries and per-orbit global selections. `--check` privately rebuilds the proof sources. Unsupported reductions and work-budget exhaustion are explicit errors.

```sh
python -m perfectpower checked-auto-population --coefficients '[1,1,2]' --cutoff 1000000000000 --check
python -m perfectpower checked-pell-orbits --D 2 --norm 7 --cutoff 100 --global-ranks '[{"orbit":1,"rank":1000}]' --check
```

See [the orbit reduction monograph](../docs/ORBIT_REDUCTION_MONOGRAPH.md) for the finite seed bounds, coordinate inversion and the distinct saturation-at-2 census result.

## Structural mathematics APIs

`perfectpower.species` supplies exact exponent invariants and bounded species count/select/rank. `ExactPopulation({'kind':'species','bound':1000})` integrates them with population sampling and catalogue persistence. `perfectpower.inequality_certificates` supplies rational PSD, Gram, constrained polynomial bounds, quadratic minima, real Toeplitz positivity and linear stability certificates. `perfectpower.descent_squareclasses` supplies supported squareclass covers, finite local exclusions, rational point transport and two-isogeny rank bounds. See [the structural mathematics monograph](../docs/STRUCTURAL_MATH_MONOGRAPH.md) for runnable examples, evidence and precise limits; reproduce with `make structural-math`.
