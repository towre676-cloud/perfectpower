# Open-front checkpoint

This checkpoint tracks completed results and remaining directions on the working branch. The k=22 closure below is already in the complete registry. Lean 4.20.0 is installed locally and the new foundational modules are checked sequentially; the full repository build and global axiom report are separate checks.

`NativeCubic` proves associativity, commutativity and the identity for the integral normalized binary-cubic multiplication table. This is the start of native order arithmetic. The determinant norm and an exact integral basis bridge for shifted negative-monic forms are now proved in `NativeCubicNorm` and `NativeCubicBridge`. A maximal-order certificate and basis-independent nonmonic rank-one reduction are still needed. A binary cubic is an index form in this construction; its values must not silently be identified with unit norms.

`WeightedSkolem` proves the finite-zero theorem for `(A^N Γ)₂₀`, with arbitrary representative matrix Γ. Its hypotheses require a certified period and a first-order test in every residue class. The inverse orbit can be checked separately. `WeightedNormList.complete_of_cert` now assembles signed-exponent completeness from the checked norm slab and two directional weighted bounds. `WeightedNorm107` supplies a complete nonempty example: u³+4v³=107 exactly at (-1,3). Recentring at later roots and auxiliary-prime exclusion remain work.

`OrbitLattice` proves the exact image test `w₂=0` and `a | w₀+h w₁`, and entrywise periodic congruences for weighted orbits. `python/orbit_lattice.py` searches full matrix periods, failing when its search limit is reached. Its rank-two version begins the negative-k route: the class for −63 with encoding `(4u−17v,−4v,4v)` admits 64 of 128 residue pairs modulo 8. This only removes residue classes; it is not an exponent bound. `receipts/open_fronts.json` records the eight named Matveev premise families found in the two generated analytic modules. None has been discharged here.

k=22 is now closed: all 100 integer-endpoint slab modules, the assembled source theorem, the class-list proof and the complete curve theorem passed Lean. The only integral points of y²=x³+22 are (3,−7) and (3,7), with no analytic premise. The source checks cover 971,659 original slab candidates; 99 chunks were checked afresh in 67.3 minutes and the committed first chunk was reused through its matching proof-input hash. The class-list box has 82 forms. The finite compiler's emitted whole-query equivalence also passed. The complete registry now has 73 positive curves. Generation preserves matching check identities, and the heavy-build script prevents concurrent slab reductions. k=94, with 5,294,219 slab candidates, remains the next larger instance; it has not been proved here. See `K22_PROOF.md` and the retained kernel log and receipts.

`QuarticPilot` proves the complete integral solution list of `v²=3u⁴+3u²+1`: exactly `(0,1)` and `(0,−1)`. Its map is `X=3u²+1`, `Y=3uv` onto `Y²=X³−1`; the zero fibre is retained. Consequently every nonzero integer argument gives a non-square value. This begins explicit non-power counting with a complete example. `nonzero_not_even_power` now excludes every even exponent at nonzero arguments. Odd perfect powers and Bilu–Tichy remain open.

`SparkStep` proves both arithmetic bound transitions and the accept-branch remainder identity used by the square-root pilot. These are integer refinement lemmas, not discharged GNATprove verification conditions. `final_range` bounds a nonnegative integer root of a signed 31-bit input by 46,340. Intermediate word-size overflow, bitwise-or refinement, the original VC correspondence and a GNATprove rerun remain necessary before claiming an end-to-end SPARK win.

`CurveReadout` proves coordinate export and equation transfer with an explicit inverse scale over a commutative ring. `BrainpoolReadout` instantiates these statements in the concrete 384-bit residue ring, including the published generator export. These equation statements do not require primality. A prime certificate is still required for the concrete field/group instantiation, and no implementation timing property is asserted.

`NativePolynomialSquare` now proves an effective integer coefficient bound and an unconditional finite search for y²=P(x)²+k for every nonconstant integer polynomial represented by its ascending coefficients, including nonmonic and arbitrary-degree inputs, with k≠0. `native_polynomial_square` computes the list and emits a kernel-checked completeness theorem without Python, Sage, Singular or a supplied height bound. The audit includes a degree-14 equation. General arbitrary-polynomial power-value automation, general Baker bounds, number-ring solvers and GPU/WASM deployment remain open. Classical Chabauty requires Mordell–Weil rank strictly below genus; genus at least two alone is insufficient. The existing finite-field Fermat result does not solve arbitrary function-field equations.

The recent positive-geometry, differential and monomial backlog now has native Lean modules and an explicit proof map in `receipts/lean_backlog/formalization_status.json`. `LegendreBounds` proves the actual formal power-series equation and a real convergent-series interval theorem, without assuming an analytic period identity. `MonomialConsequences.exponent_image_iff` proves the recovered nine-variable integer exponent system has a solution exactly when 3 divides b3−b2. `QuarticCutoff` proves a substantially smaller effective search with the exact zero-perturbation fibre retained. General graph support rank, arbitrary-column Cauchy–Binet, matroid greedy optimality, analytic normalization/basis completeness and Euler-period identification remain open. See `LEAN_BACKLOG_MONOGRAPH.md`.

The divisor-sum quartic ledger is fully closed at 3,080 complete lists and 3,080 kernel-checked packet equalities. There are no uncompiled catalogue indices. This closes the finite backlog without changing the original equation source or point packets.

`RungePolynomial` now proves strict domination for arbitrary integer Horner polynomials of unequal degree, the zero-residual alternative, an unconditional coordinate bound for nonzero residual, and complete original-curve square-root enumeration from a checked scaled identity. `native_runge` recognizes expanded positive even-degree inputs with positive integer-square leading coefficient through exact rational square-root truncation. The audit closes 16 finite packets through degree 20, two certificate-only searches and two exact-square families, with 79 declarations checked for standard axioms. `native_runge_certificate` proves the bound and full finite-search equivalence without evaluating large intervals. This advances the native rational-branches Runge family; nonsquare leading coefficients, arbitrary exponents, general Runge curves, Baker bounds and number-ring solvers remain open. See `NATIVE_RUNGE_MONOGRAPH.md`.

`RungePower` extends the native completion route to every exponent d ≥ 2, with the proved gap |Q(x)|^(d−1) ≤ |R(x)| for nonzero residual. The dominating polynomial is now Q^(d−1), allowing residual degree below (d−1)deg Q. `NativePowerRoots` proves binary floor-root correctness and complete signed power fibres. `native_runge_power` recognizes nonconstant expanded inputs of degree divisible by d with nonzero integer d-th-power leading coefficient, including negative odd-power leading coefficients. The audit has 20 finite packets through degree 40 and exponent 10, two certificate-only cases, three exact-power families and 124 standard-axiom declarations. Symbolic correctness of the proposal generator, sharper coefficient bounds, other leading coefficients, general Baker bounds and number-ring solvers remain open. See `NATIVE_RUNGE_POWER_MONOGRAPH.md`.

The analytic surface layer now computes numerical symplectic periods by integrating actual continued-sheet dual cycles on squarefree hyperelliptic meshes. The corpus covers six curves in genera 1 through 4, with bilinear, positivity, contour-deformation and canonical-metric basis-invariance checks. Canonical Bergman evaluations and Abel–Jacobi lattice coordinates are implemented. Certified roots/continuation, enclosed quadrature and interval period normalization remain open, as do symplectic mesh integration for cyclic degrees above two and certified smooth arbitrary-genus Voronoi boundaries. Exact rational polyhedral enclosures retain their narrower metric scope. See `SYMPLECTIC_ANALYTIC_MONOGRAPH.md`.

The parallel geometry/deep-gems pushes now have a dedicated Lean bridge. `WeightedHodge`, `DivisorCoordinates`, `SymplecticTransport`, `PolyhedralVoronoi`, `FiniteWeilAlgebra`, `CanonicalMetric`, `PowerSumRecovery`, `PSGRecovery` and `PowerComposition` prove the reusable exact statements. `QuarticPowerRegistry.complete` covers all 3,080 outer curves at every nonzero power coordinate; the 6,160 saved square/cube packets each have a separate kernel-checked lifting equality relative to the previously proved outer literal packets. Concrete weighted Hodge matrices in genera 0,1,2,3,4,7 and the stored integral symplectic bases have exact matrix audits. This does not certify numerical periods, the smooth-curve/mesh identification, the numerical Bergman curvature formula, all finite cyclotomic commutant dimensions, or bounded power-sum uniqueness. See `PARALLEL_LEAN_MONOGRAPH.md` and `scripts/check_parallel_push.sh`.

The enhanced-machinery transport now has `AffinePowerComposition.complete` and `AffineQuarticAtlas.complete`, including both integral divisibility image restrictions. The dedicated audit checks another 6,160 affine literal packets, covering the plain/affine transport outputs of all 12,320 corpus equations. `ResidueCover.quartic_no_square` closes y²=2x⁴+3 globally modulo 16. `IntegerOptimization` proves quadratic completion, its continuous lower bound and exactly both tied minimizers for x+y=1. Formal Smith saturation, LDL/LLL replay and complete ellipsoid enumeration remain open; the newest Python optimizer has not been promoted to a verified kernel.

## Monograph push: new Lean coverage

The follow-up in `docs/MONOGRAPH_LEAN_MONOGRAPH.md` proves exceptional-root finite-search assembly and the complete exceptional quartic, the nonnegative rational-grid sharp gap, direct giant integer-root examples, connection projection algebra, and exact generated-word spans for all 139 rational operator fixtures. The focused check is `scripts/check_monograph_push.sh`. General Sturm transcript correctness, all sharp-gap sign/threshold branches, full graph probabilities, and commutant/bicommutant certification still need proofs.

## Integer-root and graph-event formalization

`ROOT_EVENTS_LEAN_MONOGRAPH.md` documents unconditional Bernstein-certified integer-root trees, local signed Sturm-chain algebra, arbitrary finite mixed-event identities and conditional bounds, and closed inclusion laws for all 64 stored rational-kernel models. The classical real-root variation theorem and the 120 nonsingular nonrational-kernel models remain open. General weighted Cauchy–Binet inclusion laws are also separate from the checked finite instances.

## Unified arithmetic simplifier checkpoint

The initial exact compiler, partial/bounded analysis, supplied polynomial pullbacks,
question scopes and eight Lean composition laws are implemented. See
[the monograph](ARITHMETIC_SIMPLIFIER_MONOGRAPH.md) for APIs, evidence and remaining
compiler/formalization obligations. Automatic rational decomposition discovery, complete
nonlinear finite pullbacks, two-sided power transport, univariate Boolean integer domains
and global discrete polynomial optimization are now implemented in Python. The stored
experiment closes all 6,422 pullbacks, including 141 previous unresolved cases, and
matches 3,080 independently checked global optima. See
[Polynomial capacity](POLYNOMIAL_CAPACITY_MONOGRAPH.md). General Sturm variation,
the generic optimizer theorem, generator pullback, coefficient-bearing infinite monomial
parameterizations and whole-compiler kernel proof emission remain open.

## Gamma arithmetic checkpoint

Fixed-shift/product/binomial normalization, natural-index factorial ratios,
Landau step certificates, valuation/unit obstructions and exact hypergeometric
transport are integrated. The 52 independently sourced Bober families pass the
exact corpus. Lean now closes the whole central-binomial non-power family and
reusable Gamma, recurrence and integral-output transport statements. See
[GAMMA_ARITHMETIC_MONOGRAPH.md](GAMMA_ARITHMETIC_MONOGRAPH.md). General Landau
criterion equivalence, factorial-unit algorithm correctness, controlled complex
Gamma evaluation and infinite Pell Mellin/heat error bounds remain open.
