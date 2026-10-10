# PSG structural algebra in PerfectPower

## The concrete change

This extension turns three mechanisms recovered from Programmable Stability Geometry into standard-library arithmetic interfaces: quadratic source elimination with complete auxiliary reconstruction, polynomial differential invariants with exact cofactor witnesses, and observable parameter fibres with explicit ambiguity. It also adds exact finite formal jets, bounded differential-model coefficient spaces, and polynomial ideal witnesses for redundant constraints. The original PSG source is reproduced from its saved 26-term expression, reduced to the same 100-term polynomial already present in PerfectPower, and connected to the repository's existing generalized Pell populations. These are executable exact rational calculations. The new Lean files contain proof sources and an audit entry point; their compilation status is recorded separately rather than inferred from Python acceptance.

The purpose is to make an elimination useful to the person who needs an original answer. A resultant alone is often only a necessary condition. It can forget the sign of a square root, hide a singular denominator, or introduce integer candidates that have no integer preimage. Here the reduction retains the original polynomial, a normal form, multipliers witnessing the eliminated constraint, and a complete reconstruction rule over every supplied exact base point. Likewise, a numerical residual alone says little about what additional information would settle a parameter. Here the observation calculation supplies the whole rational affine fibre and concrete pairs of points that agree on the observations but disagree on the requested target.

## Quadratic elimination as an explicit norm

Let R be a commutative coefficient ring, let t be an auxiliary variable, and let D be a polynomial in the remaining variables. D must be independent of t. Division by the monic polynomial t²−D gives an exact decomposition

\[P=A+tB+(t^2-D)C.\]

The code constructs this without multivariate Gröbner discovery. Every monomial t^(2k) reduces to D^k, and every monomial t^(2k+1) reduces to tD^k. The quotient follows from the finite geometric identity

\[t^{2k}-D^k=(t^2-D)\sum_{j=0}^{k-1}t^{2(k-1-j)}D^j.\]

Consequently A and B contain no t. The reduced quadratic norm is N=A²−DB². The producer also emits the exact ideal witness

\[N=(A-tB)P+\bigl(B^2-(A-tB)C\bigr)(t^2-D).\]

This identity proves that P=0 and t²=D imply N=0. Its replay checks every polynomial coefficient, both source identities, the declared variable order, and the original source supplied by the caller. Replacing the saved source while leaving its certificate intact is rejected. Replay does not rerun the reduction algorithm or trust the packet's description of success.

The norm identity is also the elementary algebra behind quadratic field norms and Pell equations. It gives a common interface for expressions involving an auxiliary square root, repeated square-coordinate substitutions, and arithmetic in a quadratic extension. It should not be confused with a generic arbitrary-degree number-ring solver. This implementation reduces one specified monic quadratic relation; the coefficient and operation budgets deliberately stop computations that exceed their declared scope.

## Complete reconstruction and the singular branch

After specializing the remaining variables to exact rational values, A, B and D are numbers. If N is nonzero, the auxiliary fibre is empty. If N=0 and B is nonzero, the only possible auxiliary value is t=−A/B. Substitution proves t²=D and P=0. In the rational domain this is the complete fibre. In the integer domain it is accepted only when its denominator is one. This is an image restriction, not a numerical approximation or a rounding decision.

If B=0, the equation must be handled separately. When A is nonzero there is no solution. When A=0, the source imposes no additional restriction on t beyond t²=D. The fibre is therefore the exact rational or integer square-root fibre of D. Negative D gives no such roots. A nonsquare nonnegative rational gives no rational roots. D=0 gives one root, and a positive square gives the two signed roots. This branch is essential: division by B would lose it, while accepting all norm-zero points would introduce incorrect rational or integer conclusions.

Reconstruction is complete over a supplied exact base point. It does not establish a global classification of all base points satisfying the norm polynomial. Those base points still need a suitable arithmetic family, a complete bounded domain, or a separate theorem. The API makes that division of work explicit.

## Recovering the actual PSG source

The recovered script supplies P(x,L,T) and the chamber equation T²=Y²−1. Exact reduction reproduces a norm polynomial with 100 surviving terms. All powers of x and Y are even, so the polynomial factors through U=x² and Z=Y². `power_coordinates` checks divisibility of every exponent before it creates the compressed polynomial. An unmapped variable with nonzero exponent, or a power not divisible by the proposed coordinate exponent, causes rejection.

The resulting Q(U,L,Z) is coefficient-for-coefficient equal to `recovery_sources/deep_gems/PSG_Q_U_L_Z.txt`. This closes a missing executable link upstream of the existing `PSGRecovery.deweighting` statement. The saved polynomial was not merely copied into the new implementation: it was independently reconstructed from the earlier source expression and quadratic chamber relation. The receipt retains hashes identifying the source scripts and records the exact comparison.

This recovery establishes algebraic identities. It does not substitute arbitrary rational L and Z for the analytic relation Z=e^(2L) and claim a physical conclusion. Nor does it prove transcendence of a distinguished analytic constant. Algebraic chamber coordinates are useful because they make the polynomial mechanism available to the rest of PerfectPower; their analytic interpretation remains a separate requirement.

## Affine norm transport into existing Pell populations

Suppose A(x,y) and B(x,y) are integer affine forms with a nonsingular two-by-two linear part. The new `affine_norm_population` solves

\[A(x,y)^2-D B(x,y)^2=m\]

by passing the canonical equation X²−DY²=m to the repository's existing generalized Pell orbit producer. The original coordinates are recovered by the exact rational inverse of the affine map. Only preimages with integral coordinates are retained. A unimodular matrix has no lattice loss; a nonsingular nonunimodular matrix imposes genuine congruence restrictions. Those restrictions are retained by the inverse-coordinate test.

The finite cutoff is |B(x,y)|≤H. It is not a box in the original x,y coordinates. This distinction matters because an affine inverse can move or stretch a coordinate substantially. The returned scope identifies the cutoff coordinate, contains every accepted original point, and retains the canonical Pell packet. Singular affine maps are rejected because the inverse-coordinate route does not apply to them. The work budget of the existing Pell producer remains in force.

The development corpus compares 90 affine norm equations against independent enumeration of the original equations. The corpus uses six nonsquare D values, five signed norm levels, and three coordinate scales. It compares 338 original points and explicitly records points rejected because the affine preimage is nonintegral. This is an integration test of the original-coordinate result, not merely a check of the canonical norm equation.

## Differential invariants with cofactor witnesses

For a polynomial vector field X=(F₁,…,Fₙ), the polynomial Lie derivative is

\[X(H)=\sum_i F_i\,\partial_i H.\]

A nonconstant polynomial H is a Darboux polynomial when X(H)=KH for a polynomial K. Along any differentiable trajectory of the vector field, H evolves by the scalar linear equation dH/ds=K H. In particular, its zero hypersurface is preserved wherever the trajectory and coefficients are defined. This interpretation depends on the ordinary differential-equation hypotheses; the arithmetic receipt itself is the polynomial identity.

The producer divides X(H) by H and emits K and a reduced remainder. Independent replay binds H and every component of X, recomputes the polynomial derivative, verifies the identity, and checks the remainder condition. A zero remainder certifies the supplied invariant. A nonzero reduced remainder rejects that supplied candidate. It does not classify every possible invariant.

All six supplied PSG factors pass this identity test: v, a, 2a−1, v+4−8a, av−2a−2pv+1, and 2av+4a−4pv−v−2. Their exact cofactors are saved. Products inherit the sum of the cofactors, so accepted primitive factors generate further accepted invariant products. The optional linear scan exhausts an explicitly bounded integer coefficient box up to nonzero rational scale. Its finite coverage is stated independently of the six recovered factors; no all-height or all-degree Darboux classification is advertised.

## Redundant constraints as polynomial identities

An equation added to a solver can be a consequence of existing equations rather than new information. The ideal-witness interface represents a target polynomial G as Σ AᵢFᵢ plus a remainder. A zero remainder gives a concrete certificate that G vanishes whenever all supplied Fᵢ vanish. Replay checks the complete sum against the caller's original target and generators.

The implementation uses ordered multivariate division, not a Gröbner-basis completion algorithm. Therefore a nonzero remainder is inconclusive about ideal membership. The tests retain an example where division leaves a nonzero remainder even though a simple difference of the generators equals the target. This prevents an unsuccessful discovery strategy from being presented as a mathematical obstruction. The useful result is the positive identity; a general ideal-membership decision procedure is outside this extension.

## Exact parameter dependence and nonvanishing witnesses

For a rational polynomial output p and an input parameter v, independence is decided algebraically. The polynomial difference p(v+1)−p(v) is identically zero exactly when p is independent of v in characteristic zero. When that difference is nonzero, the code constructs an actual point where it does not vanish. At each variable it tries degree-plus-one integer values, selecting one whose specialization remains a nonzero polynomial. A nonzero univariate polynomial cannot vanish at all those distinct values, so the procedure progresses to a nonzero rational value.

The resulting pair of input points differs in only the nominated parameter and has different output values. This is an explicit dependence witness rather than a correlation, a finite grid guess, or a nonzero derivative evaluated at an arbitrary point. It can reveal which coefficients affect a particular output and which parameters a solver can safely omit from that task. Dependence means an input can change the output somewhere; it does not mean that the effect is nonzero at every point.

## Observable fibres and the minimum missing measurements

For rational observations Az=b and a rational target Cz, the complete solution fibre is z=z₀+ker A when the observation system is consistent. The interface returns a seed z₀ and a basis of ker A. If it is inconsistent, it returns a left annihilator w with wA=0 and wb≠0. If every kernel direction is killed by C, the target is determined and the code constructs a readout L with C=LA. Otherwise it returns two points in the same observation fibre whose targets differ.

There is also a concrete experimental-design statement. The minimum number of additional arbitrary rational linear scalar measurements needed to determine the target is rank(C restricted to ker A). The code selects that many independent target rows on the kernel and returns them as sufficient observations. Fewer scalar measurements cannot kill a target variation space of that dimension. This result concerns unrestricted rational linear measurements. Costs, permitted measurement families, integer states, and nonlinear observation design need their own treatment.

## Finite jets, resonances and differential model spaces

Finite formal composition is exact when the inner germ has zero constant and the requested coefficients are known. The composer rejects insufficient source depth. Curvature jets I=F''/F' require two additional known orders of F and a nonzero F'(0). Missing coefficients are never filled with zero to assert higher resolution. The Schröder interface returns finite coefficient residuals for Ψ(F)=λΨ; it does not infer the existence of an infinite convergent conjugacy.

The saved triangular example composes Ψ(u)=u+b₃u³+b₅u⁵+b₇u⁷ with u(h)=h/2+h²/3 through order seven. Its dependency profile proves that b₇ cannot change coefficients through order six and enters coefficient seven with multiplier 1/128. This is a worked exact finite model of the separation used in PSG. It does not identify this chosen u with every analytic normalization in the older papers, or assert that one condition fixes all higher resonant coefficients.

The differential-model interface enumerates every monomial within a declared degree bound in h,F,F',…,F^(r), substitutes the known finite jets, and computes the complete rational coefficient kernel. A full-column-rank matrix excludes every nonzero relation in that bounded ansatz at that depth. A nonzero kernel supplies all finite-order compatible coefficient vectors. Compatibility at a finite depth is not an analytic identity, and excluding a bounded ansatz is not a proof of transcendence. The retained examples distinguish an exponential jet with its first-order relation, an excluded linear ansatz, and a rational-function jet compatible with a quadratic ansatz.

## Reproduction and proof status

Run `make psg-structural` for the focused regression tests and deterministic receipts. The public console exposes `psg-reduce`, `psg-darboux`, `psg-dependencies`, `psg-ideal`, `psg-fibre`, `psg-model-space`, and `psg-norm`. Expressions accept arithmetic syntax only, with exact integer or rational coefficients; calls, attribute access, floating literals and variable denominators are rejected. The operation budgets bound expression size, monomial counts, degree, coefficient size, multiplication work and division steps.

`make psg-structural-kernel` is the separate Lean compilation and axiom-audit route. The generic module supplies quadratic norm and elimination identities, reconstruction algebra, cofactor multiplication and affine norm expansion. The generated module supplies literal source-reduction, recovered-norm and six cofactor identities. The twenty declarations now compile against Lean 4.20.0 and pass their standard-axiom audit; the source-bound record is `receipts/new_work_lean/verification.json`. The Python polynomial interpreter, differentiation implementation, packet decoder, fibre assembly, rank computation and whole-console execution remain tested executable code rather than formally refined implementations.

The kernel target requires twenty distinct compiled declarations and permits only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; unexpected audit output fails the target. Both the exact receipt reproduction and the separate kernel target are registered in CI. In this workspace, twelve focused tests and twenty-two existing regression tests passed, while the original run skipped one existing Lean-dependent test. The subsequent 0.9.1 closure compiles and audits the recovered proof sources. An isolated wheel installation also passed all seven new console routes and the existing checks of 1,098 packaged runtime assets. `receipts/psg_structural/verification.json` records the local proof status separately from deterministic mathematical receipts.

For example, the following commands recover the unique original auxiliary root, expose a missing measurement, and enumerate an affine norm population with its original integer coordinates:

```sh
python -m perfectpower psg-reduce --variables x,t --source 't-x' --variable t --radicand 'x^2' --base-values '{"x":3}'
python -m perfectpower psg-fibre --observation '[[1,1]]' --values '[2]' --target '[[1,0]]'
python -m perfectpower psg-norm --variables x,y --A '2*x+1' --B y --D 2 --norm -1 --cutoff 30
```

The first returns the root 3. The second gives two states with the same observed sum but different first coordinates and proves that one additional scalar measurement suffices. The third retains only integral preimages of the Pell points under the nonunimodular map, rather than returning canonical points that the original variables cannot realize.

The resulting capability is a connected arithmetic workflow: keep the source equation, eliminate one hidden quadratic coordinate, recover every auxiliary answer with its image restrictions, recognize supplied invariant polynomial surfaces, identify redundant equations, and expose exactly what a finite observation does or does not determine. Each stage returns information that the next stage can use without confusing bounded evidence with a global theorem.
