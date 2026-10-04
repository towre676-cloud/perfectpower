# Native Runge bounds and complete integer points for higher perfect powers

The native square-value engine now extends to every integer exponent (d\ge2). Given a closed ascending list for a nonconstant integer polynomial whose degree is divisible by (d) and whose leading coefficient is a nonzero integer (d)-th power, the new recognizer constructs a rational polynomial root at infinity, clears its denominators, proves a coefficient-derived coordinate bound, and emits a complete integer-point packet. Negative leading coefficients are accepted when they are odd powers. Exact powers receive a complete parameterized relation, and large bounds receive an unevaluated but proved-complete finite search. This route invokes neither Sage, Singular, Python arithmetic nor an external height theorem.

The central extension is mathematical. It proves the integer power-gap inequality for arbitrary exponents, uses the polynomial (Q^{d-1}) to dominate the residual, and supplies a fully proved binary integer-root algorithm. The command layer computes proposed coefficients and point packets; Lean independently checks their identities and correctness. Its native computation is not an additional axiom.

## Direct use

```lean
import PerfectPower.Tactic.RungePower

native_runge_power cubic for [1,1,0,1], 3
#check cubic_complete
#print cubic
#print axioms cubic_complete
```

This proves that (y^3=x^3+x+1) has exactly `(-1,-1)` and `(0,1)`. The theorem quantifies over all integer (x,y). The emitted `cubic_decomposition`, `cubic_dominating_power` and `cubic_bound` show the polynomial identities and unconditional coordinate bound. No user-supplied search radius appears in the command.

For fourth powers, `native_runge_power fourth for [1,1,0,0,0,0,0,0,1], 4` proves that (y^4=x^8+x+1) has exactly `(-1,-1), (-1,1), (0,-1), (0,1)`. For negative odd-power leading coefficients, `native_runge_power negative for [1,1,0,0,0,0,-1], 3` proves that (y^3=-x^6+x+1) has exactly `(-1,-1), (0,1), (1,1)`.

The native shell entry point is `scripts/solve_native_runge_power.sh '1,1,0,1' 3`. It builds the focused Lean target, checks the emitted source, prints the completeness theorem and axiom dependencies, and displays the finite packet when present. Add `--source-only` to obtain a standalone Lean program, or `--certificate-only` to prove a large finite search without evaluating its packet. Coefficients and exponent are validated decimal integers and naturals; user input is not evaluated as shell code. The previous square command and its entry point remain available.

## The integer power gap

`RungePower.nonneg_gap` proves, for nonnegative integers (u,v), (u+1\le v), and (d\ge1),

\[
 v^{d-1}\le v^d-u^d.
\]

The induction uses the exact identity

\[
 v^{d+1}-u^{d+1}=v(v^d-u^d)+(v-u)u^d.
\]

The second summand is nonnegative. Multiplying the inductive lower bound by (v) gives the next power. This proves the gap for symbolic exponents, without enumerating exponent cases or appealing to an asymptotic estimate.

`RungePower.power_gap` extends the result to every pair of signed integers. If (y^d=p^d+k), (k\ne0), and (d\ge2), it proves

\[
 |p|^{d-1}\le |k|.
\]

When the magnitudes of the bases differ, the nonnegative gap applies to the smaller and larger magnitude, and the reverse triangle inequality compares their power gap to (|k|). When their magnitudes agree, equal bases would force (k=0); opposite bases do the same for an even exponent. The remaining odd-exponent case gives (|k|=2|p|^d), which controls (|p|^{d-1}). The zero base is handled separately. The theorem therefore covers negative coordinates, negative odd-power values and both signs for even exponents.

The power (d-1) matters. Reusing only the square bound (|p|\le|k|) would require the residual polynomial to have degree below (Q). The stronger gap admits residual degree below ((d-1)\deg Q), which is exactly the degree threshold obtained from general polynomial root truncation.

## Root truncation and denominator clearing

Let (\deg F=dn), with nonzero leading coefficient (c^d) for an integer (c). Reconstruct

\[
 U(x)=cx^n+u_{n-1}x^{n-1}+\cdots+u_0\in\mathbb Q[x]
\]

so that (U^d) agrees with (F) in degrees (dn,dn-1,\ldots,(d-1)n). Descending through its coefficients, the new coefficient (u_k) enters degree ((d-1)n+k) with nonzero multiplier (dc^{d-1}). Exact rational division therefore determines it from previously fixed coefficients. The native algorithm evaluates coefficient convolutions using Lean rational arithmetic.

Let (a) be the least common multiple of the coefficient denominators, set (Q=aU), and define the integer polynomials

\[
 R=a^dF-Q^d,\qquad P=Q^{d-1}.
\]

Their identities and the strict degree inequality (\deg R<\deg P) are checked independently. The command emits a universally quantified identity for (a^dF=Q^d+R), another for (P=Q^{d-1}), and kernel checks of the normalized coefficient-list validity and length comparison. A faulty convolution or division cannot establish a false identity.

For (F=x^3+x^2) and (d=3), the completion is (a=3), (Q=3x+1), (R=-9x-1), and (P=9x^2+6x+1). Thus (27F=Q^3+R). The general bound is 27, and the native command checks that the original curve has exactly `(-1,0)` and `(0,0)`. It does not include points merely because the scaled equation has an integer root. The original power equation is tested in every fibre.

The proposal generator has not itself been proved symbolically successful for every input in this class. Every accepted closed input nevertheless has the required identities, validity conditions, bound and complete-answer theorem checked in Lean. Formalizing the coefficient generator's universal specification is a further refinement, rather than an assumption used in these answers.

## An unconditional coordinate bound

Let (H) denote the sum of the absolute values of the integer coefficients and put

\[
 B=H(P)+H(R)+1.
\]

The previous `RungePolynomial.degree_domination` theorem proves that, whenever (\deg R<\deg P), the inequality (|x|\ge B) implies (|R(x)|+1\le|P(x)|). For an original solution (y^d=F(x)), the checked scaling identity gives ((ay)^d=Q(x)^d+R(x)). If the residual is nonzero, the power-gap theorem gives (|Q(x)|^{d-1}\le|R(x)|), while the second identity gives (|P(x)|=|Q(x)|^{d-1}). The two inequalities contradict one another beyond the bound.

If (R(x)=0) and (R) is a valid nonzero polynomial, apply the same degree-domination theorem to (R) and the zero polynomial. Its roots also lie inside this bound. Therefore `RungePower.coordinate_bound` proves (|x|\le B) for every original integer solution, including the zero-residual fibre. `RungePower.complete` then proves equivalence with the finite union of original power-root fibres over this interval and the exact integer roots of (R). Retaining the root branch explicitly preserves the structure for sharper future coordinate bounds.

## Verified integer root extraction

`NativePowerRoots.search` halves the integer interval between endpoints `lo` and `hi`, selecting the side according to whether the midpoint's (d)-th power is at most the nonnegative target. Its explicit fuel decreases on every recursion. `search_bounds` proves the invariant using the endpoint inequalities (lo^d\le N<hi^d) and a width bound. Instantiating the endpoints at zero and (N+1) gives a floor root for every nonzero exponent:

\[
 r^d\le N<(r+1)^d.
\]

`root_exact` proves that a genuine nonnegative (d)-th root equals this result. `roots_complete` transfers the statement to integer values using natural absolute values, proposes both signs, and filters on the original equation. Odd exponents consequently keep the appropriate single sign; even exponents keep both signs for a nonzero power and reject negative targets; zero occurs once. The algorithm does not enumerate integers up to (N), even when the target is a large polynomial value.

The audit verifies the seventh root of (10^{84}) as (10^{12}), as well as the floor root of the immediately preceding integer. It also checks negative odd-power values, negative even-power rejection, zero and the nonzero exponent-one root specification. Exponent one is valid for the root utility but excluded from the Runge solver.

## Exact powers, large searches and remaining scope

When (R=0), the command produces the exact relation

\[
 y^d=F(x)\quad\Longleftrightarrow\quad ay=Q(x)\ \lor\ \bigl(ay=-Q(x)\ \land\ d\text{ is even}\bigr).
\]

This follows from the general equality criterion for integer powers and cancellation of the nonzero scale (a^d). It retains any integer divisibility imposed by scaling. The audit checks a cube, a fourth power and an exact fifth power with negative leading coefficient; no finite packet or finite coordinate bound is asserted for these branches.

The enumeration command rejects a nonzero-residual interval larger than 10,001 coordinates before emitting generated declarations. `native_runge_power_certificate` proves the identities, bound and equivalence with `RungePower.points` without reducing the packet. For a constant term above (10^{30}), the proof remains a finite-search completeness theorem; it does not claim that the enormous search was executed. The coefficient bound is conservative, and denominator clearing or forming (Q^{d-1}) can make it large. The coordinate budget is not a universal runtime or memory guarantee.

Run `scripts/check_native_runge_power.sh` for the focused rebuild and audit. The retained cases include 20 complete finite packets, exponents 2 through 10, degree 40, dense high-degree residuals, nonmonic and negative odd-power leading coefficients, fractional truncation and zero fibres. Two certificate-only cases and three exact-power families are checked. The audit also rejects eight unsupported or excessive inputs and false point/root packets. Its 124 printed declarations use only subsets of `propext`, `Classical.choice` and `Quot.sound`. The previous 79-declaration square audit remains available as a regression check, and the higher-power audit is wired into the Lean workflow.

These results provide an effective Runge solver for the stated integer-leading-power class. They do not discharge general Baker bounds, general Runge hypotheses over number fields, arbitrary leading coefficients or arbitrary multivariate equations. General number-ring and function-field solvers, Chabauty rank computations, GPU deployment and WebAssembly remain open. The full historical root build and hosted account runner availability are separate from the focused local proofs recorded here.
