# Native effective Runge recognition for expanded square-value equations

This push adds an unconditional, native Lean route from an expanded integer polynomial to a complete answer for its integer square values. The recognizer accepts closed ascending coefficient lists of positive even degree with positive integer-square leading coefficient. It reconstructs a polynomial square at infinity, clears its rational denominators, proves an explicit coordinate bound, and checks the complete list of original integer points. Exact-square inputs produce a parameterized relation. There is no supplied integral-point list, analytic height premise, Sage or Singular invocation, Python arithmetic bridge, JSON certificate, `sorry`, custom axiom or `native_decide` in this route.

The implementation consists of `PerfectPower/RungePolynomial.lean` and `PerfectPower/Tactic/RungePolynomial.lean`. The former contains the reusable mathematical theorems. The latter proposes exact rational arithmetic data and elaborates ordinary kernel-checked proof terms. An error in the proposal generator cannot certify an incorrect result: the polynomial identity, degree comparison, nonzero leading coefficients and equality of the complete finite search with the displayed packet must all pass Lean.

## Use directly in Lean

Coefficients are in ascending order. Thus `[1,1,0,0,0,0,1]` means (x^6+x+1). The following complete program generates the four points and a theorem quantifying over every pair of integers:

```lean
import PerfectPower.Tactic.RungePolynomial

native_runge sextic for [1,1,0,0,0,0,1]
#check sextic_complete
#print sextic
#print axioms sextic_complete
```

The result is exactly `(-1,-1), (-1,1), (0,-1), (0,1)`. The generated theorem states `y^2 = NativePolynomialSquare.eval [1,1,0,0,0,0,1] x ↔ (x,y) ∈ sextic`. It is a proof of completeness over all integers, rather than a test within a chosen coordinate window. The accompanying `sextic_decomposition` and `sextic_bound` expose the identity and effective bound.

The shell entry point runs the same native command. With the pinned Lean toolchain and Mathlib available, run `scripts/solve_native_runge.sh '1,1,0,0,0,0,1'`. It builds the focused target, reports the completeness theorem and its axiom dependencies, and displays a finite packet when one was generated. `--source-only` prints a standalone Lean program that can be saved and checked later. Input is restricted to decimal integer coefficients; it is not evaluated as shell code.

## Polynomial square-root truncation

Write (F(x)=c^2x^{2n}+cdots), where (c) is a positive integer. There is a unique rational polynomial (U(x)=cx^n+u_{n-1}x^{n-1}+cdots+u_0) whose square agrees with (F) in degrees (2n,2n-1,ldots,n). At each descending step the new coefficient appears with multiplier (2c), so exact rational division determines it. The recognizer performs this computation with Lean's rational numbers. It then chooses the least common multiple (a) of their positive denominators, sets (Q=aU), and computes (R=a^2F-Q^2). The resulting integer coefficients satisfy

\[
 a^2F(x)=Q(x)^2+R(x),\qquad \deg R<\deg Q.
\]

The command emits a theorem of this identity for every integer (x), proved with `norm_num` and `ring`. It independently checks the normalized degree and validity predicates. The mathematical library does not assume that the native generator is correct. Formalizing the generator's symbolic correctness and success for all inputs is a separate possible refinement; each accepted concrete input already has a fully checked identity and complete answer.

For (F=x^6+x^5+1), the computation gives (a=16), (Q=16x^3+8x^2-2x+1), and (R=-20x^2+4x+255). Therefore (256F=Q^2+R), and the explicit general bound below is 307. For (F=x^6+x^4), it gives (a=2), (Q=2x^3+x), (R=-x^2); the original curve has exactly the point `(0,0)`. Searching the original square equation rather than the scaled completion prevents extra scaled points from entering the final answer.

## Effective bound without an analytic premise

For an ascending integer coefficient list (p), let (H(p)) be the sum of the absolute values of its coefficients. A list is valid when its last coefficient is nonzero; this gives the actual polynomial degree. `degree_domination` proves the following statement for all integer polynomials represented in this way:

\[
 \deg R<\deg Q,\quad |x|\ge H(Q)+H(R)+1
 \quad\Longrightarrow\quad |R(x)|+1\le |Q(x)|.
\]

The proof inducts directly on the Horner representation. Removing the constant coefficients produces shorter lists with the same degree inequality. The inductive strict gap is multiplied by (|x|); the explicit height bound pays for both removed constant coefficients. This works uniformly for both signs of the coordinate and arbitrary integer coefficients. It does not require a root-separation oracle or an asymptotic theorem.

If (Y^2=Q(x)^2+R(x)) and (R(x)\ne0), the existing difference-of-squares lemma gives (|Q(x)|\le|R(x)|): the two nonzero integer factors (Y-Q(x)) and (Y+Q(x)) divide the nonzero residual. This contradicts degree domination outside the bound. Hence `bound_or_residual_zero` proves (|x|\le B) or (R(x)=0), for (B=H(Q)+H(R)+1).

When (R) is valid, its roots are also bounded: apply the same degree-domination theorem to (R) and the zero polynomial. Consequently `coordinate_bound` proves the unconditional bound (|x|\le B) for every solution. This includes the zero-residual branch. The enumeration nevertheless retains the exact integer roots of (R) in its candidate set, keeping the exceptional fibre explicit and preserving the reusable structure needed by sharper future bounds.

For the original curve, set (Y=ay). `complete` proves that (y^2=F(x)) is equivalent to membership in the finite union of square-root fibres over the interval ([-B,B]) and the integer roots of (R). The integer-root algorithm is already proved complete; zero constant coefficients are peeled recursively. Each square-root fibre is computed by the existing verified integer square-root implementation. Both signs are retained, while a zero square root occurs once. Every candidate is tested against the original (F), so no denominator divisibility assumption or scaled extraneous point is hidden.

## Exact squares and large bounds

When the computed residual is zero, there is no finite coordinate search. `square_family` proves exactly

\[
 y^2=F(x)\quad\Longleftrightarrow\quad ay=Q(x)\ \lor\ ay=-Q(x),\qquad a\ne0.
\]

For example, `native_runge family for [1,2,1,2,2,0,1]` recognizes ((x^3+x+1)^2), and `family_complete` gives the two branches. The scaled relation retains any necessary integer divisibility. The command creates no misleading finite packet or finite bound for this branch.

The default command refuses a nonzero-residual interval containing more than 10,001 coordinates before adding generated declarations. This is a resource policy, not a mathematical limitation or an assertion that every smaller case will fit every machine. The general height bound is conservative; denominator clearing can make it large. `native_runge_certificate` emits the decomposition, the unconditional bound and the complete equivalence with `RungePolynomial.points`, without evaluating the finite packet. For instance, `native_runge_certificate huge for [1000000000000000000000000000001,1,0,0,0,0,1]` proves completeness of its finite search without attempting to enumerate approximately (2\cdot10^{30}) coordinates. Its mathematical proof is unconditional; its point list has not been evaluated.

## Verification and scope

Run `scripts/check_native_runge.sh` to rebuild the seven focused dependency modules and check the audit. The audit covers 16 explicit finite packets, two large or fractional certificate-only cases, and two exact-square families. It includes dense octic and decic coefficients, degrees 2 through 20, a nonmonic sextic, rational square-root truncation, trailing zero input coefficients, negative residuals, zero square-root fibres and a nonzero zero-residual fibre at `(10,±1000)`. It checks rejection of odd degree, nonsquare or negative leading coefficient, constants, the zero polynomial and an excessive enumeration budget. False packets and false polynomial identities are also tested for rejection. The 79 printed declarations depend only on subsets of `propext`, `Classical.choice` and `Quot.sound`.

The retained receipts also check the shell entry point, standalone source generation, the exact-square branch and certificate-only use at a huge bound. The new audit is wired into the Lean workflow. Local verification does not establish that a blocked GitHub account runner has been repaired; that deployment condition remains separate.

This is an effective square-value solver for the stated rational-branches-at-infinity family. It is not a formalization of general Runge theory over arbitrary number fields, a Baker bound, a general Chabauty algorithm, or automation for arbitrary exponents and polynomials. A nonsquare leading coefficient can lead to Pell behaviour and requires a different branch. Classical Chabauty requires Mordell–Weil rank strictly below genus. Number-ring solvers, general function-field equations and GPU or WebAssembly deployment remain open. The next mathematical extension can reuse the domination theorem and recognizer boundary while adding sharper leading-term bounds or exponent-specific power-gap estimates.
