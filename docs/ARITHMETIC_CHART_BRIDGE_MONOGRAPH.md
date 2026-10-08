# Rational power charts and unordered weighted determinants

## Three connected arithmetic extensions

This chapter transports rational-polynomial power equations through complete integrality charts, switches the bounded residue engine across every horizontal, vertical and singular Hensel branch, and removes the factorial overcount in the weighted Gram determinant identity. The concurrent arithmetic pipeline supplies content-normalized blowups and a general weighted local-vector expansion; its modules and public operations are preserved. This extension supplies denominator-scaled original-coordinate congruences, typed complete chart-family counts and the Gaussian-rational Gram specialization with positivity. The new modules build on the integer-valued polynomial, factored intersection, bounded patch and ordered Cauchy–Binet foundations. They preserve the original integer coordinates and existing atlas APIs. This is the arithmetic lane; concurrent wall widths and flavor work remain separate.

The generic mathematical bridge is kernel checked in Lean 4.20.0 with the repository's pinned Mathlib. Eight literal power packets and two weighted determinant examples replay concrete original-coordinate identities, complete covers, exact populations and bounded solution lists. The Python services retain exact rational and Gaussian-rational arithmetic. The general JSON parser, traversal interpreter and source-to-native compiler are not proved equivalent to the Lean definitions.

## Denominator primes change the source modulus

Write a rational polynomial as Q(x)=F(x)/L with integer F and positive common denominator L. The integrality domain is exactly F(r)=0 modulo L. Its canonical residues r between zero and L−1 give disjoint charts x=r+Ln. Expanding F(r+Ln)/L yields an integer-coefficient polynomial G_r(n), because the constant coefficient is divisible by L and every nonconstant term contains L. No integrality residue is dropped, even when Q is integer valued at every integer.

$$
Q(r+Ln)=G_r(n),\qquad Q(x)=y^d\ \Longleftrightarrow\ F(x)=Ly^d.
$$

The exact source equality transports through each chart. The congruence requires a scaled modulus in the original coordinates. This distinction matters precisely when the denominator and residue modulus share a prime.

$$
Lm\mid F(r+Ln)-Ly^d\ \Longleftrightarrow\ m\mid G_r(n)-y^d.
$$

For Q(x)=x/2 and d=2, imposing only F(x)−2y² modulo two accepts every even x, including (2,0). The correct source modulus four rejects that point. In the worked modulus-four parameter atlas, the original periods are eight in x and four in y. There are 23 modular candidates in [−8,8] × [−4,4], and the exact power solutions are (0,0), (2,−1), (2,1), (8,−2), (8,2).

Additional integer-polynomial partial-domain restrictions are pulled back coefficientwise under x=r+Ln and retained as distinct source constraints. Shared primes use the existing maximal-power factored intersection. Let B be the primary equation period and M the LCM of B with the restriction periods. The combined cover has parameter period M, original x-period LM and original y-period M. The equation is still imposed modulo B, hence its original source modulus is LB. A restriction of higher prime-power depth must not silently strengthen the equation from B to M. An independent original-coordinate census exposed and now guards that distinction.

## Signed boxes and exact family populations

For inclusive original x-bounds a and b, the chart parameter bounds are computed with mathematical floor division, including negative endpoints. The y interval is unchanged.

$$
n_{\min}=\left\lfloor\frac{a-1-r}{L}\right\rfloor+1,\qquad n_{\max}=\left\lfloor\frac{b-r}{L}\right\rfloor.
$$

`RationalPowerAtlas.parameter_bounds` proves the affine-bound equivalence. `chart_complete` transports the actual typed predicate cover to the original rectangle, and `chart_count` expresses its cardinality as a short sum over residue cells. `chart_disjoint` proves that distinct canonical residues have disjoint images. `family_complete` and `family_count` assemble all charts and prove the original-coordinate union and population, rather than assuming a supplied total count.

The service keeps factored prime-group tuples when explicit residues exceed the representation budget. Population is an exact integer; rank and select use chart order, then the existing prime-group tuple order, then the parameter and y cell offsets. These addressing operations are tested against direct enumeration and huge signed intervals, but their generic interpreter refinement remains open.

For Q(x)=x/2, primary factors eight, nine and five, and the square of radius ten to the fortieth, the periods are 720 and 360. The complete candidate population below is kernel checked by the literal chart-family count certificate; the enormous rectangle is not enumerated and no bounded solution list is claimed for it.

```
555555555555555555555555555555555555554583333333333333333333333333333333333333
```

## Complete bounded switching and branching patches

`rational_power_patch` verifies the entire transported atlas, counts the full bounded population before scanning, evaluates the denominator-cleared source at every retained candidate, and returns the exact original-coordinate solution list. It attaches the existing auxiliary-polynomial relation packet in the original coordinates. Independent replay rejects altered source terms, missing chart evidence, altered auxiliary relations and incomplete point lists.

Every local root node retains its lifting evidence. A nonzero y-derivative permits a vertical lift, a nonzero x-derivative permits a horizontal lift, both derivatives zero require all singular children, and incompatible affine lifting data certify an obstructed node. Atlas switching and restriction intersections retain all combinations; the engine never selects one representative branch. Native certificates reuse the actual complete local tables and prove their simultaneous typed covers.

The cusp y²=x³ modulo eight and nine is the branching regression. Its packet has two vertical, three horizontal, six singular and two obstructed nodes. In [−5,5]² the three modular candidates are exactly (0,0), (1,−1), (1,1), all source solutions. The native proof establishes the original-coordinate source table and complete auxiliary relations. Thus a patch with mixed orientations is checked end to end, rather than demonstrated only on a nonsingular root.

| Equation and bounded domain | Integral chart residues | Candidates | Exact source points |
|---|---|---|---|
| y²=x/2; [−8,8] × [−4,4] | 0 modulo 2 | 23 | 5 |
| y²=x(x−1)/2; [−8,9] × [−4,4] | 0,1 modulo 2 | 20 | 6 |
| y²=x²/4; [−6,6] × [−3,3] | 0,2 modulo 4 | 25 | 13 |
| y²=x²/9; [−6,6] × [−2,2] | 0,3,6 modulo 9 | 13 | 9 |
| y³=x/2; x+y=0 modulo 4 | 0 modulo 2 | 1 | 1 |
| y²=x³; [−5,5]² | 0 modulo 1 | 3 | 3 |
| y²=1/2 | none | 0 | 0 globally |

The final empty-domain example proves global impossibility by integrality, not by exhaustion of a finite box. All other finite point-list claims are restricted to their stated rectangles. In the restricted cubic example, x+y=0 modulo four is a modular partial-domain condition, not an added exact equation.

## The genuinely unordered weighted identity

Let B have a finite linearly ordered row type and n columns over a commutative characteristic-zero domain with an involution. Give each row a weight w. The Gram entry sums w times the conjugate of the first matrix entry times the second. The ordered theorem in `CauchyBinet.lean` multiplies the Gram determinant by n! because every row subset has n! orderings. The new theorem sums each subset once.

$$
\det(B^*WB)=\sum_{|S|=n}\left(\prod_{i\in S}w_i\right)\overline{\det B_S}\det B_S.
$$

`UnorderedWeightedGram.Basis` is the subtype of n-element finite row sets. Sorting supplies a canonical minor. A bijection between injective row selections and a subset together with a permutation groups the ordered sum. Repeated-row selections have zero minor. Row permutation changes each determinant by its sign; conjugation fixes the integer sign and the two signs cancel. Cancellation of the nonzero n! gives `weighted_gram`. No full-rank assumption or nonzero-weight hypothesis is needed. Fewer rows than columns and zero columns are included.

For real nonnegative weights, `real_nonnegative` proves the Gram determinant is nonnegative. For strictly positive real weights, `real_zero_iff` proves that it is zero exactly when every maximal minor vanishes. This is the all-minors formulation of rank deficiency; the theorem does not invoke a separate matrix-rank API. Zero weights remain allowed in the identity and positivity theorem but cannot be used in the strict-positive vanishing equivalence.

The exact Gaussian-rational service computes each minor once, reconstructs the weighted sum, independently computes the Gram determinant by field elimination and checks equality. It accepts complex weights; positivity flags are asserted only when every weight is real and nonnegative. The native real example has rows (1,0), (0,1), (1,1), weights two, three and five, and determinant 31. The native complex example has rows (1,i), (i,1), (1,1), weights 1+i, 2−i and zero, and determinant 12+4i. Zero-weight and rank-deficient packets exercise the degenerate cases.

## Reproduction, budgets and validation

Run `make check-arithmetic-chart-bridge` with Lean 4.20.0 and pinned Mathlib. It regenerates eight power packets, runs seventeen focused tests, crosschecks 120 power cases and 120 weighted matrices independently, builds both generic Lean modules, audits their nineteen generic declarations, and compiles every native worked proof with an axiom allowlist. The complete audit covers 504 declarations: nineteen generic facts and 485 native declarations. Neither `sorryAx` nor the native decision oracle `Lean.ofReduceBool` is permitted. Neighbor validation passes 79 residue tests and 20 integer-valued polynomial tests.

The power crosscheck tests 33,600 original rectangle coordinates and 41,256 anisotropic-period coordinates, including 46 empty modular domains. It uses direct rational evaluation and the original integer source moduli, not the chart engine to decide expected membership. The determinant crosscheck uses separate SymPy exact matrix determinants and 899 unordered subsets. Both compare actual solution lists and count/addressing outputs, not only packet self-consistency.

Power inputs have degree at most twelve, exponent two through twelve, common denominator at most 32, one through eight distinct primary prime-power factors with local moduli at most 256, and at most four additional polynomial restrictions. Native generation further inherits local modulus at most 32, at most 64 lifting nodes, at most 2048 prefix combinations and at most eight charts. Complete native source tables have at most 64 points. The Gaussian-rational determinant service permits at most sixteen rows, eight columns and 2048 unordered subsets. Unsupported budgets raise before a completeness result is issued.

## Remaining implementation boundary

The generic Lean statements prove rational source transport, denominator-scaled congruences, signed chart bounds, typed original-coordinate covers and their exact cardinalities. Literal native programs establish their concrete source identities and bounded output semantics. Python independently verifies each supplied packet and exact certificate. This combination supplies reusable mathematical facts and concrete replay, while leaving a clearly named generic implementation obligation.

The next bounded push should formalize a typed factor traversal and then the chart-family address interpreter. Define the normalized prime-group state, prove one unpruned leaf per CRT tuple, prove a zero axis population safely prunes every descendant, and distinguish a complete run from budget failure. Prove successful counts equal the existing typed candidate cardinality; derive rank/select inverses in the actual chart/tuple order. Only then refine parser and code emitter semantics. No new Mordell rank bound, global height theorem, prime saturation theorem or compiler correctness claim is made here.
