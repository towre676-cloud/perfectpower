# A=B: boundary-complete sum compilation (PerfectPower 0.9.5)

The source is Marko Petkovšek, Herbert S. Wilf and Doron Zeilberger,
*A=B*, [author-hosted PDF](https://sites.math.rutgers.edu/~zeilberg/AeqB.pdf).
Chapters 5–8 motivate rational antidifferences, creative telescoping, WZ
certificates and hypergeometric recurrence solutions. This release implements
an original bounded search and a small exact checker. It does not distribute the
book or claim to implement the complete Gosper, Zeilberger or Hyper algorithms.

## The missing connection

The existing `wz_certificates.py` verifies an interior rational identity in
Q(n)(k), but explicitly does not prove that summation endpoints disappear.
The existing `ThetaSeries` generates a formal series from a supplied operator,
but does not establish that an external sequence satisfies that operator.
This chapter supplies the missing link for a concrete family:

\[
S_p(n)=\sum_{k=0}^{n}\binom nk^p,\qquad p\in\{1,2,3,4\},\ n\ge0.
\]

The term definition, finite support, shift identity, endpoint cancellation and
initial values are checked together. The resulting differential operator is
therefore connected to a specified sum, rather than merely to numerical seeds.
The first two families yield order-one recurrences; the cube and fourth power
yield order-two recurrences. No rank or global minimal-order theorem is claimed.

## A polynomial certificate with safe endpoints

Fix an attempted order r and put N=n+r. Use the last shifted summand as the
common reference. For j=0,...,r,

\[
\frac{\binom{n+j}{k}^p}{\binom N k^p}
=\left(\frac{\prod_{h=0}^{r-j-1}(N-k-h)}
{\prod_{h=0}^{r-j-1}(N-h)}\right)^p=:U_j(n,k).
\]

This quotient is used as a rational identity first. The associated equality
of binomial terms extends across their zeros: when k>n+j, one numerator
factor is zero, and when k>N every binomial term is zero. Each denominator
factor is at least n+j+1 on the stated domain.

Seek coefficients a_j(n) in Q(n), normalized by a_r=1, and a polynomial
b(n,k) in k such that

\[
\sum_{j=0}^r a_j(n)U_j(n,k)
=(N-k)^p b(n,k+1)-k^p b(n,k).
\]

Matching powers of k produces an exact linear system over Q(n). Search tries
orders 1 through a supplied maximum, at most 3, and a supplied polynomial
degree, at most 12; the default degree is pr. This is a restricted ansatz,
not a universal denominator-reduction algorithm. An unsuccessful search says
`ANSATZ_UNRESOLVED`, never that no recurrence exists.

Set

\[
G(n,k)=k^p b(n,k)\binom Nk^p.
\]

The polynomial identity gives the summand recurrence as G(n,k+1)-G(n,k).
At k=N, the shifted binomial term is zero, so the same equality holds there
without dividing by it. G(n,0)=0 because p>0. G(n,N+1)=0 because its binomial
factor is zero. Summing from k=0 through N proves

\[
\sum_{j=0}^r a_j(n)S_p(n+j)=0\quad(n\ge0).
\]

The replay checks every certificate coefficient denominator is a polynomial
with positive constant coefficient and nonnegative remaining coefficients.
This sufficient test proves no poles for n>=0. It is deliberately stricter
than full real-root isolation: some valid alternative packets are refused.
There are no k denominators in b, so no hidden endpoint poles. Replay also
recomputes the first r sums directly. Leading coefficient one makes forward
execution unique for all n>=0.

For example, the cube sum compiles to

\[
(n+2)^2 S_3(n+2)
-(7n^2+21n+16)S_3(n+1)-8(n+1)^2S_3(n)=0,
\]

with S_3(0)=1 and S_3(1)=2. Its initial terms are
1, 2, 10, 56, 346, 2252, 15184, 104960.
This recurrence is discovered from the symbolic summand identity, not guessed
from those eight terms.

## Connecting the ordinary generating function

Clear the common Q(n) denominators to get polynomials A_j(n).
Let theta=z*d/dz and define

\[
L=\sum_{j=0}^r z^{r-j} A_j(\theta-j).
\]

At coefficient index m>=r, this is the forward recurrence at n=m-r.
The finitely many coefficients m<r need a polynomial forcing term calculated
from the checked initial sums. Keeping that forcing is essential: blindly
setting it to zero would reject or change the sequence. `theta_from_telescoping`
constructs the operator and delegates guarded exact execution to `ThetaSeries`.

These sequences generally have polynomial-coefficient recurrences. They are
not automatically finite-dimensional constant-coefficient realizations of the
kind DynaComp's rational generating-function bridge minimizes. This release
therefore changes PerfectPower only; it does not mislabel holonomic sequences
as finite-state linear systems.

## Antidifferences and proposed closed forms

`discover_antidifference` solves the identity

\[
r(k)R(k+1)-R(k)=1
\]

with a supplied polynomial denominator and bounded numerator degree. If
`t(k+1)=r(k)t(k)`, then R(k)t(k) is an antidifference. The checker independently
reconstructs the rational identity. `sum_from_antidifference` checks every
needed ratio denominator and certificate endpoint in a bounded integer
interval before returning its boundary difference. The supplied initial term
is a premise, explicitly recorded. This refuses poles even when a different
analytic continuation could cancel them. Empty intervals return zero only
when their certificate endpoint is defined.

The finite summation executor transports the term by exact ratio products;
it does not promise constant-time endpoint evaluation. The benefit here is a
reusable checked identity, not a universal faster summation claim.

`certify_hypergeometric_solution` substitutes a supplied rational first-order
ratio into the discovered forward recurrence and checks its initial values.
It proves equality to the sum using recurrence uniqueness and the positive
denominator guard. Retained packets prove ratios 2 for S_1 and
(4n+2)/(n+1) for S_2. A proposed constant ratio 8 for S_3 is rejected. Rejecting
one proposed solution does not establish that S_3 has no hypergeometric form.
Full Hyper and certified nonsummability decisions remain future work.

## Exact power queries and reproducibility

`BinomialSumSequence.power_hits` executes a bounded sequence window and calls
the existing exact integer power-root decision for each value. It reports all
hits in that window and explicitly denies an unbounded classification. For
S_1(n)=2^n, the square query over indices 0 through 119 finds exactly the even
indices. This illustrates the end-to-end definition→identity→recurrence→integer
value→power-root path. For the harder families, absence of hits in a finite
window proves nothing about all later indices.

Run the retained examples and independent direct-sum cross-checks with:

```sh
PYTHONPATH=python python python/run_telescoping.py
PYTHONPATH=python python -m perfectpower generating-function examples/telescoping/binomial_power_3.json
PYTHONPATH=python python -m perfectpower.telescoping replay receipts/telescoping/binomial_power_3.json
PYTHONPATH=python python -m unittest discover -s python/tests -p test_telescoping.py -v
```

Six example specifications, eight certificate receipts and a summary are
retained. Four families are independently cross-checked through index 100 in
the regeneration script. Tests also check shifted finite intervals, geometric
and polynomial sums, rational telescopes, corrupted identities, seed changes,
poles, incomplete searches, closed-form candidates and command-line replay.

All new proofs are exact Python replay, not Lean kernel theorems. Existing
Lean results are unchanged. Algebra, coefficient bits, term windows and
sequential indices have explicit limits inherited from the rational-function
and formal-series engines. Hitting a limit raises a work-limit exception;
it does not provide evidence against a mathematical identity. No performance
claim, revenue claim or benchmark extrapolation follows from this release.
