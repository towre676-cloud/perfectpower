# Finite spectral reconstruction and a sharp positive certificate

**Research checkpoint, 20 October 2026 UTC.** The [Coxeter–Raghava bridge](RAGHAVA_COXETER_UNIFICATION.md) identifies an infinite even Mellin family with normalized inverse-binomial operator moments. This chapter strengthens its spectral conclusion to a finite certificate, an exact sharpness counterexample, and oriented recovery using odd Mellin observations. The mathematics is standard positive-moment and Bernoulli theory applied to the actual repository spectra. Historical priority is not established. The new arguments have mathematical proofs and exact Python replay; this chapter adds no Lean theorem.

## Positive moments turn a trace into a finite identification problem

For a nonnegative finite phase profile \(A=\sum_qw_q[q]\), with \(0\le q<1\), the existing normalized moments are

\[
r_j(A)=\frac{4^j}{(2j)!}\sum_qw_q(q-\tfrac12)^{2j},\qquad
\mu_j=\frac{(2j)!}{4^j}r_j=\sum_i W_ix_i^j,
\quad x_i=(q_i-\tfrac12)^2\in[0,\tfrac14].
\tag{FR1}
\]

Here equal folded nodes are combined, and zero weights are omitted. Thus \(W_i>0\). The zeroth coordinate is mass, as in the original chapter; it is not a weight-zero Mellin evaluation. We obtain an ordinary positive atomic measure \(\sum_iW_i\delta_{x_i}\). The even observations recover the combined pair weights at \(q\) and \(1-q\), not their orientation.

Suppose there are \(s\) distinct folded atoms. Put \(H=(\mu_{i+j})_{0\le i,j<s}\). Its Vandermonde factorization is \(H=V\operatorname{diag}(W_i)V^T\), where \(V_{ji}=x_i^j\). Therefore

\[
\det H=\left(\prod_iW_i\right)\prod_{i<j}(x_j-x_i)^2>0.
\]

The first \(2s\) coordinates determine the monic degree-\(s\) polynomial

\[
p(X)=X^s+\sum_{j=0}^{s-1}p_jX^j,
\qquad H(p_0,\ldots,p_{s-1})^T
=-(\mu_s,\ldots,\mu_{2s-1})^T.
\tag{FR2}
\]

Indeed \(\prod_i(X-x_i)\) satisfies these equations, and nonsingularity makes it their unique solution. Once its roots are known, the first \(s\) moments determine the weights by the Vandermonde inverse. The executable verifier recovers \(p\) from the data and checks a supplied list of rational roots; it does not pretend to factor an arbitrary real polynomial into rational roots.

**Finite positive uniqueness theorem.** The coordinates \(\mu_0,\ldots,\mu_{2s}\) determine this measure among *all* nonnegative finite measures on \([0,1/4]\), without any competitor support or conductor bound.

The extra coordinate establishes

\[
\sum_{i,j=0}^{s}p_ip_j\mu_{i+j}
=\int p(x)^2\,d\mu(x)=0,\qquad p_s=1.
\tag{FR3}
\]

A nonnegative competing measure with the same coordinates has the same zero integral of a nonnegative function. Every atom of that competitor must therefore be a root of \(p\). The roots are exactly the original \(s\) nodes. The Vandermonde system then forces the original weights. Positivity is essential: signed competitors can cancel the square integral. This elementary proof is the univariate positive flat-extension mechanism; compare [Laurent–Mourrain](https://arxiv.org/abs/0812.2563) for the broader moment-theoretic setting.

The recovered annihilator also determines every later even coordinate:

\[
\mu_{n+s}=-\sum_{j=0}^{s-1}p_j\mu_{n+j}\quad(n\ge0).
\tag{FR4}
\]

Thus the result is a certificate for the complete even observation family, not just a short numerical fit.

## E₈ has a nine-coordinate folded fingerprint

For the actual eight-dimensional E₈ reflection operator, the phases are the primitive thirtieth-root phases. Their four folded nodes are

\[
(x_1,x_2,x_3,x_4)=\frac1{225}(1,4,16,49),\qquad W_i=2.
\tag{FR5}
\]

The annihilator is

\[
p(X)=X^4-\frac{14}{45}X^3+\frac{371}{16875}X^2
-\frac{836}{2278125}X+\frac{3136}{2562890625}.
\]

Consequently **mass and the first eight Raghava moments**, \(r_0,\ldots,r_8\), certify the folded E₈ spectrum among every nonnegative finite phase profile. The theorem does not assume a competitor has conductor 30, dimension eight with integer weights, or four folded nodes. It proves spectral uniqueness; it does not recover an integral lattice, root system, bracket or Lie algebra from those moments.

## Eight coordinates really do admit a different positive profile

The ninth even coordinate is necessary within the declared class of nonnegative rationally weighted profiles. Consider the increasing rational-square nodes

\[
(x_0,\ldots,x_8)=
\left(0,\frac1{225},\frac1{100},\frac4{225},\frac1{25},
\frac{16}{225},\frac19,\frac{49}{225},\frac14\right),
\qquad \delta_i=\frac1{\prod_{j\ne i}(x_i-x_j)}.
\]

Lagrange interpolation of \(X^k\), followed by comparison of its degree-eight coefficient, gives

\[
\sum_{i=0}^8\delta_ix_i^k=0\quad(0\le k<8),\qquad
\sum_{i=0}^8\delta_ix_i^8=1.
\tag{FR6}
\]

The signs of \(\delta_i\) alternate: positive at even indices, negative at odd indices. The odd-index nodes are exactly the four E₈ nodes. Define

\[
\varepsilon=\min_{i\in\{1,3,5,7\}}\frac1{-\delta_i}
=\frac{14144}{3243658447265625},\qquad
W'_i=2\mathbf1_{i\text{ odd}}+\varepsilon\delta_i.
\]

Every new weight is strictly positive: each old weight stays at least one, while each even-index weight is positive. Their mass and moments through order seven equal the E₈ values. The order-eight power moment differs by exactly \(\varepsilon\). Every node is a rational square of an offset from \(1/2\), and all phases obtained by taking the two offsets have conductor dividing 30. Split each interior folded weight equally between its two phases; retain each self-dual endpoint once. The exact phase array and all weights are emitted by the verifier.

This is an exact positive same-conductor counterexample. Its weights are rational, not integral, so it does **not** establish a minimum among actual dimension-eight representations. Clearing denominators gives actual larger representations, with the reference an integral multiple of the E₈ spectrum. The sharpness claim retains this boundary.

## Odd Mellin observations recover the phase orientation

For \(k\ge1\), define

\[
y_k(A)=\frac1{\pi^{2k+1}}\operatorname{Im}
\sum_{n\ge1}\frac{\operatorname{Tr}(T^n)}{n^{2k+1}}
=\frac{(-1)^{k+1}2^{2k}}{(2k+1)!}
\sum_qw_qB_{2k+1}(q).
\tag{FR7}
\]

The series converge absolutely, since their weights are at least three. The identity is the classical [Bernoulli sine Fourier series, DLMF 24.8.2](https://dlmf.nist.gov/24.8.E2). No weight-one regularization or convention for a conditionally convergent trace is required.

Suppose the folded nodes and weights have been recovered, and \(s_*\) of those nodes lie strictly inside \((0,1/4)\). At an interior node write \(t_i=\sqrt{x_i}>0\) and
\(d_i=w(1/2+t_i)-w(1/2-t_i)\). Bernoulli parity and endpoint identities imply

\[
B_{2k+1}(\tfrac12+t)=t(t^2-\tfrac14)P_{k-1}(t^2),
\qquad P_{k-1}\text{ monic of degree }k-1.
\tag{FR8}
\]

Indeed the centered polynomial is odd, vanishes at \(t=0,\pm1/2\), and has leading coefficient one. Dividing gives a monic even polynomial. After removing the nonzero known row normalizations in (FR7), the observations \(y_1,\ldots,y_{s_*}\) form a linear system in the differences \(d_i\). Its determinant is

\[
\left(\prod_i t_i(x_i-\tfrac14)\right)
\prod_{i<j}(x_j-x_i)\ne0.
\tag{FR9}
\]

This follows by monic row operations reducing \(P_0,\ldots,P_{s_*-1}\) to the power basis. Recover the two phase weights as \((W_i\pm d_i)/2\). The self-dual endpoints already specify their single phase weights and contribute zero to the odd observations. The executable inverse uses rational angles and checks that all recovered phase weights are nonnegative. The mathematical Vandermonde argument applies to arbitrary real angles as well.

For reflection, \(s_*=4\). The four odd observations at weights 3, 5, 7 and 9 vanish, so together with the nine even coordinates they recover precisely the eight primitive thirtieth-root phases, each of multiplicity one. Thus 13 scalar coordinates including mass suffice for the oriented fingerprint. This is a sufficient count, not a proved minimum for combined even-plus-odd schemes.

For the actual adjoint Coxeter lift, the spectrum \(8+\mathbf1_{\gcd(j,30)=1}\) has 16 folded nodes, including both self-dual endpoints. Its analogous certificate uses 33 even coordinates and 14 odd observations. The weight-two cancellation alone is far weaker than such complete spectral identification.

## Equation table and reproduction

| Mechanism | Exact role | Scope |
|---|---|---|
| FR1 | Raghava coordinates become positive power moments | Finite rational weighted phase profiles |
| FR2 | Recover the monic annihilator from a Hankel system | First \(2s\) coordinates, nonzero Hankel determinant |
| FR3 | Force every positive competitor onto the same roots | \(2s+1\) coordinates; no conductor bound |
| FR4 | Predict the entire later even family | Exact finite recurrence |
| FR5 | Certify the actual E₈ folded spectrum | Four nodes, weight two each, nine coordinates |
| FR6 | Exhibit a positive rational collision at eight coordinates | Same conductor 30; no dimension-eight integer minimum claim |
| FR7–FR9 | Restore phase orientation | \(s_*\) absolutely convergent odd Mellin observations |

Run `PYTHONPATH=python python -m unittest python/tests/test_coxeter_reconstruction.py -v`, then `python scripts/verify_coxeter_reconstruction.py`. The deterministic receipt in `receipts/period_bridge_deep/coxeter_reconstruction.json` includes both spectra, annihilators, Hankel determinants, orientation checks, the complete positive sharpness witness, and source SHA-256 bindings. The implementation requires only the standard library. Its 12 focused tests cover exact E₈ recovery, an independent Vandermonde determinant, recurrence prediction through order 32, positive profiles through conductor 12, oriented recovery through conductor 14, an independent sine-series comparison with an explicit absolute tail, malformed data and negativity, and the exact positive collision.

These spectral results complement the integral trace-form and normalizer certificates. They do not replace them: matching every trace of a finite-order operator does not by itself identify its integral realization or its Lie bracket.
