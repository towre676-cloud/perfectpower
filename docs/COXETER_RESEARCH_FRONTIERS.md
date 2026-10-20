# Coxeter research frontiers: arithmetic symmetry and finite recovery

**Source-derived proof monograph, 2026-10-20 UTC.**

This continuation of the [deep-period monograph](PERIOD_BRIDGE_DEEP_MONOGRAPH.md) and the [integral Coxeter–Raghava bridge](RAGHAVA_COXETER_UNIFICATION.md) records two exact mathematical extensions. The arithmetic trace form reconstructs every integral isometry normalizing the supplied Coxeter cycle: its normalizer has order 240 and its extension by the eight Galois actions is nonsplit. The finite positive-moment theorem identifies the folded E₈ reflection spectrum from mass and eight Raghava moments, without a competitor conductor bound. An explicit positive rational counterexample proves the eight-coordinate boundary, and four absolutely convergent odd Mellin observations recover orientation.

The shared equation IDs below agree exactly with the [PerfectJet canonical research registry](https://github.com/towre676-cloud/perfectjet/blob/main/data/research_frontier_equations.json). Common equations do not imply that the two packages contain identical executable engines. The proofs and exact rational replay add no Lean theorem, historical-priority claim, inference of a Lie bracket from spectra, or identification based on equal cardinalities.

## Shared equation table

| ID | Mathematical statement | Status and precise scope |
|---|---|---|
| PJ-E465 | **arithmetic E8 trace form**: `G_ij=Tr_K/Q(alpha*zeta^(i-j)); alpha=(5-zeta-2zeta^2-2zeta^3-zeta^4+zeta^6+2zeta^7)/15` | derived. K=Q(zeta_30), G=B^T A B in the supplied unimodular Krylov basis; Norm(alpha)=1/1265625 and det(G)=1. The cyclotomic realization is classical; explicit source-coordinate identity, no priority claim. |
| PJ-E466 | **integral Coxeter commutant**: `End_Z[<C>](E8)=Z[zeta_30]` | derived. The supplied cyclic vector has an integral Krylov basis; a commuting map is multiplication by its value at 1. This concerns integral linear endomorphisms, not all Lie endomorphisms. |
| PJ-E467 | **Coxeter isometry centralizer**: `u*conjugate(u)=1; C_O(E8)(C)=<C>, order 30` | derived. Use the specified trace form, trace nondegeneracy and Kronecker; alternatively exhaustive root-image replay. The centralizer theorem is classical, not newly discovered here. |
| PJ-E468 | **semilinear arithmetic isometry**: `S_a(x)=u_a*sigma_a(x) is an isometry iff alpha*u_a*conjugate(u_a)=sigma_a(alpha)` | derived. a is a unit modulo 30 and sigma_a(zeta)=zeta^a; S_a must also preserve the integral lattice to be an integral isometry. The norm ratio is sigma_a(alpha)/alpha. |
| PJ-E469 | **complete Coxeter normalizer by cyclic root images**: `K_a(r)=[r,C^a r,...,C^(7a)r]; U=K_a(r)B^-1; K_a(r)^T A K_a(r)=G; \|N_O(E8)(<C>)\|=240` | derived. Enumerate all eight unit exponents and all 240 actual roots; exactly 30 lifts per exponent. Completeness follows from the cyclic basis. There are two root orbits of size 120; the group is not identified with the roots by cardinality. |
| PJ-E470 | **nonsplit arithmetic normalizer extension**: `S C=C^7 S; S^4=C^25; (C^i S)^4=C^(25+10i)!=I` | derived. S(x)=(zeta^2+zeta^3+zeta^4+zeta^5-zeta^7)*sigma_7(x). Every lift of the quotient element 7 has nonidentity fourth power, so 1->C30->N->(Z/30)^*->1 has no section. No historical novelty claim. |
| PJ-E471 | **Raghava moments as positive power moments**: `mu_j=(2j)!*r_j/4^j=sum_q w_q*((q-1/2)^2)^j` | derived. Principal phases 0<=q<1 and nonnegative weights; mu_0=r_0 is mass. Positivity is essential for global finite uniqueness; this identifies a folded spectral measure. |
| PJ-E472 | **exact Hankel annihilator reconstruction**: `H_(s-1)*(p_0,...,p_(s-1))^T=-(mu_s,...,mu_(2s-1))^T` | derived. H_ij=mu_(i+j); s distinct positive-mass folded atoms make H_(s-1) positive definite. p(X)=X^s+sum_(j<s)p_j X^j. This step uses 2s coordinates and a declared atom count. |
| PJ-E473 | **conductor-independent finite positive uniqueness**: `sum_q w_q*p(x_q)^2=0 => support(mu) subset roots(p); mu_0..mu_(2s) determine the positive s-atom profile` | derived. The extra moment mu_(2s) proves support containment for every nonnegative finite competitor, without a competitor conductor or support-size bound; Vandermonde then fixes weights. Signed measures are excluded. |
| PJ-E474 | **all later Raghava moments from a finite annihilator**: `mu_(n+s)+sum_(j=0)^(s-1)p_j*mu_(n+j)=0 for every n>=0` | derived. p vanishes on the recovered folded support. The identity determines all subsequent even moment coordinates; it does not recover the integral lattice or Lie bracket. |
| PJ-E475 | **finite E8 folded spectral certificate**: `E8: x={1,4,16,49}/225, each weight 2; mass and r_1..r_8 certify this folded profile` | derived. Nine coordinates including mass uniquely determine the folded reflection spectrum among all nonnegative finite phase profiles. Four further odd Mellin observations suffice to orient it. |
| PJ-E476 | **sharp eight-coordinate positive rational collision**: `delta_i=1/prod_(j!=i)(x_i-x_j); sum_i delta_i*x_i^k=0 (k<8); sum_i delta_i*x_i^8=1` | derived. Use the nine interlaced nodes 0,1/225,1/100,4/225,1/25,16/225,1/9,49/225,1/4 and weights 2*1_(i odd)+epsilon*delta_i, epsilon=14144/3243658447265625. All weights are positive, phases have conductor dividing 30, and r_0..r_7 match E8. Minimality among dimension-eight integer representations is not proved. |
| PJ-E477 | **oriented recovery by absolutely convergent odd Mellin traces**: `y_k=(-1)^(k+1)*2^(2k)/(2k+1)!*sum_q w_q B_(2k+1)(q); B_(2k+1)(1/2+t)=t*(t^2-1/4)*P_(k-1)(t^2)` | derived. k>=1; y_k is Im(sum_n Tr(T^n)/n^(2k+1))/pi^(2k+1). For s* interior folded nodes, s* rows invert a scaled Vandermonde system and recover orientation. Reflection: 9 even+4 odd sufficient; adjoint:33 even+14 odd. No minimum claim for the combined scheme. |

## Reproduction and proof boundaries

Run `python scripts/export_coxeter_research.py`, then `python scripts/export_coxeter_research.py --check` to recompute the two source-bound child receipts, this full proof monograph and the live summary. The second command requires byte-identical deterministic output. Focused verification is `PYTHONPATH=python python -m unittest python/tests/test_coxeter_normalizer.py python/tests/test_coxeter_reconstruction.py -v`.

The [normalizer receipt](../receipts/period_bridge_deep/trace_normalizer.json) contains the exact trace form, all eight lift fibers and the nonsplitting witness. The [spectral receipt](../receipts/period_bridge_deep/coxeter_reconstruction.json) contains the positive Hankel certificates, complete sharpness counterexample and oriented reflection and adjoint checks. Their source hashes and the scoped research block in the summary identify these fresh computations separately from the historical deep-period `results_sha256`, result path, source-parent identity and proof statuses.

Reflection uses nine even coordinates including mass and four odd coordinates. Adjoint uses 33 even coordinates including mass and 14 odd coordinates. The sharpness claim concerns the nine-even-coordinate reflection certificate among nonnegative rationally weighted profiles. Minimality among actual dimension-eight integer representations, and minimality of the combined even-plus-odd scheme, are not established. These spectral observations do not reconstruct an integral lattice or Lie bracket.

The complete proof chapters follow. Equation labels TN1–TN9 and FR1–FR9 remain local to their respective chapters.

# Arithmetic trace form and the nonsplit Coxeter normalizer

**20 October 2026 UTC.** This extends the [actual integral Coxeter–Raghava bridge](RAGHAVA_COXETER_UNIFICATION.md). The cyclotomic realization of E₈ and the centralizer theorem are classical. The present contribution is an explicit trace form, exhaustive semilinear lifts and a nonsplitting certificate in the repository's precise coordinates. Historical priority is not established. These mathematical proofs and exact Python checks add no Lean theorem.

## The metric as an arithmetic object

Let \(K=\mathbb Q(\zeta)\), \(\zeta=\zeta_{30}\), and \(O=\mathbb Z[\zeta]\). The existing integral bridge \(B=(v,Cv,\ldots,C^7v)\), with \(v\) the eighth simple root, transports the actual E₈ Cartan form \(A\) to \(G=B^TAB\). Multiplication by \(\zeta\) corresponds to \(D=B^{-1}CB\). The arithmetic datum specifying this metric is

\[
\alpha=\frac{5-\zeta-2\zeta^2-2\zeta^3-\zeta^4+\zeta^6+2\zeta^7}{15},
\qquad b(x,y)=\operatorname{Tr}_{K/\mathbb Q}(\alpha x\bar y).
\tag{TN1}
\]

**Trace-form theorem.** In the coefficient basis \(1,\zeta,\ldots,\zeta^7\), this form has matrix exactly \(G\). Its coefficient is real and totally positive, and

\[
\bar\alpha=\alpha,\quad\operatorname{disc}(K)=3^4 5^6=1265625,
\quad N(\alpha)=1265625^{-1},\quad\det G=1.
\tag{TN2}
\]

For a complete finite proof, solve the nonsingular trace system
\(\sum_k\alpha_k\operatorname{Tr}(D^{k+i})=G_{i0}\) for \(0\le i<8\). It gives precisely (TN1). Then verify all64 identities
\(G_{ij}=\sum_k\alpha_k\operatorname{Tr}(D^{k+i-j})\), reducing powers modulo30. This proves the form identity without fitting eigenvalues. Positivity follows from \(G=B^TAB\). In the four conjugate embedding pairs the real scalar extension is \(2\sum_\sigma\sigma(\alpha)|\sigma(x)|^2\), so positivity forces all real conjugates of \(\alpha\) to be positive.

The denominator15 does not make the pairings fractional. The trace dual of \(O\) is its codifferent, and unimodularity proves

\[
\alpha O=\mathfrak D^{-1}.
\tag{TN3}
\]

An independent generator check uses
\(\alpha\Phi'_{30}(\zeta)=1+\zeta-\zeta^3-2\zeta^4-\zeta^5+\zeta^6+2\zeta^7\), an integral unit of norm1. Since the monogenic codifferent is \(\Phi'_{30}(\zeta)^{-1}O\), the displayed unit also proves(TN3). The inverse of \(\alpha\) is \(8+11\zeta+13\zeta^2+9\zeta^3+3\zeta^4-4\zeta^5-7\zeta^6-5\zeta^7\). Every identity is recomputed by rational multiplication matrices.

## Integral commutants and semilinear lifts

An integral endomorphism commuting with \(D\) is determined by its value \(u\) at1 and equals multiplication by \(u\). Thus

\[
\operatorname{End}_{\mathbb Z[\langle C\rangle]}(E_8)=O.
\tag{TN4}
\]

Nondegeneracy of the trace pairing shows that this map is an isometry exactly when \(u\bar u=1\). Every conjugate of an integral such \(u\) has modulus1; Kronecker's theorem makes it a root of unity. The roots of unity in \(K\) are \(\mu_{30}\), giving the conceptual centralizer theorem \(C_{O(E_8)}(C)=\langle C\rangle\), of order30. The finite enumeration below provides an independent proof for this concrete lattice.

If \(UC=C^aU\), with \(a\in(\mathbb Z/30)^\times\), the cyclotomic map must be semilinear:

\[
S_a(x)=u_a\sigma_a(x),\quad \sigma_a(\zeta)=\zeta^a,
\qquad S_a\text{ isometric}\iff\alpha u_a\bar u_a=\sigma_a(\alpha).
\tag{TN5}
\]

Indeed the transported pairing is \(\operatorname{Tr}(\alpha u_a\bar u_a\sigma_a(x\bar y))\). Apply \(\sigma_a^{-1}\) inside the trace and use nondegeneracy. The ratio is \(u_a\bar u_a=\sigma_a(\alpha)/\alpha\); a plain Galois coordinate permutation need not preserve the form.

## Complete normalizer from1920 root-image candidates

An isometry sends the cyclic root \(v\) to an actual root \(r\). Its other columns are forced:

\[
K_a(r)=(r,C^ar,\ldots,C^{7a}r),\quad U=K_a(r)B^{-1},
\qquad U^TAU=A\iff K_a(r)^TAK_a(r)=G.
\tag{TN6}
\]

Check the240 actual roots and eight unit exponents. Exactly30 candidates pass per exponent. Each resulting matrix is integral because \(B^{-1}\) is integral; the isometry equation forces determinant \(\pm1\). The intertwining equation is checked independently. Conversely every normalizer isometry must occur because its exponent and cyclic root image determine it on the entire basis. Therefore

\[
1\longrightarrow C_{30}\longrightarrow N_{O(E_8)}(\langle C\rangle)
\longrightarrow(\mathbb Z/30)^\times\longrightarrow1,
\qquad |N|=240.
\tag{TN7}
\]

Completeness of the roots is elementary in the standard Euclidean model: an integer norm-two E₈ vector has exactly two coordinates \(\pm1\); a half-integer norm-two vector has eight coordinates \(\pm1/2\) with the parity restriction. These are precisely the112+128 supplied roots. Each normalizer fiber is also checked to be one coset of the30 Coxeter powers. Nothing here identifies the240 primitive branches of an unrelated phase fiber with the240 roots.

## A concrete obstruction to splitting

Take \(u_7=\zeta^2+\zeta^3+\zeta^4+\zeta^5-\zeta^7\) and \(S(x)=u_7\sigma_7(x)\). Its cyclic-root image has simple-root coordinates \((0,0,1,1,1,1,1,1)\). Direct multiplication gives

\[
S^TAS=A,\qquad SC=C^7S,\qquad S^4=C^{25}.
\tag{TN8}
\]

Every other lift of7 is \(C^iS\), so

\[
(C^iS)^4=C^{(1+7+7^2+7^3)i+25}=C^{25+10i}\ne I.
\tag{TN9}
\]

The only fourth-power exponents are5,15,25. The quotient element7 has order4, whereas no lift has fourth power1. A section would preserve this relation, so **the extension is nonsplit**. Ten lifts have order8 and twenty have order24. The normalizer has two root orbits of size120; its240 elements therefore do not act regularly on the240 roots.

## Equation table and next mathematical targets

| Equations | Mathematical consequence | Scope |
|---|---|---|
| TN1–TN3 | Explicit metric, unimodularity and trace duality | Actual integral lattice |
| TN4 | Complete integral commuting algebra | Cyclic-basis theorem |
| TN5 | Metric-preserving Galois transport | Semilinear norm equation |
| TN6–TN7 | All240 normalizing isometries | Exhaustive root-image proof |
| TN8–TN9 | Nonsplitting of the extension | Explicit lift and every coset element |

The next ambitious arithmetic target is the real subfield tower, particularly the golden field and the E₈–H₄ construction. It should transport a relative Hermitian form, reflection action and identities in actual coordinates. Reeder's work gives the classical framework; a golden-ratio picture alone would not establish the correspondence. A second target is to transport Raghava moment identities through the now certified isometries \(C\mapsto C^a\).

Run `PYTHONPATH=python python -m unittest python/tests/test_coxeter_normalizer.py -v` and `python scripts/verify_coxeter_normalizer.py`. The latter binds sources and emits the trace form, all eight representative lift matrices, complete fiber counts, root orbits and nonsplitting certificate. There is no external CAS runtime dependency.

Primary references: [Jouve–Rodriguez-Villegas, *On the bilinear structure associated to Bezoutians*](https://arxiv.org/abs/1004.4208), [Hollenbach–Wegener, *The centralizer of a Coxeter element*](https://arxiv.org/abs/1912.01529), and [Reeder, *Cyclotomic structures on root lattices*](https://www.math.utah.edu/~ptrapa/math-library/reeder/reeder-cyclotomic-root-lattices-2008.pdf). These prevent attributing historical novelty to the underlying classical realization or centralizer result. The exact presentation and certificates are contributions to this research programme; their historical priority has not been established.

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
