# A real Coxeter–Raghava bridge: lattices, moments, and induction

**PerfectPower. Mathematical chapter prepared 17 October 2026.**

The construction in this chapter replaces an association between pictures by an explicit integral coordinate map and a commuting system of exact operations. The eight-dimensional E₈ Coxeter lattice is identified with an integral cyclotomic companion module, including its bilinear form. Raghava's inverse-binomial series are then applied to that actual operator. A triangular Bernoulli transformation identifies their traces with the real even Mellin traces of the same operator. Ordinary cyclic induction acts on both descriptions, and the transformation intertwines the two actions. This is the precise sense of unification used here. It does not assert an equivalence of unspecified higher categories or a physical model.

## The actual integral lattice map

Let \(A\) be the E₈ Cartan matrix in the simple-root ordering used by `e8_periods.py`, and let \(C=s_8\cdots s_1\) be its Coxeter matrix, with \(s_1\) acting first. In the coefficient basis of

\[
\Lambda=\mathbb Z[X]/(\Phi_{30}(X)),\qquad
\Phi_{30}(X)=X^8+X^7-X^5-X^4-X^3+X+1,
\]

write \(D\) for multiplication by \(X\). Let \(v\) be the eighth simple-root coordinate vector, and form the Krylov matrix

\[
B=(v,Cv,C^2v,\ldots,C^7v).
\]

For the supplied ordering, this is the explicit matrix

\[
B=\begin{pmatrix}
0&0&0&0&0&0&1&0\\
0&0&0&0&0&1&0&1\\
0&0&0&0&0&1&1&0\\
0&0&0&0&1&1&1&1\\
0&0&0&1&0&1&1&1\\
0&0&1&0&0&1&1&1\\
0&1&0&0&0&1&1&0\\
1&0&0&0&0&1&0&0
\end{pmatrix}.
\]

It has an integral two-sided inverse. Thus it is a unimodular change of lattice coordinates, rather than a map available only after allowing rational denominators. Direct multiplication establishes

\[
CB=BD,\qquad B^{-1}B=BB^{-1}=I,
\qquad G=B^{\mathsf T}AB.
\tag{1}
\]

Equip \(\Lambda\) with the Gram matrix \(G\), rather than silently assigning it a different trace form. Equation (1) gives an isometry of integral lattices with their specified operators. In particular,

\[
(Bx)^{\mathsf T}A(By)=x^{\mathsf T}Gy,
\qquad C^nB=BD^n\quad(n\ge0).
\tag{2}
\]

The norm-two vectors correspond under this map, with their pairings preserved. This supplies an actual cyclotomic realization of the E₈ root lattice and its Coxeter action. It does not identify a list of primitive field-conjugate branches with a list of roots by their common size.

The proof is finite integral arithmetic for the inverse, intertwining and Gram identities, followed by induction for (2). The source `PerfectPower/CoxeterPhaseBridge.lean`, in namespace `PerfectPower.CoxeterPhaseBridge`, records the concrete matrices and the statements `bridge_inverse_left`, `bridge_inverse_right`, `integralBridge`, `coxeter_intertwining`, `all_power_conjugacy`, `transported_cartan`, `bridge_preserves_bilinear` and `norm_two_iff`. The chapter's final proof-status paragraph distinguishes these source statements from successful kernel compilation.

There is also a precise connection to the original phase of conductor 1680. Put \(\omega=\zeta_{1680}\) and \(\eta=\omega^{56}=\zeta_{30}\). The inclusion \(\mathbb Q(\eta)\subset\mathbb Q(\omega)\) has degree \(384/8=48\). Consequently multiplication by \(\eta\) on \(\mathbb Q(\omega)\), considered as a rational cyclic module, is 48 copies of multiplication by \(\eta\) on \(\mathbb Q(\eta)\). After the rational extension of (1), it is 48 copies of the E₈ reflection module. Choosing a basis of this field extension makes that direct-sum isomorphism explicit; no canonical integral basis of the larger extension is claimed here. Every operator trace developed below therefore scales by 48 on this conductor-1680 module.

## One operator produces the Raghava and Mellin families

Let \(T\) be a finite-order complex linear operator on a finite-dimensional space \(V\). Its eigenvalues have the form \(e^{2\pi iq}\), with representatives \(0\le q<1\). Repeated eigenvalues retain their multiplicities. A finite-order operator is diagonalizable, because its minimal polynomial divides a polynomial \(X^N-1\) with distinct complex roots. Equivalently, averaging any positive Hermitian inner product over its finite cyclic group makes \(T\) unitary. Thus the following spectral construction does not require the displayed matrix of \(T\) to be Hermitian in its original basis.

Define

\[
L_T=2I+T+T^{-1}.
\]

Its eigenvalue at phase \(q\) is

\[
\lambda(q)=2+2\cos(2\pi q)=4\cos^2(\pi q)\in[0,4].
\tag{3}
\]

For \(j\ge1\), define the finite harmonic factors by

\[
\prod_{a=1}^{n-1}\left(1+\frac{z}{a^2}\right)
=\sum_{r\ge0}e_r(n)z^r.
\]

The empty product at \(n=1\) is one. The scalar identity used by Raghava is

\[
\sum_{n\ge1}\frac{e_{j-1}(n)t^{2n}}
 {n^2\binom{2n}{n}}
=\frac{4^j}{(2j)!}\arcsin(t/2)^{2j},\qquad |t|<2.
\tag{4}
\]

This is [Raghava, Eq. (2.2)](https://arxiv.org/html/2607.09904v2), with the paper's stated classical antecedents retained. The coefficient normalization is important: at \(j=1\), the right side is \(2\arcsin(t/2)^2\).

**Operator moment theorem.** The series

\[
\mathcal R_j(T)=\sum_{n\ge1}
\frac{e_{j-1}(n)L_T^n}{n^2\binom{2n}{n}}
\tag{5}
\]

converges in every matrix norm, and its eigenvalue at phase \(q\) is

\[
\frac{(2\pi)^{2j}}{(2j)!}(q-\tfrac12)^{2j}.
\tag{6}
\]

To prove this, take \(t=\sqrt{\lambda(q)}=2|\cos(\pi q)|\). For \(0\le q\le1\),

\[
\arcsin(|\cos(\pi q)|)=\pi|q-\tfrac12|.
\]

Equation (4) therefore gives (6) whenever \(\lambda(q)<4\). At \(\lambda=4\), every summand of (4) is nonnegative. Taking \(t\uparrow2\), monotone convergence for the counting measure gives the endpoint sum as the finite limit \(\pi^{2j}/(2j)!\). This is the required endpoint argument; substituting a boundary value into an open-disk power-series statement without it would leave a gap. There are finitely many eigenspaces, so absolute scalar convergence on each eigenspace gives convergence of the matrix series after conjugation by a fixed diagonalizing matrix. This proves (5)–(6), including trivial eigenphases.

Write

\[
r_0(T)=\dim V,\qquad
r_j(T)=\pi^{-2j}\operatorname{Tr}\mathcal R_j(T)
=\frac{4^j}{(2j)!}\sum_q m_q(q-\tfrac12)^{2j}.
\tag{7}
\]

These definitions extend linearly to finite rationally weighted phase profiles. Positivity is needed for the endpoint proof for each scalar series, not for extending the resulting identities by finite rational linearity.

For \(k\ge1\), write

\[
Z_T(2k)=\operatorname{Re}\sum_{n\ge1}
\frac{\operatorname{Tr}(T^n)}{n^{2k}},\qquad
z_k(T)=Z_T(2k)/\pi^{2k}.
\tag{8}
\]

Absolute convergence follows from finite dimension and finite order. When describing coordinate vectors below, define the additional zeroth coordinate to be \(z_0=r_0=\dim V\). **This is a coordinate convention, not a definition or evaluation of a Mellin trace at weight zero.**

## The exact invertible Bernoulli transformation

**Moment–Mellin theorem.** For every \(k\ge1\),

\[
\boxed{z_k(T)=\sum_{j=0}^k c_{kj}r_j(T),\qquad
c_{kj}=\frac{(-1)^{k+1}4^{k-j}B_{2k-2j}(1/2)}
 {2(2k-2j)!}.}
\tag{9}
\]

For the zeroth row set \(c_{00}=1\) and \(c_{0j}=0\) for \(j>0\). For every finite order \(K\), the matrix \(\mathcal B_K=(c_{kj})_{0\le k,j\le K}\) is triangular and invertible over \(\mathbb Q\).

The classical Bernoulli Fourier identity, [DLMF 24.8.1](https://dlmf.nist.gov/24.8.E1), gives

\[
\operatorname{Re}\operatorname{Li}_{2k}(e^{2\pi iq})
=\frac{(-1)^{k+1}(2\pi)^{2k}}{2(2k)!}B_{2k}(q).
\]

Expand the Bernoulli polynomial about \(1/2\). Its odd centered coefficients vanish, because \(B_{2k}(1-x)=B_{2k}(x)\). Substituting (7) into this finite centered expansion gives (9) term by term. Its diagonal is \(c_{kk}=(-1)^{k+1}/2\ne0\). Hence the inverse is obtained recursively without any assumption of numerical independence of special constants.

The first two rows are

\[
z_1=-\frac{r_0}{12}+\frac{r_1}{2},\qquad
z_2=-\frac{7r_0}{720}+\frac{r_1}{12}-\frac{r_2}{2}.
\tag{10}
\]

Consequently the retained even Mellin observations and Raghava moments contain exactly the same information at each finite order. The complete families determine the inversion-symmetrized finite phase profile: if two profiles differ, collect their distinct values of \((q-1/2)^2\). The first corresponding power moments form a Vandermonde system with distinct nodes, so their simultaneous vanishing forces every combined weight to be zero. This recovers pair weights at \(q\) and \(1-q\), rather than the orientation of an individual nonreal phase or the Lie bracket of a representation. A short truncation need not already identify the whole profile. The coordinate transformation is additive and respects intertwining operators; it is not claimed to turn tensor products into products of integral values.

## An exact inverse-binomial evaluation from the E₈ operator

Return to the actual eight-dimensional Coxeter matrix \(C\), and put \(L=2I+C+C^{-1}\). Its primitive phases have exponents

\[
1,7,11,13,17,19,23,29\pmod {30}.
\]

None is trivial, so \(L\) has no eigenvalue four. The finite matrix identity

\[
L^4-7L^3+14L^2-8L+I=0
\tag{11}
\]

gives an efficient exact integer recurrence. If \(a_n=\operatorname{Tr}(L^n)\), then

\[
(a_0,a_1,a_2,a_3)=(8,14,42,146),
\qquad
a_{n+4}=7a_{n+3}-14a_{n+2}+8a_{n+1}-a_n.
\tag{12}
\]

Thus \(a_4=538\), \(a_5=2044\), \(a_6=7902\) and \(a_7=30856\). These are traces of the actual matrix in (1), not coefficients chosen to fit a desired sum.

The phase formula (7) gives

\[
r_1(C)=\frac{56}{45},\qquad
r_2(C)=\frac{10696}{151875},\qquad
r_3(C)=\frac{194896}{102515625}.
\]

In particular,

\[
\boxed{\sum_{n\ge1}\frac{a_n}{n^2\binom{2n}{n}}
=\frac{56\pi^2}{45}.}
\tag{13}
\]

Equations (1), (5) and (12) are the mechanism behind this evaluation. At higher orders the same integer sequence \(a_n\) is weighted by \(e_{j-1}(n)\), producing \(\pi^{2j}r_j(C)\). No new operator must be fitted for each weight. On the conductor-1680 module with action by \(\omega^{56}\), equation (13) scales to \(896\pi^2/15\).

There is a fully explicit independent remainder bound. Let \(\rho<1\) be any rational upper bound for \(\cos^2(\pi/30)\), obtained here from rational Machin bounds for \(\pi\) and a cosine Taylor remainder. Then \(0\le a_n\le8(4\rho)^n\). The inequalities

\[
e_r(n)\le\frac{2^r}{r!},\qquad
\binom{2n}{n}\ge\frac{4^n}{2n+1}
\]

show that the tail after \(N\ge0\) terms at moment \(j\) is at most

\[
\frac{24\,2^{j-1}}{(j-1)!(N+1)}
\frac{\rho^{N+1}}{1-\rho}.
\tag{14}
\]

The first inequality follows by bounding the elementary symmetric sum by a power of \(\sum_{a\ge1}a^{-2}<2\), divided by \(r!\). The second follows because the central binomial coefficient is the largest of the \(2n+1\) coefficients whose sum is \(4^n\). For \(n\ge N+1\), \((2n+1)/n^2\le3/(N+1)\), giving (14) by a geometric sum. The implementation sums (13) independently using exact rational coefficients, then rounds the result outward. At 4096 terms it obtains an enclosing interval of width less than \(1.518\times10^{-20}\), around \(12.28217436580009\). The closed value is used only for an independent interval comparison, never to manufacture the partial sum or remainder.

## The actual adjoint lift and its cancellation

The exact construction in `python/perfectpower/e8_lift.py` uses the E₈ Lie bracket and simple-root exponentials to construct an actual adjoint Coxeter lift \(T_{\mathrm{ad}}\), not merely an abstract 248-dimensional vector space. Its signed root-space cycles have product-one sign around every orbit. Removing those signs by a checked coordinate change gives eight regular cycles of length thirty, together with the Cartan spectrum above. The Lie construction and lift conventions are described in `docs/E8_LIFT_NOTE.md`, with classical inputs from [Geck's simply-laced lattice-cocycle construction](https://arxiv.org/html/2602.19632v1) and [Adams–He's Coxeter-lift order theorem](https://arxiv.org/abs/1608.00510). Thus its phase multiplicities are

\[
m_j=8+\mathbf1_{\gcd(j,30)=1},\qquad0\le j<30.
\tag{15}
\]

Direct evaluation of (7) for (15) gives \(r_0=248\) and \(r_1=124/3\). Equation (10) therefore proves \(Z_{T_{\mathrm{ad}}}(2)=0\), while (5) identifies that same cancellation with a positive inverse-binomial operator identity:

\[
\boxed{\sum_{n\ge1}
\frac{\operatorname{Tr}(L_{T_{\mathrm{ad}}}^n)}{n^2\binom{2n}{n}}
=\frac{124\pi^2}{3}.}
\tag{16}
\]

The eight trivial phases in (15) contribute eigenvalue four to \(L_{T_{\mathrm{ad}}}\). They can be removed exactly. Each contributes \(\pi^{2j}/(2j)!\) to the \(j\)-th moment. At first order this yields

\[
\boxed{\sum_{n\ge1}
\frac{\operatorname{Tr}(L_{T_{\mathrm{ad}}}^n)-8\,4^n}
 {n^2\binom{2n}{n}}
=\frac{112\pi^2}{3}.}
\tag{17}
\]

The remaining coefficients are nonnegative, and their 240 eigenvalues are bounded by \(4\rho<4\). Replacing rank eight by rank 240 in (14) gives an exponential tail bound for (17) and its higher moments. A separate 2048-term rational sum encloses (17) with width less than \(5.382\times10^{-9}\). Adding the removed endpoint contribution gives (16), and (10) recovers the exact zero Mellin trace. This provides a convergent computational route to the same cancellation through Raghava's positive sums.

## Induction is an exact operation on the moments

Consider a finite weighted phase profile \(A=\sum_q w_q[q]\), with rational weights and \(0\le q<1\). Ordinary cyclic induction of degree \(d\ge1\) replaces each phase \(q\) by

\[
\frac{q+u}{d},\qquad0\le u<d,
\]

with the original weight on each branch. Write \(r_j(A)\) for (7) with these weights, including \(r_0(A)=\sum_qw_q\).

**Moment transfer theorem.** For every \(j\ge0\),

\[
r_j(\operatorname{Ind}_d A)=\sum_{k=0}^j M_d(j,k)r_k(A),
\tag{18}
\]

where

\[
M_d(j,k)=\frac{4^{j-k}d^{-2j}}{(2j-2k)!}
\sum_{u=0}^{d-1}\left(u-\frac{d-1}{2}\right)^{2j-2k}.
\tag{19}
\]

The diagonal is \(M_d(j,j)=d^{1-2j}\), including \(M_d(0,0)=d\). To prove the formula, write the centered phase of an induced branch as

\[
\frac{q+u}{d}-\frac12
=\frac{q-1/2+u-(d-1)/2}{d}.
\]

Expand its even power by the binomial theorem. Every odd power of the second centered term sums to zero under \(u\leftrightarrow d-1-u\). The remaining even terms give (18)–(19), with the factorials cancelling exactly as displayed. The finite centered sums can be evaluated by the Bernoulli–Faulhaber formula, so the algorithm does not have to enumerate an enormous number of branches.

Inducing first by \(e\) and then by \(d\) produces the same phases, with multiplicity, as induction by \(de\): the two branch indices combine by the ordinary mixed-radix bijection. Therefore

\[
M_dM_e=M_{de}.
\tag{20}
\]

The finite matrices here are truncated at a common order; triangularity makes the same equality valid at every such truncation. The full-fiber root-of-unity filter also gives

\[
z_k(\operatorname{Ind}_d A)=d^{1-2k}z_k(A),\quad k\ge1.
\]

Together with mass scaling, this proves the commuting identity

\[
\boxed{\mathcal B_K M_d
=\operatorname{diag}(d,d^{-1},d^{-3},\ldots,d^{1-2K})\mathcal B_K.}
\tag{21}
\]

It is also an independent consequence of the Bernoulli multiplication formula. Equation (21) is the exact connection among branch filtering, Raghava moments and Mellin traces. It makes no appeal to a numerical resemblance between their values.

## A preserved cancellation and a sharp uniqueness statement

At first order, (18) becomes

\[
r_1(\operatorname{Ind}_d A)
=\frac{r_1(A)}d+\frac{d^2-1}{6d}r_0(A).
\]

Define the cancellation defect

\[
\Delta(A)=r_1(A)-\frac{r_0(A)}6=2z_1(A).
\]

Since \(r_0(\operatorname{Ind}_d A)=d\,r_0(A)\),

\[
\boxed{\Delta(\operatorname{Ind}_d A)=\Delta(A)/d.}
\tag{22}
\]

Thus induction preserves and reflects an exact zero; it cannot produce a zero defect from a nonzero one. For the actual adjoint profile (15), \(r_0=248\), \(r_1=124/3\), and \(\Delta=0\). At \(d=264\), equations (18) and (22) give

\[
r_0'=65472,\qquad r_1'=10912,\qquad\Delta'=0.
\tag{23}
\]

Inflating the order-thirty spectrum to conductor 1680 before induction does not change any phase or moment, and places this degree-264 operation at conductor 443520. This is how the reference multiplier enters a genuine operation on the E₈ spectral object. The resulting mass 65472 is the induced adjoint dimension; it is not the dimension of E₈ or the size of one primitive fiber.

There is a useful uniqueness theorem with an explicit scope. Among the two-parameter phase profiles

\[
w_j=a+b\,\mathbf1_{\gcd(j,30)=1},\qquad a,b\in\mathbb Q,
\]

the mass and first moment are

\[
r_0=30a+8b,\qquad r_1=\frac{451a+112b}{90}.
\]

Direct subtraction gives

\[
\boxed{\Delta=\frac{a-8b}{90};\qquad\Delta=0\iff a=8b.}
\tag{24}
\]

Thus the actual adjoint mixture has the uniquely required ratio of regular to primitive multiplicity in this ansatz. With nonnegative integral \(a,b\), the smallest nonzero cancelling profile is \(a=8,b=1\), of mass 248; every other such profile is an integral multiple. This does not classify all cyclic representations with a weight-two zero. The restriction to this regular-plus-primitive family is essential.

The Lean source `PerfectPower/RaghavaInduction.lean` defines arbitrary finite rational weighted profiles and proves the finite centered-square formula underlying (22). Its named statements include `fiberMoment_eq`, `inducedMoment_eq`, `induction_defect`, `induction_zero_iff`, `coxeter_family_defect` and `coxeter_family_zero_iff`. Its finite rational formula is valid for arbitrary rational phase coordinates. The analytic identification with (5) additionally uses the principal representatives \(0\le q\le1\), as specified above.

## Why the tempting 240-to-240 identification fails

The primitive branches above the fixed phase \(\zeta_{1680}\) have exponents

\[
u=1+1680t,\quad0\le t<264,\quad\gcd(u,443520)=1.
\]

There are 240 such branches. Every exponent satisfies \(u\equiv1\pmod{30}\). Restricting their characters from \(C_{443520}\) to its natural \(C_{30}\) subgroup therefore gives 240 copies of the single phase \(\zeta_{30}\). The root-space part of the actual E₈ Coxeter lift gives eight copies of every thirtieth-root phase. The multiplicity functions disagree, so no equivariant isomorphism exists for this proposed natural restriction. An arbitrary bijection of the two underlying sets cannot repair that representation-theoretic obstruction.

The integral lattice isomorphism (1) and the commuting formulas (9), (18) and (21) avoid this problem. They identify specified operators and preserve specified forms or transformations. They do not require the false fixed-fiber identification.

## Proof scope, reproducibility and originality

The analytic results in this chapter have mathematical proofs from the cited classical scalar identities, finite spectral calculus, the centered binomial expansion and elementary convergence estimates. Historical priority for their present combination or the displayed E₈ inverse-binomial evaluations has not been established. They are reported as derived bridges and concrete evaluations, rather than as a newly discovered special-function summation principle.

The exact Python implementation is `python/perfectpower/raghava_coxeter.py`. Its `receipt(order=8)` recomputes the operator polynomial, moment and Mellin coordinates, triangular inverse, degree-264 transfer checks, fixed-fiber obstruction and independent series enclosures. The focused command is `PYTHONPATH=python python3 -m unittest python/tests/test_raghava_coxeter.py -v`. All eleven focused tests passed during preparation of this chapter. They include 6560 exact scalar phase comparisons through conductor forty and weight sixteen, 81 powers of the actual eight-dimensional matrix, 41 powers of the actual signed 248-dimensional adjoint matrix, exact transfer composition and Bernoulli diagonalization, and positive-series tail comparisons. These checks exercise independent finite mechanisms; they are not substitutes for the general mathematical proofs.

The three new Lean modules compile with pinned Lean 4.20.0 and Mathlib 4.20.0. The integrated audit checks all 102 theorem declarations: 15 finite Fourier and fiber theorems, 61 integral Coxeter and operator theorems, and 26 rational phase-moment and induction theorems. Their axiom reports contain only the standard propext, Classical.choice and Quot.sound; no admitted proof, native decision oracle or new axiom occurs. Reproduce with `make raghava-coxeter-kernel`. The source-bound result is retained in `receipts/period_bridge_deep/unification_lean.json`. The infinite-series, functional-calculus and analytic convergence arguments in this chapter remain mathematical proofs outside the Lean kernel; the Lean files do not import them as new axioms.

## Source-driven cinematic companion

The cinematic resonance now projects actual conjugates and refinement
branches, applies genuine integer power-map endpoints and moves every root
by the exact Coxeter successor. Moment partials, signed Mellin partials,
spectral traces and exact cancellations are inspectable. Projection and
interpolation scope are specified in [the visualization account](INTEGRAL_ATLAS_NOTE.md).
This rendering adds no new mathematical equivalence or Lean theorem.
