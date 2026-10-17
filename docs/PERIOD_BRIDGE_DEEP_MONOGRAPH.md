# Deep Integral Bridges: Raghava Generators, Cyclotomic Descent, and Coxeter Spectra

**PerfectPower mathematical reader. 17 October 2026 (UTC).**

The organizing principle of this work is to retain the mechanism that makes an integral exact. In Raghava's generating functions, a finite harmonic product and a carefully chosen normalization cancel unwanted orders. In a cyclotomic sum, a finite Fourier filter removes unwanted indices. In an adjoint Coxeter spectrum, the root-space cycles and Cartan eigenvalues create a prescribed cancellation. Retaining each mechanism produces a reusable family, an explicit coefficient system, and a controlled numerical remainder, rather than one isolated evaluated integral.

The implementation now contains 130 complete Raghava generating-family records, 65 in each of two families, through weight 131. It preserves all 120 earlier selected-order identities by an exact decomposition into those complete generators. The sine-pole and arcsine families remain available, with their convergence conditions and rational tail estimates. The theorem-supported generating construction extends to arbitrary fixed order; the source code's order bounds control resource use.

The supplied artifact angles lead to three distinct, useful counts: a base cyclotomic field of degree 384, a complete induced branch fiber of size 264, and a primitive conjugate fiber of size 240. These counts are connected by exact conductor maps, an induced polynomial factorization, and a two-term reduction of 240 polylogarithmic integrals. A finite linear category supplies actual matrices, induction and restriction, and the explicit Hom-space bijection of Frobenius reciprocity. An ordinary directed colimit is proved by a common-conductor construction. Those are concrete classical realizations of part of the artifacts' ambition; the higher categorical diagrams require additional definitions before they specify further theorems.

The E8 construction has advanced beyond a dimension analogy. Its actual 248-dimensional Lie algebra, simple-root exponentials, and Tits lifts are implemented with sparse exact arithmetic. Computing the root-space signs and their cycle gauges identifies the adjoint Coxeter spectrum and proves the spectral Mellin zero at weight two for the stated actual lift. A logarithmic companion is nonzero and exact. The full periodic trace can be represented by a minimal 30-state output machine, while the reflection trace requires eight states; neither compression changes the 248-dimensional Lie algebra itself.

A final classification covers every irreducible reduced crystallographic root system. Types A, D, and E have their unique real Mellin zero at weight two. Types B and C move that zero with rank, and their rank can be selected to place it at any requested integer weight at least two. The rank-seven weight-four example gives a zero integral and the logarithmic value $-\pi^4\log 2/5145$. Types F4 and G2 have no real zero on the common half-plane. The complete sign argument appears below, together with the normalization needed to distinguish the Mellin trace from the raw integral.

The result is an exact working bridge among harmonic sums, special functions, finite spectral objects, Lie-theoretic operators, and observation quotients. Classical sources are attributed throughout. The finite computations are Python arithmetic and explicit certificates, supplemented by cited analytic theorems; they are not new Lean-kernel proofs and do not establish historical priority. A separate 240-dimensional field-conjugate fiber is never identified with E8 root spaces merely because the dimensions agree.

The final operator bridge puts the Raghava inverse-binomial moments and the even Mellin traces on one actual Coxeter operator. An explicit integral lattice conjugacy, an invertible Bernoulli coordinate transform, and an induction law for the weight-two defect give a precise commuting construction. The fixed 240-branch identification is ruled out by its character, while degree-264 induction preserves the actual adjoint cancellation. The finite Lean scope and the separate analytic proof are stated in the new chapter.

## A guide to the reader

The first part starts from the two artifact angles and develops the root filters. The next two parts emphasize Raghava: first the elementary integral and arcsine mechanisms, then the complete generating functions and global inequalities. The middle parts supply the exact periodic-character engine and the finite linear descent construction. The final parts establish the actual E8 lift, compress its complete observations, and derive the all-type Coxeter classification and weight tuner. The last part records reproduction, source provenance, and the distinction between a mathematical result, a fresh computation, and a public application update.


## The mathematical objects behind the pictures

The project inputs include the two public Claude artifacts attributed by the user to Cody Lakeland: the [Categorical-Spectral-Cyclotomic visualization](https://claude.ai/public/artifacts/1db99748-b7fd-477b-8a9c-1bb54fb33a19) and the [384-264 Resonance visualization](https://claude.ai/public/artifacts/4fd0f32a-22b6-4fae-b2d2-1f3732d324af). The earlier source audit found canvas visualizations with fixed phase labels and comments proposing categorical connections. They motivate the mathematical inputs used here. The author's Facebook identity and the original Facebook posts were not independently recovered.

Write

\[
q=e^{i\pi/840}=\zeta_{1680},\qquad
Q=e^{i\pi/221760}=\zeta_{443520}.
\]

Here \(\zeta_n=e^{2\pi i/n}\). Since \(221760=264\cdot840\), the elementary phase identity is

\[
Q^{264}=q.
\]

This is an actual map between roots of unity. The three important counts have different meanings:

| Quantity | Exact value | Meaning |
|---|---:|---|
| \(\varphi(1680)\) | 384 | Degree of \(\mathbb Q(q)\) over \(\mathbb Q\) |
| \(443520/1680\) | 264 | Number of branches solving \(z^{264}=q\) |
| \(\varphi(443520)/\varphi(1680)\) | 240 | Number of conjugates of \(Q\) over \(\mathbb Q(q)\) |
| \(\varphi(1680)/2\) | 192 | Degree of the maximal real subfield of \(\mathbb Q(q)\) |

Thus a branch count of 264 is not the relative field degree, which is 240. The degree 96 belongs to other related conductors, including \(\varphi(420)\), and cannot serve as the maximal real degree at conductor 1680. Such distinctions determine which averaging operation is mathematically available. They also specify what a future categorical interpretation would have to explain.

## One integral kernel for every rational phase

For \(\Re s>1\) and \(|z|=1\), define

\[
I_s(z)=\frac{1}{\Gamma(s)}
\int_0^1\frac{z(-\log x)^{s-1}}{1-zx}\,dx.
\]

The power of the positive real number \(-\log x\) uses its real logarithm. Expanding the geometric kernel and integrating each monomial gives

\[
\frac{1}{\Gamma(s)}\int_0^1x^{n-1}(-\log x)^{s-1}\,dx=n^{-s},
\qquad
I_s(z)=\sum_{n\ge1}\frac{z^n}{n^s}=\operatorname{Li}_s(z).
\]

Absolute convergence on the stated half-plane justifies the interchange, including \(z=1\). This common domain is intentionally used throughout the phase-filter engine. Some individual kernels admit wider domains, but those continuations are separate analytic statements. The integral representation and polylogarithm conventions are recorded in the [NIST Digital Library of Mathematical Functions, §25.12](https://dlmf.nist.gov/25.12).

The finite Fourier identity

\[
\sum_{j=0}^{d-1}e^{2\pi ijn/d}
=d\,\mathbf{1}_{d\mid n}
\]

then proves the distribution formula

\[
\sum_{j=0}^{d-1}I_s(ze^{2\pi ij/d})
=d^{1-s}I_s(z^d).
\]

The reduction is structural. Every disallowed series index cancels before any numerical approximation. For the artifact parameters it reads

\[
\sum_{j=0}^{263}I_s(Qe^{2\pi ij/264})
=264^{1-s}I_s(q).
\]

More generally, a periodic coefficient sequence \(c_1,\ldots,c_N\) defines a rational kernel

\[
\frac{\sum_{r=1}^{N}c_rx^{r-1}}{1-x^N}.
\]

Its Mellin integral is the Dirichlet series with those periodic coefficients. Discrete Fourier inversion expresses that series as a finite combination of \(I_s(\zeta_N^j)\). This is the operational bridge between rational logarithmic integrals and finite phase geometry. It recognizes an entire family rather than matching a single decimal constant.

## From 240 conjugates to two periods

The complete 264-branch fiber contains nonprimitive roots. The conjugate fiber relevant to the field extension retains precisely the primitive roots. Its exponents are

\[
u=1+1680t,\qquad 0\le t<264,\qquad \gcd(u,443520)=1.
\]

Only the prime 11 is new when passing from conductor 1680 to 443520. All other prime divisors already divide 1680 and cannot divide \(1+1680t\). Since \(1680\equiv8\pmod{11}\), the excluded class is \(t\equiv4\pmod{11}\). There are 24 excluded values, leaving 240.

The complete fiber reduces to \(264^{1-s}I_s(q)\). The excluded exponents have the form \(6721+18480k\), \(0\le k<24\), and their 24th powers have phase

\[
\frac{24\cdot6721}{443520}
=\frac{611}{1680}\pmod1.
\]

A second Fourier distribution therefore subtracts exactly the 24-branch contribution. Write \(U\) for the retained 240 values of \(t\). Then

\[
\boxed{
\sum_{t\in U}
I_s\!\left(\zeta_{443520}^{1+1680t}\right)
=264^{1-s}I_s(q)-24^{1-s}I_s(q^{611}).
}
\]

The same calculation works for arbitrary \(n\mid N\), not merely these conductors. Suppose \(\gcd(a,n)=1\), and let \(P\) contain the prime divisors of \(N\) absent from \(n\). Write \(U_{n,N,a}\) for the primitive residues modulo \(N\) congruent to \(a\) modulo \(n\). Inclusion-exclusion over the squarefree products of primes in \(P\) gives

\[
\sum_{u\in U_{n,N,a}}
I_s(\zeta_N^u)
=\sum_{d\mid\prod_{p\in P}p}
\mu(d)\left(\frac{N}{nd}\right)^{1-s}
I_s\!\left(\zeta_n^{a d^{-1}\bmod n}\right).
\]

Indeed, imposing \(d\mid u\) and writing \(u=dv\) changes the congruence to \(v\equiv ad^{-1}\pmod n\). The resulting full fiber contains \(N/(nd)\) roots, so its distribution formula gives the displayed term. If \(a\) is not a unit modulo \(n\), the primitive fiber is empty. This case is represented explicitly rather than passed through an invalid modular inverse.

For even weight \(2k\), the Bernoulli Fourier identity gives

\[
\Re I_{2k}(e^{2\pi it})
=\frac{(-1)^{k+1}2^{2k-1}}{(2k)!}B_{2k}(t)\pi^{2k},
\qquad 0\le t<1.
\]

The [DLMF Bernoulli Fourier expansions](https://dlmf.nist.gov/24.8) fix the normalization. Consequently every rational phase at positive even weight has an exact rational real coefficient. Here the weight-two and weight-four reductions are

\[
\Re\sum_{u}I_2(\zeta_{443520}^u)
=\frac{22537}{6773760}\pi^2,
\]

\[
\Re\sum_{u}I_4(\zeta_{443520}^u)
=\frac{21467004594397}{43971386730872832000}\pi^4.
\]

The software computes the source-side Bernoulli sum independently of the reduced side. Agreement therefore tests both the retained fiber and the reduction coefficients; it does not merely reevaluate a stored formula.


## Raghava's sine-over-pole family

The recovered [ICTP interview](https://ictp.global/news/13119204) displays Raghava's first seven sine-over-pole examples and credits Abdulhafeez Abdulsalam with the all-order generalization. The implementation preserves those separate roles. A useful parameter extension follows directly from the same elementary residue calculation.

For an integer \(k\ge1\) and positive real \(a,b\), put

\[
J_k(a,b)=\int_{-\infty}^{\infty}
\left(\frac{\sin(ax)}{x-ib}\right)^kdx.
\]

For \(k\ge2\) the integral is absolutely convergent. For \(k=1\), each half-line converges as an ordinary oscillatory improper integral. Expand

\[
\sin(ax)^k=(2i)^{-k}\sum_{j=0}^{k}
(-1)^j\binom{k}{j}e^{ia(k-2j)x}.
\]

For a positive frequency \(c\), closing the contour above gives

\[
\int_{\mathbb R}\frac{e^{icx}}{(x-ib)^k}\,dx
=\frac{2\pi i(ic)^{k-1}}{(k-1)!}e^{-bc}.
\]

Negative frequencies close below and contribute zero. The zero-frequency term, when present, also integrates to zero for \(k\ge2\). Thus

\[
\boxed{
J_k(a,b)=\frac{\pi a^{k-1}}{2^{k-1}(k-1)!}
\sum_{j=0}^{\lfloor(k-1)/2\rfloor}
(-1)^j\binom{k}{j}(k-2j)^{k-1}e^{-ab(k-2j)}.
}
\]

For example, \(J_1(a,b)=\pi e^{-ab}\), \(J_2(a,b)=\pi a e^{-2ab}\), and

\[
J_3(a,b)=\frac{\pi a^2}{8}
\left(9e^{-3ab}-3e^{-ab}\right).
\]

The substitution \(y=ax\) independently checks the scale relation \(J_k(a,b)=a^{k-1}J_k(1,ab)\). The exact output consists of rational coefficients and exponential powers. Its optional binary64 evaluation is separately labeled because severe cancellation can reduce floating-point accuracy at high order.

## Arcsine kernels as exact coefficient machines

Raghava's current [arcsine and inverse-binomial paper](https://arxiv.org/html/2607.09904v2) supplies the specific harmonic and two-order constructions implemented here. The paper explicitly traces its evaluations to classical hypergeometric transformations and inverse-sine expansions. The release follows that attribution and implements a bounded range of the formulas, rather than claiming a new summation principle.

Set \(y(t)=\cos(2u\arcsin(t/2))\), using the inverse-sine branch that vanishes at the origin. Direct differentiation gives

\[
(4-t^2)y''-ty'+4u^2y=0,
\qquad y(0)=1,\quad y'(0)=0.
\]

Writing \(y=\sum c_nt^{2n}\) gives a complete rational recurrence:

\[
c_0=1,\qquad
c_{n+1}=\frac{n^2-u^2}{2(n+1)(2n+1)}c_n.
\]

This proves the kernel expansion

\[
\cos(2u\arcsin(t/2))
=1-u^2\sum_{n\ge1}
\frac{t^{2n}}{n^2\binom{2n}{n}}
\prod_{j=1}^{n-1}\left(1-\frac{u^2}{j^2}\right),
\qquad |t|<2.
\]

For integer \(u\), the recurrence terminates. For example, \(u=3\) gives the polynomial \(1-9t^2/2+3t^4-t^6/2\). This provides an independent finite check without evaluating inverse trigonometric functions numerically.

Define elementary symmetric factors by

\[
\prod_{j=1}^{n-1}(1+z/j^2)=\sum_{r\ge0}e_r(n)z^r.
\]

They satisfy the finite update

\[
e_r(n+1)=e_r(n)+n^{-2}e_{r-1}(n),
\qquad e_0(n)=1.
\]

Extracting the coefficient of \(u^{2j}\) from the kernel and cosine expansions proves

\[
\boxed{
\sum_{n\ge1}\frac{e_{j-1}(n)t^{2n}}
{n^2\binom{2n}{n}}
=\frac{4^j}{(2j)!}\arcsin(t/2)^{2j}.
}
\]

At \(t=2\sin(\pi/840)\), the principal inverse sine recovers \(\pi/840\). Therefore the first moments equal \(\pi^2/352800\) and \(\pi^4/746807040000\). The refined artifact angle \(\pi/221760\) produces the same identities with an additional factor \(264^{-2j}\). This directly connects the two phase resolutions to an all-order harmonic series family.

The rational-input evaluator also produces a rigorous truncation bound. Since

\[
0\le e_r(n)\le\frac{2^r}{r!},\qquad
\binom{2n}{n}\ge\frac{4^n}{2n+1},
\]

the tail beyond \(M\) terms of the \(j\)-th moment, with \(\rho=t^2/4<1\), is bounded by

\[
\frac{3\,2^{j-1}}{(j-1)!}
\frac{\rho^{M+1}}{(M+1)(1-\rho)}.
\]

The bound is conservative but exact and transparent. Algebraic angle specializations and rational-input enclosures use different APIs, so an expression such as \(2\sin(\pi/840)\) is never silently substituted into an API that promises an exact rational argument.

## Deliberate cancellation of two selected orders

A second use of Raghava's construction chooses an odd polynomial and a harmonic weight so that unwanted Fourier constants vanish. Let \(\alpha=\pi/6\), and define Lidstone polynomials by

\[
\ell_0(v)=v,\qquad \ell_k''=\ell_{k-1},\qquad
\ell_k(0)=\ell_k(1)=0\quad(k\ge1).
\]

Their even endpoint derivatives select individual orders. For \(1\le r<s\), write \(\lambda_k=\ell_k'(0)\) and form

\[
P_{r,s}(\theta)=\alpha^{2s-1}(2s-1)!
\left[\ell_{s-1}(\theta/\alpha)
-\frac{\lambda_{s-1}}{\lambda_{r-1}}
\ell_{r-1}(\theta/\alpha)\right].
\]

The linear term cancels. Only the even endpoint derivatives corresponding to orders \(r\) and \(s\) can remain. Choose

\[
D=2^{2r+2s-2},\qquad
A=D+2^{2r-1}+2^{2s-1}.
\]

Then the Fourier multiplier factors exactly as

\[
1+(D-A)z+Dz^2
=(1-2^{2r-1}z)(1-2^{2s-1}z).
\]

Its two roots are precisely \(2^{1-2r}\) and \(2^{1-2s}\). The polynomial removes every other even sine order, and the multiplier removes the two selected orders. This is cancellation by construction, with an explicit finite reason for every vanished coefficient.

The relation to an integral follows from elementary harmonic insertion. For \(P(\theta)=\sum p_j\theta^{2j-1}\), set

\[
w_P(n)=\sum_j\frac{p_j(2j-1)!}{4^j}e_{j-1}(n).
\]

The inverse-binomial generating function and \(t=2\sin\theta\) give

\[
\sum_{n\ge1}\frac{w_P(n)}{n^2\binom{2n}{n}}
\left(H_{2n}+AH_n-\frac D{2n}\right)
=\int_0^{\alpha}P(\theta)L_{A,D}(\theta)\,d\theta,
\]

\[
L_{A,D}(\theta)=-(A+1)\log(1-2\sin\theta)
-A\log(1+2\sin\theta)+D\log(2\sin\theta).
\]

The logarithmic endpoint singularities are integrable. Repeated integration by parts in the Fourier expansion gives a finite combination of odd zeta values once the even sine coefficients have canceled.

For \((r,s)=(2,3)\), the software reproduces \(A=296\), \(D=256\), and \(P(\theta)=\theta^5-\alpha^2\theta^3\). The resulting published specialization is

\[
\sum_{n\ge1}\frac{e_2(n)-\pi^2e_1(n)/180}
{n^2\binom{2n}{n}}
\left(H_{2n}+296H_n-\frac{128}{n}\right)
=\frac{61\pi^4\zeta(3)}{3645}
-\frac{20153\pi^2\zeta(5)}{9720}
+\frac{24563\zeta(7)}{1296}.
\]

Each finite coefficient, endpoint derivative, and multiplier is retained in the computation receipt. The current implementation supports every pair \(1\le r<s\le16\), giving 120 pairs. The theorem covers arbitrary fixed pairs; that theorem and this finite execution range are different statements. Its classification concerns the specified polynomial cancellation mechanism and does not classify all inverse-binomial or odd-zeta identities.



## Raghava: the complete generating families

The finite selected-order construction sits inside two complete generating families. The present engine reproduces the source formulas with exact rational coordinates and recovers the earlier identities as combinations of those generators. The all-order analytic input is Raghava's revised arcsine and hypergeometric paper; the order-64 software guard retains 130 complete family records through weight 131.

### Common harmonic coordinates and normalization

Define the finite reciprocal-square factors by

$$\prod_{k=1}^{n-1}(1+z/k^2)=\sum_{r\ge0}e_r(n)z^r.$$

Thus $e_0(n)=1$, and descending updates $e_r(n+1)=e_r(n)+e_{r-1}(n)/n^2$ compute the finite factors without special-function dependencies. Let $\lambda_k$ be the rational Taylor coefficients of $y/\sinh y$. Multiplication by the series for $\sinh y/y$ gives

$$\lambda_0=1,\qquad\lambda_m=-\sum_{h=1}^m\frac{\lambda_{m-h}}{(2h+1)!}.$$

The first values are $1,-1/6,7/360,-31/15120$. They also equal the derivatives at zero of the odd Lidstone polynomials: their generating function is $\sinh(vy)/\sinh y$. This explains why the older interpolation construction and the complete generating construction share the same normalization.

Set

$$F_m(n)=\sum_{r=0}^m\lambda_{m-r}(\pi/3)^{2m-2r}e_r(n),\qquad b_m=2^{2m+1}.$$

The complete second and supplementary families are

$$S_m=\sum_{n\ge1}\frac{F_m(n)(H_{2n}+b_mH_n)}{n^2\binom{2n}{n}},$$

$$B_m=\sum_{n\ge1}\frac{F_m(n)((1+b_m^{-1})H_n-1/(2n))}{n^2\binom{2n}{n}}.$$

These sums converge absolutely for every fixed nonnegative integer $m$. The implementation permits $0\le m\le64$, hence weights through $131$. This finite guard controls coefficient growth and does not assert a final mathematical order.

### Explicit complete coefficient formulas

For $A=4^k$, define

\[
\begin{aligned}
C_{k,j}={}&-\frac1{72\,36^j}+\frac{1-A}{18\,9^j}
+\frac1{8\,4^j}+\frac{A-1}{2}\\
&+\frac{A(6-A)}{9(2-A)}(4/9)^j
+\frac{A(3A-2)}{2-A}4^j.
\end{aligned}
\]

For $T=A/(2-A)$, define

\[
\begin{aligned}
D_{k,j}={}&\frac{T+1}{9\,9^j}+\frac{2T+3-4/A}{8\,4^j}
+\frac{4/A-1}{72\,36^j}\\
&+\frac1{8A\,16^j}-\frac1{72A\,144^j}.
\end{aligned}
\]

The exact scalar values are

$$S_m=\sum_{j=0}^m(-1)^j\lambda_{m-j}(\pi/3)^{2m-2j}C_{m-j,j}\zeta(2j+3),$$

$$B_m=\sum_{j=0}^m(-1)^j\lambda_{m-j}(\pi/3)^{2m-2j}D_{m-j,j}\zeta(2j+3).$$

For example, $S_0=5\zeta(3)/3$, $B_0=\zeta(3)/2$,

$$S_1=\frac{19}{54}\pi^2\zeta(3)-\frac{77}{18}\zeta(5),\qquad B_1=\frac1{162}\pi^2\zeta(3)-\frac7{108}\zeta(5).$$

The supplementary multiplier is independently tested by convolving the sine-normalization and cosine Taylor series, including the half-angle relation. This test checks a second construction of the coefficients rather than replaying the multiplier formula.

### Generators and the six-resolvent identity

The entire generators are

$$U_j(x)=\sum_{n\ge1}\frac{H_{jn}}{n^2\binom{2n}{n}}\prod_{k<n}(1+x^2/k^2),\qquad j=1,2.$$

Write $Z(x)=\sum_{k\ge1}1/[k(k^2+x^2)]$ and $c=\cosh(\pi x/3)$. Raghava's master relation is

\[
\begin{aligned}
4U_1(2x)+2cU_2(x)={}&-\frac{c}{36}Z(x/6)
+\frac{c-1}{9}Z(x/3)+\frac c4Z(x/2)\\
&+(1-c)Z(x)+\frac{8c^2+2}{9}Z(2x/3)
+(8c^2-6)Z(2x).
\end{aligned}
\]

Near zero, $Z(x)=\sum_{j\ge0}(-1)^j\zeta(2j+3)x^{2j}$. The master therefore turns six rational argument scales into all the exact coefficients above. The normalizing factor $a(x)=(\pi x/3)/\sinh(\pi x/3)$ obeys $a(2x)c=a(x)$, and the normalized left side has coefficients $S_m$. The implementation encloses left and right independently in both hyperbolic and oscillatory conventions. Its master evaluator retains $|x|<1/2$, the common disk of all resolvent expansions. It never evaluates an individually singular resolvent and asserts that the finite result follows from cancellation.

The direct $U_j$ evaluator instead accepts real rational $|x|\le16$. It computes the original finite products. In the oscillatory convention it evaluates $U_j(ix)$ and correctly terminates when $x$ is a nonzero integer; for instance, $U_1(i)=1/2$ and $U_2(i)=3/4$. The normalization evaluator permits hyperbolic $|x|\le32$ and sine $|x|<3$, stopping before the latter's first pole. These domains are evaluator budgets; the entire functions themselves are not confined to them.

### Formal normal forms and preservation of the earlier 120 identities

At fixed weight $2M+3$, use the formal coordinate vectors $\pi^{2(M-j)}\zeta(2j+3)$. The vectors $\pi^{2(M-k)}S_k$ give a triangular basis because their diagonal is

$$(-1)^k\frac{72\,144^k+40\,16^k+9\,9^k-1}{72\,36^k}\ne0.$$

`canonical_second_basis` performs exact back substitution and reconstructs the original coordinate vector. It accepts arbitrary homogeneous rational input through $M=32$. Uniqueness is a formal statement about coefficient vectors; it does not assume algebraic or numerical independence of odd zeta values. Equal vectors prove an expression identity, while unequal vectors do not prove that the resulting real numbers are unequal.

For the two-selected-order construction, put $1\le r<s$, $D=b_{r-1}b_{s-1}$, $A=D+b_{r-1}+b_{s-1}$, and

$$\kappa=(\pi/3)^{2s-2r}\lambda_{s-1}/\lambda_{r-1}.$$

Its value is exactly

$$S_{s-1}+DB_{s-1}-\kappa(S_{r-1}+DB_{r-1}).$$

This equality holds before summation: each relevant $b$ satisfies $b+D(1+b^{-1})=A$. All 120 retained pairs $1\le r<s\le16$ are checked against the earlier independent Lidstone/Fourier implementation, matching the harmonic polynomials, harmonic insertion constants, and complete zeta evaluations.

### Rational enclosures and global bounds

`family_partial` computes the original inverse-binomial summands as a polynomial in $\pi^2$ and bounds its entire signed omitted tail. It uses $e_r(n)\le2^r/r!$, $H_{jn}\le jn$, $\binom{2n}{n}\ge4^n/(2n+1)$, and $\pi<22/7$. `family_interval` independently evaluates the finite zeta formula with rational Machin bounds for $\pi$ and positive Euler-transformed eta bounds for $\zeta$. If $K$ Euler terms are retained, the omitted eta tail is at most $2^{-K}$. Reversing the finite transform reduces its evaluation to $K$ weighted rational Dirichlet terms instead of a quadratic array of large rational differences. The two evaluations have no shared fitted decimal values.

For direct generator evaluation, the absolute product bound $\prod_{k<n}|1\pm x^2/k^2|\le3^{\lceil2x^2\rceil}$ gives an omitted tail at most $j3^{\lceil2x^2\rceil}4^{-N}$. Hyperbolic summands are nonnegative and give a one-sided enclosure; oscillatory summands use the absolute two-sided bound.

For $t\ge0$, define $V(t)=a(\sqrt t)U_2(\sqrt t)+2a(2\sqrt t)U_1(2\sqrt t)$. The cited complete-monotonicity theorem gives $(-1)^rV^{(r)}(t)>0$ and hence $(-1)^mS_m>0$. Taylor's integral remainder gives the global inequalities

$$\sum_{m=0}^{2N+1}S_mt^m<V(t)<\sum_{m=0}^{2N}S_mt^m\qquad(t>0).$$

Their validity does not require convergence of the infinite Taylor series at the chosen $t$. `global_taylor_bounds` independently encloses the coefficients first and applies these polynomial inequalities for any nonnegative rational $t$ within precision and degree budgets. `global_generator_interval` directly evaluates $V(t)$ by squared-parameter arithmetic for $0\le t\le64$, avoiding a numerical square root. Tests compare the independent bounds at $t=1,4,9$, beyond the initial local resolvent disk.

The exact arithmetic checks establish the implemented finite computations. The analytic theorems remain supported by the cited paper and the mathematical arguments above; the recovered engine does not claim Lean-kernel verification or a new independent hypergeometric summation principle.



## Periodic Dirichlet families and exact character spectra

The same finite-period viewpoint works beyond additive phase sums. Rational coefficient tables give rational Mellin kernels; multiplicative characters give exact cyclotomic coefficients, conductor descent, Euler factors, and independent Gauss-sum evaluations. Opposite-parity constants remain formal instead of being fitted to unsupported powers of pi.

### One finite table, three analytic descriptions

Let a rational table be indexed from one through its length:

\[
c=(c_1,\ldots,c_N),\qquad c_{n+N}=c_n,
\qquad D_c(s)=\sum_{n\geq1}\frac{c_n}{n^s}.
\]

The convention matters: the last entry is the value at residue zero.  The
constructor is `PeriodicDirichlet((c1, ..., cN))`; `coefficient(n)` follows
the same convention even at zero and negative integer arguments.  Exact
integers, fractions, and rational strings are accepted.  Floats and booleans
are rejected, so an accidental decimal cannot silently enter a certificate.

Summing a geometric series gives a rational kernel:

\[
K_c(x)=\frac{\sum_{a=1}^{N}c_a x^{a-1}}{1-x^N},
\qquad
D_c(s)=\frac1{\Gamma(s)}\int_0^1
(-\log x)^{s-1}K_c(x)\,dx.
\]

The common absolute convergence region is \(\operatorname{Re}s>1\).
If \(\sum c_a=0\), the numerator also vanishes at one and the apparent pole
in the kernel is removable.  Summation by parts then gives convergence of
the ordinary Dirichlet series for \(\operatorname{Re}s>0\), and the Mellin
integral has the same larger domain.  The removable endpoint value is

\[
K_c(1)=-\frac1N\sum_{a=1}^{N}(a-1)c_a.
\]

The coefficient mean \(\mu=N^{-1}\sum c_a\) is the residue at the possible
pole of the analytic continuation at \(s=1\).  A zero-mean table yields an
entire continuation.  These continuation claims do not turn divergent
ordinary series into convergent ones.  The API reports the ordinary,
absolute, and continued domains separately.

Splitting the sum into residue classes gives

\[
D_c(s)=N^{-s}\sum_{a=1}^{N}c_a\zeta(s,a/N).
\]

The corresponding generating family, initially for \(|z|<1\), is

\[
\sum_{n\geq1}\frac{c_nz^n}{n^s}
=N^{-s}\sum_{a=1}^{N}c_a z^a
\Phi(z^N,s,a/N).
\]

`hurwitz_reduction()` and `lerch_reduction()` return these complete symbolic
reductions, including their scale, residue arguments, and domains.  They do
not claim that an arbitrary Hurwitz or Lerch value is elementary.

### Exact Fourier transport

With \(\zeta_N=e^{2\pi i/N}\), put

\[
b_h=\frac1N\sum_{a=1}^{N}c_a\zeta_N^{-ha},
\qquad 0\leq h<N.
\]

Finite Fourier inversion is exact:

\[
c_n=\sum_{h=0}^{N-1}b_h\zeta_N^{hn},
\qquad
D_c(s)=\sum_{h=0}^{N-1}b_h
\operatorname{Li}_s(\zeta_N^h).
\]

The polylog identity is asserted on the safe common region
\(\operatorname{Re}s>1\).  The code keeps the coefficient \(b_h\) as a
reduced element of \(\mathbb Q[z]/(\Phi_N(z))\), with the specified complex
embedding \(z=e^{2\pi i/N}\).  A packet records the ambient root order,
the cyclotomic polynomial, and the reduced rational coefficients.  The
ambient order need not be the smallest possible field of definition.

`CyclotomicNumber` supports exact sums, products, inverses, integer powers,
conjugation, and changes of ambient field.  For fields of orders \(M\)
and \(N\), arithmetic is performed in the common field of order
\(\operatorname{lcm}(M,N)\).  The embedding sends
\(\zeta_N\) to \(\zeta_L^{L/N}\), so it preserves the specified complex
value.  This reuses the repository's polynomial quotient machinery rather
than relying on rounded comparisons of complex numbers.

### Parity gives algebraic multiples of powers of pi

For a positive integer \(k\), suppose
\(c_{-a}=(-1)^k c_a\).  The two halves of the bilateral Dirichlet sum then
agree.  Combining its Bernoulli Fourier expansion with the exact DFT gives

\[
\boxed{
\frac{D_c(k)}{\pi^k}
=-\frac{(2i)^k}{2k!}
\sum_{h=0}^{N-1}b_h B_k(h/N).
}
\]

All quantities on the right belong to a finite cyclotomic field and are
computed exactly.  The implementation uses an ambient order divisible by
four so that \(i\) has an exact representation.  For weight one, matching
odd parity forces zero mean, and therefore the potentially exceptional
zero Fourier mode vanishes.

This is a general algebraic coefficient, not necessarily a rational one.
For the odd residue pair modulo eight,

\[
\sum_{m\geq0}\left(\frac1{(8m+1)^3}-\frac1{(8m+7)^3}\right)
=\frac{4+3\sqrt2}{256}\pi^3.
\]

The exact coefficient is stored as
\(1/64+3(\zeta_8-\zeta_8^3)/256\), using
\(\sqrt2=\zeta_8+\zeta_8^{-1}\).  Squaring that last algebraic number
returns two by exact polynomial reduction.  `residue_pair(8, 1)` creates
the coefficient table directly.

Opposite parity is deliberately retained as a formal period.  For example,
the beta character modulo four has table \((0,1,0,-1)\) when indexed from
zero, or \((1,0,-1,0)\) under the periodic-series convention.  Its odd
values give

\[
\beta(1)=\frac\pi4,\qquad
\beta(3)=\frac{\pi^3}{32},\qquad
\beta(5)=\frac{5\pi^5}{1536}.
\]

Its even value \(\beta(2)\), Catalan's constant, remains formal.  The API
does not report an invented algebraic multiple of \(\pi^2\), nor does a
formal result assert impossibility of every other kind of expression.

### Full characters, primitive reduction, and Gauss sums

`DirichletCharacter(q, order, exponents)` takes a full table indexed from
zero.  `None` records zero at a nonunit; an integer \(e\) records
\(e^{2\pi i e/\mathrm{order}}\) at a unit.  The constructor checks every
unit pair for multiplicativity and requires the correct support and value
at the identity.  It removes redundant common factors from the root order.
The quartic example modulo five is
`DirichletCharacter(5, 4, (None, 0, 1, 3, 2))`, with \(\chi(2)=i\).
Thus complex characters are supported in full, rather than being replaced
by just the real or quadratic cases.

The conductor is found by testing every divisor \(d\mid q\): the values on
units must depend only on the residue modulo \(d\).  Reduction to the
least such divisor produces the primitive character \(\chi^*\).  Induction
to a larger modulus restores the zeros at the new nonunits.  The Euler
relation is

\[
L(s,\chi)=L(s,\chi^*)
\prod_{p\mid q}\left(1-\frac{\chi^*(p)}{p^s}\right).
\]

Factors at primes already dividing the primitive conductor are one and
are omitted from the stored nontrivial list.  For example, inducing the
beta character from four to twelve removes the multiples of three and
multiplies its cubic value by \(1+3^{-3}\).  The result is
\(L(3,\chi_{12})=7\pi^3/216\).

Gauss sums are computed from the actual finite table:

\[
G_a(\chi)=\sum_{r\bmod q}\chi(r)\zeta_q^{ar}.
\]

The identity
\(G_a(\chi)=\overline{\chi(a)}G_1(\chi)\) holds for every multiplier when
the character is primitive, and for unit multipliers even when it is
imprimitive.  Extending that identity to nonunits of an imprimitive
character would be an error.  The principal character modulo four supplies
an exact counterexample: \(G_1=0\), while \(G_2=-2\).  The implementation
reports the nonunit imprimitive case as inapplicable instead of converting
it into a false equality.

For an independent check on the DFT evaluation, the engine also computes
generalized Bernoulli numbers and the primitive Bernoulli-Gauss formula,
then applies the Euler factors.  Matching-parity results obtained by these
two routes must agree exactly.  Generalized Bernoulli numbers also give
the continued values
\(L(-m,\chi)=-B_{m+1,\chi}/(m+1)\); the method name and note explicitly
identify these as analytic continuation rather than ordinary sums.

`all_characters(q)` enumerates the complete finite character group.  It
extends a character on a subgroup \(H\) through one new generator \(g\).
If \(g^t\) first returns to \(H\), its possible exponents satisfy the exact
finite congruence \(tx=\chi(g^t)\).  Repeating these extensions gives all
\(\varphi(q)\) characters, including noncyclic unit groups.  An explicit
modulus budget prevents an accidental unbounded enumeration.

### Error bounds and computational scope

For a zero-mean rational table, let
\(B_M=\max_{1\leq j\leq N}|\sum_{n=M+1}^{M+j}c_n|\).  Discrete summation
by parts gives, for every positive integer \(k\),

\[
\left|D_c(k)-\sum_{n=1}^{M}\frac{c_n}{n^k}\right|
\leq\frac{B_M}{(M+1)^k}.
\]

This includes conditionally convergent weight-one sums.  A separate
absolute-series bound is available for every table at weights above one;
the engine returns the smaller valid bound.  The partial sum and radius
are rational numbers, so `enclosure()` returns an exact rational interval.

For a complex nonprincipal character, a partial sum is a cyclotomic number
and the tail is enclosed in a complex disk of rational radius.  A prefix
is bounded both by the number of unit values already included and by the
number left in the period.  This conservative triangle bound uses neither
rounded complex magnitudes nor an ordering of a complex number field.

Fourteen tests cover exact field embeddings, DFT inversion for every
period through twelve, rational kernel endpoint cancellation, finite
residue-class grouping, known beta values, the radical coefficient above,
weight-one tail enclosures, complex characters, conductor and Euler
reduction, primitive and imprimitive Gauss scope, analytic continuation,
and invalid-input rejection.  All character tables through modulus sixteen
are enumerated, and the DFT and independent primitive Euler evaluations
are compared at matching weights one through four.  These checks establish
the executable exact arithmetic used in the retained experiments; they
are not a claim of formal kernel verification of this module.

The classical analytic formulas can be checked against the primary NIST
references [DLMF 25.15](https://dlmf.nist.gov/25.15),
[DLMF 25.12](https://dlmf.nist.gov/25.12), and
[DLMF 25.14](https://dlmf.nist.gov/25.14).



## Actual linear descent and the conductor colimit

This part supplies ordinary linear objects and actual matrix morphisms. It is stronger than drawing arrows between dimension labels: the maps, finite universal property, and induction-restriction adjunction are explicitly defined and checked. Its rational phase grading is a split spectral model; the rational forms of genuine cyclic representations retain their separate Galois conditions.

### Canonical phase classes and their colimit

Write a rational phase as \(q\in\mathbb Q/\mathbb Z\), represented by its unique rational number in \([0,1)\). A `PhaseClass` is a finite sum

\[
 A=\sum_q a_q[q],\qquad a_q\in\mathbb Q.
\]

Equal phases merge and zero coefficients disappear. Addition is termwise, the product is convolution \([q][r]=[q+r]\), and duality sends \([q]\) to \([-q]\). The resulting algebra is the ordinary finite-support group algebra \(\mathbb Q[\mathbb Q/\mathbb Z]\). Its conductor is the least common multiple of the denominators of the phases with nonzero coefficient. The zero class has conductor one.

At stage \(N\), let \(A_N=\mathbb Q[C_N]\), with phase basis \([k/N]\). When \(N\mid M\), the connecting injection is

\[
 \iota_{N,M}[k/N]=[(kM/N)/M].
\]

It preserves the rational phase. This is the phase-class operation associated with inflation of cyclic representations through \(C_M\twoheadrightarrow C_N\). It is not induction. Every finite phase class lies at a finite stage, and two representatives define the same class exactly when they agree after passage to the least common multiple of their conductors. `colimit_witness` checks this finite common-stage equality explicitly.

These two observations prove the ordinary directed-colimit universal property. Given compatible linear maps \(f_N:A_N\to W\), define \(f(A)=f_N(A_N)\) at any stage containing the support of \(A\). Any two such stages inject into a common stage, so compatibility makes this well defined. Linearity follows by moving finitely many inputs to a common stage. Uniqueness follows because every phase basis vector appears at a finite stage. If every \(f_N\) is a unital algebra map, the same argument proves the algebra-colimit statement.

The executable `FiniteLinearCocone` handles supplied finite families of rational-valued functionals. `StageFunctional(N, values)` specifies one value for every phase basis vector at stage \(N\). Two stages intersect in the phase basis at their greatest common divisor; agreement there is precisely the compatibility condition. The finite cocone descends uniquely to the linear span of the supplied phase bases. It rejects evaluation at an uncovered phase. For example, stages two and three cover the four phases \(0,1/2,1/3,2/3\), not all six phases at stage six. Choosing a common conductor cannot invent the missing functional values at \(1/6\) and \(5/6\).

### Actual linear objects and morphisms

A `PhaseSpace` is a finite rational vector space with a rational phase grading,

\[
 V=\bigoplus_{q\in\mathbb Q/\mathbb Z}V_q,
 \qquad \dim_{\mathbb Q}V_q\in\mathbb Z_{\ge0}.
\]

Each graded piece has a fixed ordered basis. A `PhaseLinearMap` is an actual collection of rational matrix blocks \(f_q:V_q\to W_q\). The constructor checks every matrix dimension and forbids blocks between distinct phases. Identity maps are identity matrices. Composition is matrix multiplication. Direct sum uses block diagonal matrices, tensor product uses the graded Kronecker construction, and duality reverses the arrow, transposes each matrix, and negates its phase. When distinct phase pairs have the same tensor-product grade, the implementation preserves their separate basis positions; it does not merge different vectors simply because their grades coincide.

The underlying rational-vector-space functor is faithful: assembling the blocks into an ordinary matrix retains every block entry. It is generally not full, since an arbitrary underlying linear map may mix distinct phases. Passing from `PhaseSpace` to its `PhaseClass` records dimensions and forgets morphisms; this decategorification is not a faithful functor. Two unrelated maps can have the same source and target class.

This is a split rational spectral model. After complexification, one can attach the finite-order operator acting by \(e^{2\pi iq}\) on the grade \(q\). A phase \(1/3\) does not mean that multiplication by a primitive cube root is already a rational scalar on a one-dimensional ordinary rational representation. Rational forms of actual cyclic representations impose additional Galois conditions. The distinction prevents the convenient rational block model from being mistaken for every representation category over \(\mathbb Q\).

The finite categories embed fully faithfully as the conductor grows, because phase-preserving inflation introduces no new grades between old objects and no new matrix blocks. Every finite object and every finite collection of its matrix morphisms therefore occurs at a common finite stage. This explains the concrete directed-union category used here. It supplies no higher cells or higher-categorical universal property beyond this ordinary construction.

### Induction, inflation, and Frobenius reciprocity

Fix \(n\mid N\), with \(d=N/n\), and use the subgroup \(C_n\subset C_N\) generated by \(g_N^d\). A character at grade \(a/n\) has the following three distinct operations:

\[
 \operatorname{Inf}_{C_n}^{C_N}[a/n]=[a/n],
 \qquad
 \operatorname{Ind}_{C_n}^{C_N}[a/n]
   =\sum_{j=0}^{d-1}[(a+nj)/N],
\]

\[
 \operatorname{Res}_{C_n}^{C_N}[b/N]=[b/n].
\]

Inflation preserves dimension and the complex eigenphase. Induction multiplies dimension by \(d\). Restriction can merge phase grades and therefore carries a direct sum of the original basis blocks into a larger multiplicity space. The source provides these operations on both objects and actual matrices.

Frobenius reciprocity is implemented as an explicit linear bijection

\[
 \operatorname{Hom}_{C_N}(\operatorname{Ind}V,W)
 \;\cong\;
 \operatorname{Hom}_{C_n}(V,\operatorname{Res}W).
\]

For fixed \(a\), write the left-hand map in blocks \(F_b:V_{a/n}\to W_{b/N}\), where \(b\equiv a\pmod n\). The forward map stacks the rows of the \(F_b\) in the fixed increasing-phase basis order. The inverse splits the stacked rows back into the original blocks. These operations are mutually inverse without an approximation or a dimension-only argument. The tests also check naturality under actual precomposition and postcomposition, including non-diagonal matrix blocks and merged restriction grades.

For the artifact conductors,

\[
 n=1680,\qquad N=443520=264\cdot1680,
\]

inflating one character gives one character, while inducing it gives 264 branches. A primitive base character has 240 primitive branches at conductor 443520 and 24 branches at conductor 40320. The number 384 is \(\varphi(1680)\), the degree of the base cyclotomic field; it is not the number of branches over one character. Thus 384, 264, and 240 are different quantities with exact relationships, rather than interchangeable categorical dimensions.

Inducing the entire primitive base spectrum gives dimension \(384\cdot264=101376\). Its cyclotomic polynomial factorization is

\[
 \boxed{\Phi_{1680}(x^{264})
   =\Phi_{40320}(x)\,\Phi_{443520}(x)},
\]

\[
 101376=9216+92160,
 \qquad 9216=384\cdot24,
 \qquad 92160=384\cdot240.
\]

The proof is by root order. A primitive \(m\)-th root raised to the 264th power has order \(m/\gcd(m,264)\). Among the divisors of 443520, the condition that this order equal 1680 selects precisely 40320 and 443520. The roots of \(\Phi_{1680}(x^{264})\) are simple in characteristic zero, so the selected primitive-root sets give the polynomial identity. `induced_primitive_factorization` computes this root-order certificate and checks the exact degree sum; it does not pretend to expand and multiply degree-101376 dense polynomials.

### Full complex Mellin traces and exact recovery

For a finite phase class define

\[
 F_A(s)=\sum_q a_q\operatorname{Li}_s(e^{2\pi iq}),
 \qquad \Re s>1.
\]

Absolute convergence gives both its Dirichlet expansion and its Mellin integral:

\[
 F_A(s)=\sum_{m\ge1}\frac{t_A(m)}{m^s},
 \qquad t_A(m)=\sum_q a_qe^{2\pi imq},
\]

\[
 F_A(s)=\frac1{\Gamma(s)}\int_0^1
 (-\log x)^{s-1}
 \sum_q\frac{a_qe^{2\pi iq}}{1-xe^{2\pi iq}}\,dx.
\]

`cyclic_period_trace` retains this full complex family and supplies exact cyclotomic Dirichlet coefficients. At the phase one, the endpoint singularity still gives an integrable function for \(\Re s>1\). A symbolic weight is formal and carries this domain; exact numeric integer and rational weights must exceed one.

At conductor \(N\), the coefficients \(t_A(m)\) are periodic modulo \(N\). The entire phase class is recovered by the discrete Fourier inversion formula

\[
 a_{k/N}=\frac1N\sum_{r=0}^{N-1}t_A(r)e^{-2\pi ikr/N}.
\]

The source performs this inversion exactly in \(\mathbb Q[z]/\Phi_N(z)\), with conductor budget \(N\le64\). It retains all real and imaginary information through rational polynomial residues; no floating-point complex roots enter the calculation. The DFT conductor budget is an implementation bound, rather than a restriction on the mathematical statement.

The full Mellin family is injective. If \(F_A(s)=0\) for all real \(s>1\), uniqueness of its absolutely convergent Dirichlet series gives \(t_A(m)=0\) for every positive integer \(m\). To see uniqueness directly, choose the least index \(j\) with nonzero coefficient. Multiplying the series by \(j^s\) and letting real \(s\) tend to infinity leaves \(t_A(j)\); the bounded-coefficient tail tends to zero by dominated convergence. This contradicts the vanishing series. Periodicity now supplies all \(N\) Fourier coefficients, including index zero via index \(N\), and exact DFT inversion gives \(A=0\).

A single integral value does not have this injectivity. At weight two, \(\operatorname{Li}_2(1)+2\operatorname{Li}_2(-1)=0\), although the corresponding phase class \([0]+2[1/2]\) is nonzero. Taking real parts also loses orientation: \([q]\) and \([-q]\) always have identical real Mellin traces. The implementation and note distinguish the full complex family, one selected weight, and the symmetrized real trace.

### Reproduction of this component

Run the focused `test_phase_descent.py` module using the unittest invocation given in the final reproduction section. The checks include canonical conductor equality, finite cocone overlap and uncovered-phase rejection, actual matrix identities and compositions, contravariant duality, direct sums, tensor bifunctoriality with colliding grades, induction versus inflation, induction/restriction functoriality, explicit Frobenius inverse maps and both naturality directions for 28 cyclic inclusions, exact DFT inversion across 37 conductors up to 64, full-complex orientation, and the artifact-conductor root-order factorization.

`descent_receipt()` returns a compact JSON-safe summary for the live research feed. Its claim is an ordinary exact finite linear construction and its proved conductor descent. The relation to higher-category drawings remains a precisely stated classical realization; the drawings alone do not supply associators, higher morphisms, coherence laws, or an E8 representation-theoretic identification.



## The actual E8 adjoint Coxeter lift

The earlier standalone root-permutation-plus-Cartan calculation supplied a correct cyclic model but left a specific question: do the root-space signs of an actual E8 inner automorphism give that same spectrum? The following explicit Lie bracket, exponentials, and signed-orbit computation settle that question for the fixed simple system and Coxeter ordering. The identification is established through brackets and operators, rather than through the number 248.

### Roots, Cartan spectrum, and the artifact circle

In Euclidean eight-space the actual E8 roots are the 112 vectors $\pm e_i\pm e_j$, $i<j$, together with the 128 vectors whose coordinates are $\pm1/2$ with an even number of minus signs. Their squared lengths are two. The implementation doubles coordinates so that every root is an integer vector of squared norm eight. Exact simple reflections preserve the complete root set, and the fixed simple-root system gives 120 positive roots and highest-root height 29.

The Coxeter matrix on the eight-dimensional Cartan subalgebra has order 30 and characteristic polynomial

\[
\Phi_{30}(X)=X^8+X^7-X^5-X^4-X^3+X+1.
\]

Its exponents are $1,7,11,13,17,19,23,29$, the units modulo 30. The map from the artifact circle is the actual power identity $q^{56}=\zeta_{30}$. Reduction of all 384 primitive exponents modulo 1680 to exponents modulo 30 gives 48 copies of each of these eight phases. Equivalently, restriction of the rational cyclotomic module $\mathbb Q(\zeta_{1680})$ to its $\mathbb Q(\zeta_{30})$ action consists of 48 copies of the eight-dimensional rational Coxeter module. This is a precise spectral relationship. It does not identify the separate 240-element conductor fiber with the E8 roots.

### The cocycle and the Lie algebra

Express roots in the fixed simple-root basis as integer vectors $a=(a_1,\ldots,a_8)$. Let $A$ be its symmetric Cartan matrix. Set

$$E(a,b)=\sum_i a_i b_i+\sum_{i>j}a_i A_{ij}b_j,
\qquad \epsilon(a,b)=(-1)^{E(a,b)}.$$

Bilinearity of $E$ modulo two gives bimultiplicativity and the cocycle identity

$$\epsilon(a,b)\epsilon(a+b,c)=\epsilon(b,c)\epsilon(a,b+c).$$

Moreover $E(a,b)+E(b,a)\equiv a^TAb\pmod2$, while
$E(a,a)\equiv a^TAa/2\pmod2$. Thus

$$\epsilon(a,b)\epsilon(b,a)=(-1)^{(a,b)},\qquad
\epsilon(a,a)=(-1)^{(a,a)/2}.$$

Every root has squared length two, so its diagonal cocycle sign is $-1$. On the basis $h_1,\ldots,h_8$ and $e_\alpha$ for all 240 roots, define

$$[h_i,h_j]=0,\qquad [h_i,e_\alpha]=(\alpha_i,\alpha)e_\alpha,$$

$$[e_\alpha,e_{-\alpha}]=-h_\alpha,
\qquad h_\alpha=\sum_i a_i h_i,$$

$$[e_\alpha,e_\beta]=\epsilon(\alpha,\beta)e_{\alpha+\beta}
\quad\text{if }\alpha+\beta\text{ is a root}.$$

All other root brackets vanish. This is the classical simply-laced Frenkel-Kac construction in the negative opposite-root normalization. Geck's Theorem 3.3 and Example 3.4 describe this construction; the cocycle here is chosen explicitly instead of importing a sign table. The root decomposition and connected E8 Cartan matrix identify the resulting complex Lie algebra as E8.

In particular, the normalized simple triples are

$$E_i=e_{\alpha_i},\quad F_i=-e_{-\alpha_i},\quad H_i=h_i,$$

$$[E_i,F_i]=H_i,\qquad [H_i,E_i]=2E_i,\qquad [H_i,F_i]=-2F_i.$$

The sign of $F_i$ matters. A lift built with the wrong middle exponential would not be the Weyl lift claimed below.

### Finite exponentials and Tits lifts

For every root, $D_\alpha=\operatorname{ad}(e_\alpha)$ satisfies $D_\alpha^3=0$ on this Lie algebra. The executable function checks every third commutator before using

$$\exp(tD_\alpha)=I+tD_\alpha+\frac{t^2}{2}D_\alpha^2.$$

For $t=\pm1$ all resulting entries are integers. The tests construct the exponentials of all 240 roots, verify integrality, and verify that the positive and negative exponentials are inverse operators. They also check an exact half-parameter composition. The simple Tits operator is

$$n_i=\exp(\operatorname{ad}E_i)\exp(-\operatorname{ad}F_i)
\exp(\operatorname{ad}E_i)
=\exp(\operatorname{ad}e_{\alpha_i})
\exp(\operatorname{ad}e_{-\alpha_i})
\exp(\operatorname{ad}e_{\alpha_i}).$$

It is an actual inner automorphism, as a product of exponentials of inner derivations. Its Cartan action is the corresponding simple reflection; on a root vector its image is a signed reflected root vector. Each of the eight simple lifts has 56 negative root images. The arithmetic checks also verify, separately from this theoretical explanation, bracket preservation for every basis pair under each lift.

The lifts have the Tits square law

$$n_i^2(e_\alpha)=(-1)^{(\alpha_i,\alpha)}e_\alpha,
\qquad n_i^2(h_j)=h_j.$$

All 1,984 basis instances of these eight square laws and all 28 pairwise commutation or length-three braid relations are checked exactly on the 248-dimensional space.

### The signed Coxeter orbits

Use the same ordering as the geometric root action:

$$N=n_8\cdots n_1,$$

where $n_1$ acts first. Its restriction to the Cartan is the existing eight-dimensional Coxeter matrix with characteristic polynomial

$$\Phi_{30}(X)=X^8+X^7-X^5-X^4-X^3+X+1.$$

The actual lifted action has 128 negative root images. The deterministic signed root-space orbit data are:

\Needspace{14\baselineskip}

| Orbit | Length | Negative edge signs | Product of signs |
|---|---:|---:|---:|
| First | 30 | 20 | +1 |
| Second | 30 | 20 | +1 |
| Third | 30 | 12 | +1 |
| Fourth | 30 | 12 | +1 |
| Fifth | 30 | 12 | +1 |
| Sixth | 30 | 20 | +1 |
| Seventh | 30 | 12 | +1 |
| Eighth | 30 | 20 | +1 |

To remove signs by a coordinate change, write $Ne_j=s_j e_{j+1}$ around an orbit. Choose $g_0=1$ and set $g_{j+1}=g_j s_j$. Each product-one condition makes this choice periodic, and the basis $f_j=g_j e_j$ then satisfies $Nf_j=f_{j+1}$. The receipt retains all 240 gauge signs, of which 124 are negative with the fixed seeds. The software checks the intertwining equality for every root vector, not just the product around each cycle.

This gauge is an ordinary change of linear coordinates. It is not claimed to preserve the old displayed structure constants as a separate Lie automorphism. The Lie action was already constructed from exponentials before this coordinate change was used to read its spectrum.

Consequently the actual adjoint spectrum consists of eight copies of every 30th root plus one copy of each primitive 30th root. It follows that

$$\boxed{\det(XI-N)=(X^{30}-1)^8\Phi_{30}(X).}$$

Every primitive 30th-root eigenvalue has multiplicity nine, and every other 30th-root eigenvalue has multiplicity eight. The program separately verifies $N^{30}=I$ and rules out each proper divisor of 30 as its order. Adams-He, Proposition 5.1.1, provides the independent group-theoretic order explanation: a Coxeter lift to the Coxeter number gives the principal central involution, which is trivial for E8.

There is an independent height-spectrum comparison. Count the simple-root heights of all 240 actual roots modulo 30 and add eight Cartan eigenvalues of phase zero. Every one of the resulting 30 multiplicities equals the lifted spectrum above. In the root-length-two normalization, half the positive-root sum has squared length $\|\rho\|^2=620$; the 120 positive-root heights sum to 1240 and their squares sum to 18600. These three values are recomputed from coordinates, and do not come from the signed cycles.

### The adjoint integral and its nonzero logarithmic derivative

For $\Re s>1$, the actual adjoint polylogarithm trace is the absolutely convergent series

$$Z(s)=\sum_{m\ge1}\frac{\operatorname{Tr}(N^m)}{m^s}.$$

The traces are

$$\operatorname{Tr}(N^m)=c_{30}(m)+240\,\mathbf1_{30\mid m},$$

where $c_{30}$ is the Ramanujan sum. The primitive phase trace contributes
$\zeta(s)\prod_{p\in\{2,3,5\}}(p^{1-s}-1)$, and the eight regular cycles contribute $8\,30^{1-s}\zeta(s)$. Therefore

$$\boxed{Z(s)=\zeta(s)30^{1-s}
\left[8-(2^{s-1}-1)(3^{s-1}-1)(5^{s-1}-1)\right].}$$

This now has an actual adjoint interpretation, closing the sign condition retained by `e8_periods.py`'s deliberately weaker standalone model. The older module remains valid without importing this larger Lie construction.

The corresponding rational kernel is

$$K(x)=\frac{240x^{29}}{1-x^{30}}-\frac{\Phi_{30}'(x)}{\Phi_{30}(x)},$$

and

$$Z(s)=\frac1{\Gamma(s)}\int_0^1(-\log x)^{s-1}K(x)\,dx,
\qquad \Re s>1.$$

For real $s>1$, the product $(2^{s-1}-1)(3^{s-1}-1)(5^{s-1}-1)$ is strictly increasing from zero to infinity. At $s=2$ it equals eight. Thus $Z$ has exactly one real zero on this interval, at two, and

$$\boxed{\int_0^1(-\log x)K(x)\,dx=0.}$$

Differentiating the normalized Mellin formula at two is legitimate by absolute domination on a smaller closed half-plane. Since $Z(2)=0$, the derivative of $1/\Gamma(s)$ makes no contribution. Differentiating the explicit product gives

$$\boxed{\int_0^1(-\log x)\log(-\log x)K(x)\,dx
=-\frac{\pi^2}{180}(16\log2+12\log3+10\log5).}$$

The exact rational coefficients of $\pi^2\log2$, $\pi^2\log3$, and $\pi^2\log5$ are respectively $-4/45$, $-1/15$, and $-1/18$. A zero observation at weight two therefore does not make the spectral response or the Lie action zero.

### Reproduction of the actual lift

Run `PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_e8_lift.py -v` for the eight tests. Run `PYTHONPATH=python python3 -m perfectpower.e8_lift --exhaustive` to recompute the complete JSON receipt. Without `--exhaustive`, the receipt explicitly marks the large root-pair, Jacobi, and lift-bracket counts as unexecuted, while still recomputing the lifts, signed cycles, gauge, Tits relations, traces, height comparison, and order.

The full checks comprise 248 alternating basis values, 30,628 skew-symmetry basis pairs, all 57,600 ordered root-pair cocycle signs, all 2,511,496 distinct unordered basis triples for Jacobi, and all 245,024 simple-lift bracket-preservation pairs. Alternation and trilinearity extend the checked Jacobi identities to repeated indices and all vectors. The full bracket-preservation checks include zeros. The tests additionally check all 240 root exponentials, all eight simple reflection actions, eight normalized $\mathfrak{sl}_2$ triples, the exact Tits relations, and the actual Coxeter spectrum.

This resolves the actual E8 adjoint-lift condition for the stated spectral integrals. It does not identify the separate 240-dimensional field-conjugate fiber with the 240 E8 root spaces, provide the categorical trace 264, or prove unspecified higher-category claims in the motivating visualizations. Those require their own constructions. Classical provenance is retained and no historical novelty claim is made for the Lie construction or its integral specialization.

Sources: Meinolf Geck, [On Lusztig's canonical bases of simple Lie algebras](https://arxiv.org/html/2602.19632v1), Theorem 3.3 and Example 3.4; Jeffrey Adams and Xuhua He, [Lifting of elements of Weyl groups](https://arxiv.org/abs/1608.00510), Proposition 5.1.1. Root coordinates, Coxeter geometry, and analytic normalizations are documented separately in `e8_periods.py` and the integral monograph.



## Complete observations and minimal trace machines

The entire periodic trace is an observable object in its own right. Its exact rational kernel and minimal output machine retain every future trace while allowing substantial compression. The compression concerns the output behavior, and does not replace the underlying representation or Lie bracket.

Let a rational block \(c_1,\ldots,c_N\) extend periodically to positive
indices. Its reduced rational kernel is

\[
K_c(x)=\frac{c_1+c_2x+\cdots+c_Nx^{N-1}}{1-x^N},
\qquad
F_c(s)=\sum_{n\ge1}\frac{c_n}{n^s}
=\frac1{\Gamma(s)}\int_0^1(-\log x)^{s-1}K_c(x)\,dx.
\]

The last integral and series converge absolutely on \(\Re(s)>1\).
The reduced kernel, the entire future coefficient sequence, and the whole
Dirichlet function on this half-plane each determine the other two.
Matching one selected period value does not establish any of these equalities.

Kernel and sequence determine one another by uniqueness of power-series
coefficients. To prove uniqueness for the Dirichlet function, suppose the
difference of two bounded sequences first differs at index \(m\), with
coefficient \(d_m\ne0\). Multiply their Dirichlet-series difference by
\(m^s\) and let real \(s\to\infty\). If \(|d_n|\le C\), the tail for
\(s\ge2\) is bounded by

\[
C\left(\frac{m}{m+1}\right)^{s-2}
 \sum_{n>m}\left(\frac mn\right)^2\longrightarrow0.
\]

Consequently the limit equals \(d_m\), so an identically zero difference
would be impossible. For periodic blocks, equality is already decidable on
one least-common-multiple period. `separating_witness` records the first
unequal coefficient, or the full common-period comparison when they agree.
It carries an explicit work budget and does no numerical value recognition.

`PeriodObservation.generating_function()` uses the existing
`generating.RationalGF` implementation to cancel polynomial factors over
\(\mathbb Q\). `machine()` realizes the coefficient block as a cyclic shift
and reads its first coordinate, then invokes the existing
`observable_machine.minimal_machine`. Its exact intertwining identities
preserve every future output. Its finite spanning-word and nonsingular
Hankel-minor witnesses establish minimal linear dimension over \(\mathbb Q\).
At machine time \(k\ge0\) the output is \(c_{k+1}\), whereas the Dirichlet
series starts at index one. The general block budget is 4096 entries; the
existing dense machine is limited to 64 states. Coefficients have an
8192-bit rational budget. These are exact Python certificates, not Lean proofs.

For E8 reflection traces the coefficients are the integer Ramanujan sums
\(c_{30}(n)\), the reduced denominator is \(\Phi_{30}(x)\), and the minimal
observable dimension is eight. For the actual adjoint Coxeter lift, the
separate Lie-algebra calculation gives

\[
a_n=c_{30}(n)+240\,\mathbf1_{30\mid n}.
\]

Its reduced denominator is \(1-x^{30}\), so the minimal trace-output machine
has dimension 30. The underlying adjoint representation still has dimension
248. This compression neither constructs a 30-dimensional replacement Lie
algebra nor identifies the full adjoint representation with a smaller one.
The independently reduced rational kernel and observable quotient agree on
these dimensions. `receipt()` retains both certificates, including their
nonzero Hankel determinants.

The adjoint example also separates a special-value cancellation from loss of
the complete observation: \(F_a(2)=0\), yet \(a_{30}=248\). Its zero period
therefore does not make its sequence, kernel, or full Dirichlet function zero.
Tests compare late outputs through time \(10^{18}\), repeated blocks,
kernel values, coefficients from the Dirichlet engine, the E8 matrix traces,
and the exact weight-two cancellation. No floating-point calculation enters
these checks.



## Coxeter Mellin traces: all types and prescribed vanishing weights

The E8 calculation belongs to a complete real-zero classification. A cited theorem about Coxeter lifts resolves the root-space closing scalars in all crystallographic types; exponent filters then produce compact exact formulas. The B/C case gives a particularly concrete design rule: choose the rank to choose the integer vanishing weight.

### From an actual Coxeter lift to the spectrum

Work over the complex numbers. Let $G$ be a connected simple algebraic group, $T$ a maximal torus, $R$ its root system, $r$ its rank, $h$ its Coxeter number, $c$ a Coxeter element in the Weyl group, and $g$ any lift of $c$ in the normalizer of $T$. The elementary-looking distinction between a permutation of roots and the adjoint action on root spaces matters: $g$ can multiply root vectors by scalars as it permutes their root spaces. A dimension match alone does not identify their spectra.

Adams and He, *Lifting of elements of Weyl groups*, Proposition 5.1.1, give the needed theorem: the $h$-th power of $g$ is the principal central involution. Its adjoint action is therefore the identity. Their section 5.1 also records that Coxeter elements are regular. These standard Lie-theoretic results are cited inputs to the following argument, not new results of the Python calculation.

Choose a regular Coxeter eigenvector $v$ with primitive eigenvalue $\zeta_h$. If a root $\alpha$ were fixed by $c^d$, invariance of the pairing would give

\[
(1-\zeta_h^{-d})\langle\alpha,v\rangle=0.
\]

Regularity means that the second factor does not vanish, so $h$ divides $d$. Every root orbit thus has exactly $h$ members. There are $r$ such orbits because the root count is $rh$. On one orbit, choose a nonzero root vector $X$ and use $X,\operatorname{Ad}(g)X,\ldots,\operatorname{Ad}(g)^{h-1}X$ as a basis. The vectors belong to distinct root spaces, and $\operatorname{Ad}(g)^hX=X$. In that basis the action is the regular $h$-cycle, including its closing coefficient. This resolves the possible root-vector signs and scalars.

On the Cartan subalgebra the eigenvalues are $\zeta_h$ to the reflection exponents $m_1,\ldots,m_r$. Consequently the adjoint eigenvalue multiset consists of $r$ full $h$-cycles together with those $r$ Cartan eigenvalues. The resulting dimension is $r(h+1)$, the dimension of the simple Lie algebra. A different central quotient of $G$ has the same adjoint representation and the same trace.

The exact module independently constructs the simple reflections, their Coxeter product, reflection closure of the simple roots, and the actual root orbits. It compares the integer matrix characteristic polynomial against the polynomial obtained from the stated exponents. This finite evidence checks the implemented data, while the cited theorem and preceding argument establish why those data describe the adjoint spectrum.

### The Mellin identity

Let $C$ denote that finite-order adjoint operator. Its resolvent trace kernel is

\[
K_R(x)=\operatorname{Tr}\bigl(C(I-xC)^{-1}\bigr),\qquad 0<x<1.
\]

For complex $s$ with real part greater than one, the geometric series and the classical polylogarithm Mellin integral give

\[
Z_R(s):=\frac{1}{\Gamma(s)}\int_0^1(-\log x)^{s-1}K_R(x)\,dx
=\zeta(s)\,r h^{1-s}+\sum_{j=1}^r\operatorname{Li}_s(\zeta_h^{m_j}).
\]

The condition on $s$ controls the possible $1/(1-x)$ singularity from the eigenvalue one. It also justifies absolute convergence of the series used in the derivation. The identities concern the normalized integral $Z_R$; a raw integral has the additional $\Gamma(s)$ factor. The code keeps that normalization explicit.

The regular-cycle contribution follows from summing a complete root-of-unity fiber. The exceptional exponent contributions reduce by the same divisor filters already used by the E8 and cyclotomic engines. Since the spectrum is rational, the final coefficient of $\zeta(s)$ is a finite combination of real positive bases to the power $1-s$. At integer weights every such coefficient is rational.

### The complete classification for real s greater than one

Write $t=s-1$, so $t$ is positive. The following table gives the complete real-zero classification. Since $\zeta(s)$ and $h^t$ are positive for real $s>1$, the displayed numerator alone determines the sign and zeros.

| Type | Coxeter number | Unique real zero on $s>1$ |
|---|---:|---|
| $A_n$ | $n+1$ | $2$ |
| $B_n$, $C_n$ | $2n$ | $1+\log(n+1)/\log2$ |
| $D_n$ | $2(n-1)$ | $2$ |
| $E_6$, $E_7$, $E_8$ | $12$, $18$, $30$ | $2$ |
| $F_4$, $G_2$ | $12$, $6$ | none |

Writing $Z_R(s)/\zeta(s)=P_R(t)/h^t$, the exact numerators are

\[
\begin{aligned}
P_{A_n}(t)&=n+1-(n+1)^t,\\
P_{B_n}(t)=P_{C_n}(t)&=n+1-2^t,\\
P_{D_n}(t)&=n+1-2^t-(2^t-1)(n-1)^t,\\
P_{E_6}(t)&=6-(3^t-1)(4^t-2^t+1),\\
P_{E_7}(t)&=7-(2^t-1)(9^t-3^t+1),\\
P_{E_8}(t)&=8-(2^t-1)(3^t-1)(5^t-1),\\
P_{F_4}(t)&=4+(2^t-1)(3^t-1),\\
P_{G_2}(t)&=2+(2^t-1)(3^t-1).
\end{aligned}
\]

Here $n$ is the rank, and the standard irreducibility ranges remove the low-rank repetitions. The $B_1$ and $C_1$ boundary case is $A_1$ and is included separately by the tuner when $k=2$. Noncrystallographic finite reflection groups and nonreduced root systems are outside this classification.

For type A the numerator is strictly decreasing and is zero at $t=1$. For type D, both subtracted terms are strictly increasing and positive for $t>0$; the value at $t=1$ is $n+1-2-(n-1)=0$. For $E_6$, both positive factors in the product are strictly increasing: the derivative of $4^t-2^t$ is $\log(2)(2\cdot4^t-2^t)>0$. For $E_7$ the same argument applies to $9^t-3^t$. For $E_8$ all three positive factors are strictly increasing. In each exceptional E case the product takes the value $r$ at $t=1$. Thus A, D, and E have a positive normalized trace for $1<s<2$, exactly one zero at $s=2$, and a negative normalized trace for $s>2$.

For types B and C the numerator decreases strictly from $n$ to minus infinity, and its sole zero solves $2^t=n+1$. Types $F_4$ and $G_2$ have positive numerators for every $t>0$ and no real zero in this domain. This proves completeness of the real-zero classification once the displayed finite reductions are established. It says nothing about zeros at nonreal $s$.

### Recovering the reductions from exponent fibers

For $A_n$ the Cartan exponents are all nonzero residues modulo $h=n+1$. Their polylogarithm sum is $(h^{-t}-1)\zeta(s)$. Adding the $n$ regular cycles gives the A numerator in the table.

For $B_n$ and $C_n$ the exponents are all odd residues modulo $2n$. The full $2n$-fiber minus the even $n$-fiber gives $((2n)^{-t}-n^{-t})\zeta(s)$. Adding $n$ regular cycles gives

\[
Z_{B_n}(s)=Z_{C_n}(s)
=\zeta(s)n^{1-s}\left((n+1)2^{1-s}-1\right).
\]

For $D_n$ the odd residues modulo $2(n-1)$ occur together with the additional exponent $n-1$. That extra exponent must be counted even when it duplicates an odd exponent. Its polylogarithm is $\operatorname{Li}_s(-1)=(2^{-t}-1)\zeta(s)$. This gives the displayed D formula. Omitting the duplicate exponent in even rank would produce a false answer.

For $E_6$ the exponents modulo 12 comprise the primitive 12th roots and the two primitive cube roots. For $E_7$ the exponents modulo 18 comprise the primitive 18th roots and the additional phase -1. For $E_8$ all eight exponents are primitive modulo 30. The divisor filters respectively give the three factorizations in the table. Types $F_4$ and $G_2$ have the primitive exponents modulo 12 and 6; after adding their regular cycles the surviving product has a plus sign. These statements can be checked entirely through rational cyclotomic polynomials and integer Coxeter matrices, without floating eigenvalue calculations.

### Prescribing the vanishing weight

For any integer $k\ge2$ set

\[
n=2^{k-1}-1.
\]

Then the $B_n$ and $C_n$ zero occurs at exactly $s=k$. This is an infinite family in the mathematical statement. The implementation accepts arbitrary integer weights within a caller-visible rank bit budget and computes $n$ symbolically without allocating rank-n matrices. The default budget allows 4096-bit ranks, hence target weights through 4097. Increasing the explicit budget extends the implementation range; the theorem itself has no such ceiling.

The corresponding rational kernel has an elementary closed form:

\[
\boxed{K_n(x)=n\,\frac{(2n+1)x^{2n-1}-x^{n-1}}{1-x^{2n}}.}
\]

One way to see this is to use the Cartan characteristic polynomial $u^n+1$. Its resolvent trace is $-nx^{n-1}/(1+x^n)$. The $n$ regular Coxeter cycles contribute $2n^2x^{2n-1}/(1-x^{2n})$. Combining denominators gives $K_n$. The kernel changes sign once on $(0,1)$, at $x=(2n+1)^{-1/n}$; the Mellin weight controls how its positive and negative portions balance.

Differentiating the unnormalized Mellin integral at the tuned zero gives a logarithmic companion. The Gamma derivative and zeta derivative terms disappear because they multiply the vanishing factor. What remains is

\[
\boxed{\int_0^1(-\log x)^{k-1}\log(-\log x)K_n(x)\,dx
=-\Gamma(k)n^{1-k}\zeta(k)\log 2.}
\]

This derivative identity is valid for the exact tuned $n$. The normalization is essential: the formula includes $\Gamma(k)$, unlike the derivative of the normalized $Z$. Since $n>0$ and $\zeta(k)>0$, the logarithmic companion is strictly negative.

At $k=4$, $n=7$, the actual $B_7$ and $C_7$ adjoint spectra have dimension 105 and Coxeter number 14. Their common kernel is

\[
K_7(x)=7\frac{15x^{13}-x^6}{1-x^{14}}.
\]

The two exact raw integrals are

\[
\int_0^1(-\log x)^3K_7(x)\,dx=0,
\qquad
\int_0^1(-\log x)^3\log(-\log x)K_7(x)\,dx
=-\frac{\pi^4\log 2}{5145}.
\]

At $k=3$ the rank is three, so $B_3/C_3$ already provide a weight-three cancellation with logarithmic companion $-2\zeta(3)\log(2)/9$. At $k=8$ the rank is 127. These examples make the scaling cost visible: choosing a larger vanishing weight grows the required rank exponentially, even though the symbolic factor remains compact.

### Exact implementation and reproducibility

The implementation is `python/perfectpower/coxeter_mellin.py`. Its `zeta_factor(family, rank, s)` returns the exact rational coefficient of $\zeta(s)$ at integer weight $s$. `even_pi_coefficient` converts an even-weight trace to its rational coefficient of $\pi^s$. `bernoulli_pi_coefficient` independently sums Bernoulli polynomials over every root-cycle and Cartan phase. The comparison does not reuse the closed zeta-factor reduction.

`cartan_matrix`, `roots`, `coxeter_matrix`, and `root_orbits` construct the finite geometry in simple-root coordinates through rank sixteen. `geometry_receipt` checks the root count, the actual orbit partition, the exact order of the Coxeter matrix, and its characteristic polynomial against the exponent polynomial. An independent B/C calculation starts with the Euclidean roots $\pm e_i\pm e_j$ and the axial roots, then applies the signed coordinate cycle $e_i\mapsto e_{i+1}$, $e_n\mapsto-e_1$. It obtains $n$ complete $2n$-cycles without using the Cartan closure. E8 root coordinates and its operator also agree exactly with the earlier dedicated E8 module. The complete receipt has 64 geometry cases: A1 through A16, B2 through B16, C2 through C16, D4 through D16, and the five exceptional systems.

`bc_zero_tuner(k)` returns the tuned rank, dimension, Coxeter number and normalization as a JSON-safe record. A rank-bit guard protects allocation of the rank integer. `zeta_factor` and `bc_kernel` separately check exact-exponentiation budgets before constructing large rational powers. Those resource limits are explicit implementation limits, not restrictions on the identities.

Run the independent focused checks with `PYTHONPATH=python python3 -m unittest python/tests/test_coxeter_mellin.py -v`. The tests cover all 64 finite geometries, five even Bernoulli weights on 27 systems, exact E8 agreement, tuning at every integer weight from 2 through 128, the 4096-bit rank boundary, the weight-four logarithmic value, and the B/C rational kernel. The exact finite computations use the Python standard library and the existing rational polynomial machinery. They do not invoke numerical root finding or require SymPy.

### Sources and scope

Jeffrey Adams and Xuhua He, *Lifting of elements of Weyl groups*, [arXiv:1608.00510](https://arxiv.org/html/1608.00510v1), section 5.1, Proposition 5.1.1, supplies the central power of a Coxeter lift; section 1 defines the central principal involution. The application to the root-space cycles is the argument given above.

Mark Reeder, *Cyclotomic structures on root lattices*, [author-hosted paper](https://www.math.utah.edu/~ptrapa/math-library/reeder/reeder-cyclotomic-root-lattices-2008.pdf), section 3.2, relates reflection exponents to cyclotomic spectra and gives exceptional exponent data. The implemented matrices and roots provide an independent finite check of the displayed data.

The [NIST Digital Library of Mathematical Functions, section 25.12](https://dlmf.nist.gov/25.12), supplies the standard polylogarithm Mellin representation and root-of-unity identities. The reductions, sign argument, and zero tuner in this note are derived from these inputs. A separate literature study would be needed before asserting that the classification or a particular presentation is new. No equation here identifies unrelated 240-dimensional objects, proves the Claude artifacts' proposed categorical colimit, or establishes a physical E8 model.


## Reproduction, provenance, and what has actually been established

The exact mathematical engine uses the Python standard library and existing PerfectPower rational polynomial modules. The PDF renderer additionally requires ReportLab, pypdf, Pandoc, and XeLaTeX. From the repository root the main research command is `PYTHONPATH=python python3 -m perfectpower integral-families --details`. The deterministic deeper receipts are regenerated by `PYTHONPATH=python python3 python/develop_period_bridge_deep.py`; the browser source is exported by `python3 python/export_integral_browser.py`. The retained JSON reports name the source files and hashes used for each computation. They distinguish historical evidence from results freshly calculated from the present source.

Focused tests are ordinary `unittest` modules under `python/tests`. The suite covers the Raghava base and generating engines, cyclotomic filters and phase transports, linear conductor descent, periodic Dirichlet families, E8 roots and actual lifts, complete observation quotients, and all-type Coxeter Mellin formulas. A selected module can be run from the repository root as follows:

```bash
PYTHONPATH=python python3 -m unittest \
  python.tests.test_dirichlet_periods -v
```

These tests check distinct mechanisms: root fibers and Bernoulli coordinates, original inverse-binomial tails versus zeta enclosures, actual Lie brackets and Tits relations, exact matrix adjunctions, character conductor/Euler formulas, minimal observable quotients, and all-type geometric and spectral reductions.

The previously saved deeper monograph reported a historical 91-test run. That number is preserved as a record of that earlier artifact, not added to present tests or treated as proof that missing code was executed after recovery. The current release verification independently passed 108 Python tests and 330 actual browser comparisons: 130 generating families, 120 selected-order decompositions, 24 angle cases, 50 harmonic moments, and six E8 cases. Twenty-one source and receipt digests bind those browser comparisons to the retained source. The deterministic receipts retain their detailed finite sweep counts separately; none of the historical test count is included in these fresh totals.

The strongest general statements are proved through the displayed derivations and their cited analytic or Lie-theoretic inputs. Finite enumeration independently checks the concrete geometry, coefficients, and matrix identities used in software. Rational remainder bounds certify the numerical enclosures they actually report. A finite set of numerical comparisons is not a proof of every all-order formula, and an exact Python packet is not automatically a Lean theorem. These distinctions keep the bridge useful: a recipient can reproduce a finite result, inspect the general argument, and see precisely where a classical theorem is an input.

Resource limits are explicit. The generating-family engine supports orders zero through 64, and the dense formal second-basis conversion supports order through 32. The phase-descent DFT reconstruction has a conductor budget of 64. The Dirichlet character enumeration has a default modulus budget of 128; explicit cyclotomic arithmetic can use a caller's chosen ambient order, so this monograph does not claim a nonexistent default DFT-order guard in that separate module. General periodic observation blocks support 4096 entries and the dense observable-machine realization is limited to 64 states. General Coxeter root geometry is constructed through rank 16; the B/C weight tuner instead retains a symbolic rank and accepts a caller-visible rank-bit budget. None of these implementation bounds truncates the mathematical identities themselves.

The source collection came from publicly accessible mathematical pages, author materials, search-indexed content, and archives. It recorded 644 Raghava archive entries, of which 308 were integral-bearing, 73 transcribed mathematical formulas, 30 Math Stack Exchange threads, and four LinkedIn posts. These are different units: a source URL, an archive entry, a posted solution, and a distinct integral are not interchangeable, and repeated publication can describe the same mathematics. Zero original Facebook posts were directly verified in this collection. Therefore this reader does not present the recovered archive as an exhaustive Facebook history.

For Chew Seong-Cheong, the collection verified two credited solutions and collaborative wiki participation; that evidence does not assign sole authorship of every surrounding formula. Sazzie Lyon remained unresolved, and no material is attributed to another similarly named person as a substitute. The two Claude artifacts were supplied by the user and attributed by the user to Cody Lakeland. Their phase labels were directly examined and provided the conductor inputs, while Facebook identity and publication provenance remained unverified. The mathematical constructions here remain reproducible independently of those unresolved attribution questions.

A further public-source check in the present release retained 22 targeted Sazzie identity queries without establishing a verified identity. Two additional Cheong-related publisher archives were found, but no new verified integral was attributed to him; the two known Telegram credits were reconfirmed, and nearby formulas credited to other solvers were excluded. These negative results are retained because a larger search result count must not be mistaken for a larger verified mathematical corpus.

The work fulfills the concrete portion of the larger aspiration through definitions that can be used immediately: exact integral generators, formal zeta normal forms, rational analytic enclosures, actual phase-linear morphisms and adjunctions, conductor descent, a genuine E8 inner automorphism, full complex trace recovery, observable compression, and a complete crystallographic real-zero classification. A higher category with specified higher cells, a physical model, or an equivariant identification between the unrelated 240-dimensional objects would each require additional data and theorems. The present results provide explicit objects and invariants that any such future construction would have to preserve.

Publishing is a separate operational step from deriving the mathematics. The repository changes must reach the canonical `main`, the deterministic feeds must be regenerated, and the browser assets must be deployed before the live application can claim the new capabilities. Updating live data does not rewrite an installed APK or Windows executable. Each release therefore supplies a pinned complete source archive and this reader, while recording the active browser and native engine snapshots separately.

## A real Coxeter–Raghava bridge: lattices, moments, and induction

**PerfectPower. Mathematical chapter prepared 17 October 2026.**

The construction in this chapter replaces an association between pictures by an explicit integral coordinate map and a commuting system of exact operations. The eight-dimensional E₈ Coxeter lattice is identified with an integral cyclotomic companion module, including its bilinear form. Raghava's inverse-binomial series are then applied to that actual operator. A triangular Bernoulli transformation identifies their traces with the real even Mellin traces of the same operator. Ordinary cyclic induction acts on both descriptions, and the transformation intertwines the two actions. This is the precise sense of unification used here. It does not assert an equivalence of unspecified higher categories or a physical model.

### The actual integral lattice map

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

### One operator produces the Raghava and Mellin families

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

### The exact invertible Bernoulli transformation

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

### An exact inverse-binomial evaluation from the E₈ operator

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

### The actual adjoint lift and its cancellation

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

### Induction is an exact operation on the moments

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

### A preserved cancellation and a sharp uniqueness statement

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

### Why the tempting 240-to-240 identification fails

The primitive branches above the fixed phase \(\zeta_{1680}\) have exponents

\[
u=1+1680t,\quad0\le t<264,\quad\gcd(u,443520)=1.
\]

There are 240 such branches. Every exponent satisfies \(u\equiv1\pmod{30}\). Restricting their characters from \(C_{443520}\) to its natural \(C_{30}\) subgroup therefore gives 240 copies of the single phase \(\zeta_{30}\). The root-space part of the actual E₈ Coxeter lift gives eight copies of every thirtieth-root phase. The multiplicity functions disagree, so no equivariant isomorphism exists for this proposed natural restriction. An arbitrary bijection of the two underlying sets cannot repair that representation-theoretic obstruction.

The integral lattice isomorphism (1) and the commuting formulas (9), (18) and (21) avoid this problem. They identify specified operators and preserve specified forms or transformations. They do not require the false fixed-fiber identification.

### Proof scope, reproducibility and originality

The analytic results in this chapter have mathematical proofs from the cited classical scalar identities, finite spectral calculus, the centered binomial expansion and elementary convergence estimates. Historical priority for their present combination or the displayed E₈ inverse-binomial evaluations has not been established. They are reported as derived bridges and concrete evaluations, rather than as a newly discovered special-function summation principle.

The exact Python implementation is `python/perfectpower/raghava_coxeter.py`. Its `receipt(order=8)` recomputes the operator polynomial, moment and Mellin coordinates, triangular inverse, degree-264 transfer checks, fixed-fiber obstruction and independent series enclosures. The focused command is `PYTHONPATH=python python3 -m unittest python/tests/test_raghava_coxeter.py -v`. All eleven focused tests passed during preparation of this chapter. They include 6560 exact scalar phase comparisons through conductor forty and weight sixteen, 81 powers of the actual eight-dimensional matrix, 41 powers of the actual signed 248-dimensional adjoint matrix, exact transfer composition and Bernoulli diagonalization, and positive-series tail comparisons. These checks exercise independent finite mechanisms; they are not substitutes for the general mathematical proofs.

The three new Lean modules compile with pinned Lean 4.20.0 and Mathlib 4.20.0. The integrated audit checks all 102 theorem declarations: 15 finite Fourier and fiber theorems, 61 integral Coxeter and operator theorems, and 26 rational phase-moment and induction theorems. Their axiom reports contain only the standard propext, Classical.choice and Quot.sound; no admitted proof, native decision oracle or new axiom occurs. Reproduce with `make raghava-coxeter-kernel`. The source-bound result is retained in `receipts/period_bridge_deep/unification_lean.json`. The infinite-series, functional-calculus and analytic convergence arguments in this chapter remain mathematical proofs outside the Lean kernel; the Lean files do not import them as new axioms.

## Primary references and attribution

K. Srinivasa Raghava, *Arcsine kernels, inverse-binomial harmonic sums, and classical hypergeometric transformations*, version 2, revised 15 October 2026, [arXiv:2607.09904v2](https://arxiv.org/html/2607.09904v2). This is the source of the implemented arcsine, selected-order, complete second and supplementary generating families, master identity, and complete-monotonicity input, with the paper's stated classical antecedents.

*Srinivasa Raghava: Patterns, Primes, and the Ramanujan Influence*, [ICTP Global Science Portal](https://ictp.global/news/13119204). The displayed sine-pole examples are credited to Raghava and the all-order extension to Abdulhafeez Abdulsalam.

NIST Digital Library of Mathematical Functions: [25.12, Polylogarithms](https://dlmf.nist.gov/25.12), [25.14, Lerch's Transcendent](https://dlmf.nist.gov/25.14), [25.15, Dirichlet L-functions](https://dlmf.nist.gov/25.15), and [24.8, Bernoulli and Euler Fourier Series](https://dlmf.nist.gov/24.8). These provide the classical special-function conventions and analytic identities.

Meinolf Geck, *On Lusztig's canonical bases of simple Lie algebras*, [arXiv:2602.19632v1](https://arxiv.org/html/2602.19632v1), Theorem 3.3 and Example 3.4, for the simply-laced Lie-algebra construction with its cocycle signs. Jeffrey Adams and Xuhua He, *Lifting of elements of Weyl groups*, [arXiv:1608.00510](https://arxiv.org/html/1608.00510v1), especially section 5.1 and Proposition 5.1.1, for the central power of a Coxeter lift and its adjoint consequence.

Mark Reeder, *Cyclotomic structures on root lattices*, [author-hosted paper](https://www.math.utah.edu/~ptrapa/math-library/reeder/reeder-cyclotomic-root-lattices-2008.pdf), especially section 3.2, for cyclotomic structures and exceptional exponents. David A. Richter, *Triacontagonal coordinates for the E(8) root system*, [arXiv:0704.3091](https://arxiv.org/abs/0704.3091). John Baez, [Integer Octonions, Part 3](https://math.ucr.edu/home/baez/octonions/integers/integers_3.html), for the explicit 112-plus-128 root-coordinate description.

The supplied project references are [Categorical-Spectral-Cyclotomic Framework Visualization](https://claude.ai/public/artifacts/1db99748-b7fd-477b-8a9c-1bb54fb33a19) and [Higher Categorical Framework: The 384-264 Resonance](https://claude.ai/public/artifacts/4fd0f32a-22b6-4fae-b2d2-1f3732d324af). Their inspiration is preserved while the executable constructions, proof scopes, and source attributions remain explicit.


<!-- INTEGRAL_STUDIO_SUPPLEMENT_START -->

# The golden integral studio: exact energies, arithmetic sectors, and E8 geometry

**Mathematical supplement. 17 October 2026.**

This supplement gives the mathematical specification of the React integral studio. Its central object is one four-parameter quadratic energy. Every curve, spectral sector, recurrence, and energy surface is a view of that same defined object. The former 38 pages of the reader remain intact; this supplement adds the proofs needed by the new instrument. The finite Lean results in those earlier pages retain their original scope. The new analytic identities here are mathematical derivations with numerical cross-checks, not new Lean theorems.

## One master energy

Put phi=(1+sqrt(5))/2 and define

\[
Q_+(x)=4x^2-2\varphi^{-1}x-\varphi^2,\qquad
Q_-(x)=4x^2+2\varphi x-\varphi^{-2}.
\]

Their product is Q(x)=16x^4+8x^3-16x^2-8x+1. Set

\[
u(x)=\pi^2/4-(\arcsin x)^2,\quad
A(x)=\log|Q_+(x)Q_-(x)|,\quad
K(x)=\log|Q_+(x)/Q_-(x)|,
\]

\[
P(x)=u(x)^2,\qquad R(x)=u(x)^2\bigl(u(x)+\pi^2/2\bigr).
\]

For real t=(a,b,c,d), our single master integral is

\[
\mathcal E(a,b,c,d)=\int_{-1}^1
\frac{[aA(x)+bK(x)+cP(x)+dR(x)]^2}{\sqrt{1-x^2}}\,dx.
\]

Use the principal real arcsine. All four internal logarithmic singularities are ordinary improper integrals, not principal values. The substitution x=cos(theta), 0<=theta<=pi, gives u=theta(pi-theta) and dx/sqrt(1-x^2)=dtheta after reversing the limits. Thus the arcsine endpoint weight disappears exactly. Squared logarithms remain integrable near every internal zero, since the integral of |log s|^2 over (0,epsilon) is finite.

Write f=(A,K,P,R). The exact Gram matrix H has entries H_ij=integral(f_i f_j dtheta), and E=t^T Ht. Off-diagonal entries contribute twice: the coefficient of ac in the expanded energy is 2H_AP. This normalization is essential when recovering the earlier challenge integrals from a single quadratic form.

## The complete answer

With chi_5(n)=0,1,-1,-1,1 for n modulo 5 equal to 0,1,2,3,4 respectively, and L(s,chi_5)=sum chi_5(n)/n^s, the ten independent matrix entries are

\[
\begin{aligned}
H_{AA}&=8\pi^3/45,&H_{AK}&=-4\pi^3/75,&H_{KK}&=8\pi^3/15,\\
H_{AP}&=832\pi\zeta(5)/1125,&H_{AR}&=157976\pi\zeta(7)/28125,\\
H_{KP}&=41\pi\sqrt5L(5,\chi_5)/54,&
H_{KR}&=1825\pi\sqrt5L(7,\chi_5)/324,\\
H_{PP}&=\pi^9/630,&H_{PR}&=4\pi^{11}/3465,&
H_{RR}&=101\pi^{13}/120120.
\end{aligned}
\]

This matrix is positive definite without assuming any algebraic independence of zeta or L-values. If aA+bK+cP+dR vanishes almost everywhere, its logarithmic coefficients at the zeros of Q_+ and Q_- must vanish. Those coefficients are a+b and a-b, forcing a=b=0. The remaining expression P[c+d(u+pi^2/2)] vanishes on an interval, so c=d=0. Consequently every nonzero parameter vector has strictly positive energy.

The logarithmic 2-by-2 block also gives the exact orthogonality

\[
\int_{-1}^1 A(x)[3A(x)+10K(x)]\frac{dx}{\sqrt{1-x^2}}=0,
\]

because 3H_AA+10H_AK=0. Away from the finite roots, 3A+10K=log|Q_+^13/Q_-^7|. The integers 13 and 7 follow from the Gram matrix rather than an arbitrary choice of exponents.

## Why Bernoulli weights isolate odd constants

For m>=1, define P_m as the polynomial in u determined by

\[
P_m(\pi^2t(1-t))=(-1)^m\pi^{2m}[B_{2m}(t)-B_{2m}(0)].
\]

The symmetry B_2m(1-t)=B_2m(t) makes the right side a polynomial in t(1-t): every polynomial invariant under t->1-t is a polynomial in that quantity. The first examples are P_1=u, P_2=u^2=P, and P_3=u^2(u+pi^2/2)=R. The classical Bernoulli Fourier expansion gives, with d_m=(2m)!/2^(2m-1),

\[
P_m(\theta(\pi-\theta))=d_m\left[\zeta(2m)-\sum_{n\ge1}\frac{\cos(2n\theta)}{n^{2m}}\right].
\]

Only even angular frequencies survive. It follows that

\[
\int_0^\pi A(\cos\theta)P_m\,d\theta
=\frac{(2m)!\pi}{2^{2m+1}}
(1-3^{-2m})(1-5^{-2m})\zeta(2m+1),
\]

\[
\int_0^\pi K(\cos\theta)P_m\,d\theta
=\frac{(2m)!\pi\sqrt5}{2^{2m+1}}
(1+3^{-2m})L(2m+1,\chi_5).
\]

For m=2 and m=3 these are precisely H_AP, H_AR, H_KP, and H_KR. The family therefore selects every odd zeta value from the product logarithm and every odd chi_5 L-value from the ratio logarithm. The coefficients and the particular extra pi^2/2 in R are fixed by the Bernoulli expansion. They cancel lower-weight contributions exactly.

## Cyclotomic factors and the Fourier proof

Let C be the actual integral E8 Coxeter matrix used in the earlier chapter, and set L=2I+C+C^(-1). Its primitive phase exponents modulo 30 are 1,7,11,13,17,19,23,29. For z=exp(i theta),

\[
z^4Q(\cos\theta)=\Phi_{30}(z),\quad
\det(I-zC)=\Phi_{30}(z),\quad
\det((2x+2)I-L)=Q(x)^2.
\]

The squared determinant occurs because conjugate Coxeter phases have the same value of 2+2cos(theta). Thus Q is a square root of this determinant with its explicitly stated leading coefficient, not the full characteristic polynomial of L.

Define the Ramanujan sum c_N(n)=sum_{r mod N,(r,N)=1} exp(2pi i rn/N). Factoring Phi_30 into its primitive roots gives the real Fourier series

\[
A(\cos\theta)=-\sum_{n\ge1}\frac{c_{30}(n)}n\cos(n\theta),
\]

\[
K(\cos\theta)=-\sum_{n\ge1}
\frac{\sqrt5\chi_5(n)c_6(n)}n\cos(n\theta).
\]

The second formula follows by weighting primitive phase exponents by chi_5. The quadratic Gauss sum modulo 5 is sqrt(5); Chinese remainder factorization supplies c_6. The positive sector contains the phase pairs with representatives 1 and 11, while the negative sector contains 7 and 13. This fixes the sign of K and of the mixed Gram entries.

For rigor, first replace each unit-modulus root by radial damping 0<r<1. The logarithmic Fourier series is then absolutely convergent. Its Fourier coefficients are square summable uniformly in r, and the radial boundary limit exists in L^2(0,pi); finite sums of log|2sin((theta-alpha)/2)| have exactly this limit. Parseval and scalar products with the smooth polynomial weights therefore pass to the limit in L^2. No pointwise interchange at a logarithmic zero is required.

Multiplicativity gives c_30(2n)=c_15(n). Its Dirichlet series is

\[
\sum_{n\ge1}\frac{c_{30}(2n)}{n^s}
=(1-3^{1-s})(1-5^{1-s})\zeta(s).
\]

Also chi_5(2)=-1, c_6(2n)=c_3(n)=-1+3[3 divides n], and chi_5(3)=-1. Therefore

\[
\sum_{n\ge1}\frac{\sqrt5\chi_5(2n)c_6(2n)}{n^s}
=\sqrt5(1+3^{1-s})L(s,\chi_5).
\]

Taking the Fourier scalar product with P_m contributes the common factor d_m*pi/4 and proves both selector families.

## Parseval and the remaining six entries

The cosine functions have squared norm pi/2 for every positive integer frequency. For a prime p, c_p(n)=-1+p[p divides n], so c_p(n)^2=1+p(p-2)[p divides n]. It follows that

\[
\sum_{n\ge1}\frac{c_{30}(n)^2}{n^2}
=\frac{32}{15}\zeta(2),\qquad
\sum_{n\ge1}\frac{5\chi_5(n)^2c_6(n)^2}{n^2}
=\frac{32}{5}\zeta(2).
\]

Multiplication by pi/2 gives H_AA and H_KK. For the mixed term, chi_5 is zero on multiples of 5 and c_5=-1 otherwise. Moreover c_6^2=1+3[3 divides n]. Thus

\[
H_{AK}=-\frac{\pi\sqrt5}{3}L(2,\chi_5)
=-\frac{4\pi^3}{75}.
\]

For completeness, B_2(1/5)=B_2(4/5)=1/150 and B_2(2/5)=B_2(3/5)=-11/150. Summing against chi_5 gives 4/25. The B_2 Fourier expansion and the Gauss sum yield L(2,chi_5)=4pi^2/(25sqrt(5)), establishing the displayed mixed evaluation directly.

The polynomial block needs only the beta integral. Set t=theta/pi and v=t(1-t). Then P=pi^4v^2 and R=pi^6v^2(v+1/2). With B(r,s)=integral_0^1 t^(r-1)(1-t)^(s-1)dt,

\[
H_{PP}=\pi^9B(5,5)=\pi^9/630,
\]

\[
H_{PR}=\pi^{11}[B(6,6)+\tfrac12B(5,5)]
=4\pi^{11}/3465,
\]

\[
H_{RR}=\pi^{13}[B(7,7)+B(6,6)+\tfrac14B(5,5)]
=101\pi^{13}/120120.
\]

These calculations finish all ten entries, hence the complete four-parameter answer. They also explain why a single energy can contain zeta values, Dirichlet L-values, powers of pi, and a logarithmic orthogonality relation without treating them as unrelated examples.

## A genuine golden action on the integral lattice

Define G=I+C^6+C^24. Exact integer matrix multiplication, using Phi_30(C)=0 and C^30=I, gives

\[
G^2=G+I,\qquad GC=CG,\qquad G^{-1}=G-I.
\]

At a primitive phase exponent r, the eigenvalue of G is 1+2cos(2pi r/5): it is phi when chi_5(r)=1 and -phi^(-1) when chi_5(r)=-1. Thus the two logarithmic sectors are the two real embeddings of the golden quadratic field inside the same Coxeter module. They are not a relabeling of two unrelated collections of points.

There is also an explicit integral module basis. If v is the eighth simple-root coordinate vector, the matrix with columns

\[
M=(v,Cv,C^2v,C^3v,Gv,GCv,GC^2v,GC^3v)
\]

has determinant -1. Exact fraction elimination is included in the reproducible PDF builder. The map sending the golden integer a+bphi to aI+bG therefore equips the lattice with a free Z[phi]-module structure of rank four, with module basis v,Cv,C^2v,C^3v. The eight columns of M are a Z-basis, so neither an index nor a denominator is concealed in this assertion.

The normalized grading J=(2G-I)/sqrt(5) satisfies J^2=I. Its eigenspace projectors (I+J)/2 and (I-J)/2 are real spectral projectors onto the two character sectors, not integer lattice endomorphisms. This distinction separates the integral golden action G from the normalized sector coloring J.

The same quadratic relation proves G^n=F_n G+F_(n-1)I for n>=1. Fibonacci recurrence is consequently an exact law for these integer transformations. G is an invertible lattice endomorphism and commutes with C; it is not an isometry of the positive-definite E8 metric. A map with expanding eigenvalue phi cannot preserve that metric. No H4 root-system identification or physical golden-ratio claim follows solely from this module structure.

## What the pictures mean mathematically

The spectral view uses the actual 240 E8 roots and the actual Coxeter action; the eight-dimensional reflection module is not confused with the 240-dimensional root permutation module. For a primitive exponent r and the Cartan metric in simple-root coordinates, the real spectral-plane projector is

\[
\Pi_r=\frac2{30}\sum_{k=0}^{29}
\cos(2\pi rk/30)C^k.
\]

This has rank two and is orthogonal for the Cartan metric because C preserves that metric. It need not be Euclidean-symmetric in the simple-root coefficient basis. Choosing an orthonormal basis of its image gives actual Coxeter-plane coordinates. A three-dimensional display combines explicitly selected projected coordinates; camera perspective is a rendering choice and does not add a dimension to the root system.

For the energy view, every two-parameter section is a positive quadratic surface obtained by holding the other two coordinates fixed. Completing the square determines its center and positive curvature. Level sets around the section minimum are ellipses; diagonalization of the exact Gram matrix, evaluated numerically, determines their axes. Normalizing each basis function by its own L2 norm gives a correlation matrix with unit diagonal and makes sliders comparable despite the different powers of pi in the raw basis. The energy must still be converted using the same normalization: changing a display scale is not changing the integral.

A Gaussian connection is available with a precise limit on its interpretation. Since H is positive definite, the standard integral over R^4 of exp(-t^T Ht/2) is (2pi)^2/sqrt(det H). This is the ordinary Gaussian volume associated with this four-dimensional Gram form. It is not a statistical fit, an identification of a physical partition function, or a formal equivalence to a model elsewhere in the repository without an explicit map and hypotheses.

An automatic tour changes the actual parameters and follows the same data path as manual controls. The AP, AR, KP, and KR scalar products are exposed by mixed states and their quadratic coefficients. The log-square challenge is the state (0,1,0,0). The orthogonality direction is the literal combination 3A+10K. These give reproducible mathematical meanings to the animation.

## Exact values, independent quadrature, and honest display

The UI evaluates the closed Gram matrix in floating-point arithmetic. Its symbolic labels retain the exact coefficients, but displayed decimals are rounded approximations. The proof of exactness is the analytic derivation above, not the number of digits shown by a browser or an apparent visual match between two curves.

Independent integration works in theta and splits at pi/15, 7pi/15, 11pi/15, and 13pi/15. Within each subinterval, the fourth-order endpoint map theta=l+(r-l)q(s), with q(s)=s^4/[s^4+(1-s)^4], moves the logarithmic endpoints to s=0,1 while its Gacobian vanishes there. The transformed squared-log terms behave like s^3(log s)^2 near an endpoint and remain integrable. An endpoint-free Gauss-Legendre rule therefore evaluates the density without sampling an infinite logarithm. Comparing two quadrature orders gives an empirical discrepancy indicator; it is not a rigorous enclosure of the integration error. It is independent of evaluating t^T Ht, and a nontrivial mixed parameter vector exercises every cross term at once.

A plot samples finitely many values. It may cap its vertical display near a logarithmic spike to keep the rest of the graph legible. Such a cap belongs solely to the drawing, and must not be used as a cutoff in the energy computation. The accumulated-area view integrates the nonnegative squared response, so it is monotone, while the unsquared response may change sign. The total area must agree with the exact matrix evaluation within the stated numerical discrepancy.

Exports should retain the four parameters, basis normalization, exact Gram labels, numerical matrix, quadrature method and order, selected spectral exponent, and software source identity. This lets a saved view be reconstructed as a mathematical observation, rather than preserving only a camera angle.

## Proof boundary and references

The earlier release's three Lean modules contain 102 audited finite theorems: 61 in CoxeterPhaseBridge, 15 in PhaseFiber, and 26 in RaghavaInduction. They cover the integral Coxeter-cyclotomic bridge, finite phase sums and transport, and rational first-moment induction identities. The newly added logarithmic Gram identities, Fourier boundary arguments, golden-module determinant calculation, and browser quadrature do not acquire Lean status by using the same matrix. The appendix makes no new kernel-verification claim. The exact integer checks and independent numerical tests have their usual computational meaning.

The analytic inputs are classical Bernoulli Fourier expansions (NIST DLMF 24.8), elementary Fourier Parseval theory, quadratic Gauss sums and Dirichlet L-functions (DLMF 25.15), and beta integrals (DLMF 5.12). Raghava's Arcsine kernels, inverse-binomial harmonic sums, and classical hypergeometric transformations, arXiv:2607.09904v2, supplies the motivating kernel and moment language already attributed in the earlier reader. The cyclotomic and actual E8 matrix conventions are those of the repository's e8_periods.py and CoxeterPhaseBridge.lean. No claim of historical novelty is needed for this exact synthesis.

Primary links: https://dlmf.nist.gov/24.8 ; https://dlmf.nist.gov/25.15 ; https://dlmf.nist.gov/5.12 ; https://arxiv.org/html/2607.09904v2 .

<!-- INTEGRAL_STUDIO_SUPPLEMENT_END -->
