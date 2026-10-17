# Recovered complete Raghava generating engine

The authoritative analytic source is K. Srinivasa Raghava, *Arcsine kernels, inverse-binomial harmonic sums, and classical hypergeometric transformations*, arXiv:2607.09904v2, revised October 15, 2026: https://arxiv.org/html/2607.09904v2. This module implements its second and supplementary generating families with exact rational coefficients. It restores the mathematics retained in the published PerfectPower integral browser after transient workspace maintenance removed the unpushed local files. Every one of the browser's 130 saved family records agrees exactly with the reconstructed Python output, including its harmonic coordinates, insertion weights, zeta coordinates, strict-sign annotation, and provenance. The restored module is `python/perfectpower/raghava_generating.py`; its focused structural tests are `python/tests/test_raghava_generating.py`.

## Common harmonic coordinates and normalization

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

## Explicit complete coefficient formulas

For $A=4^k$, define

$$C_{k,j}=-\frac1{72\,36^j}+\frac{1-A}{18\,9^j}+\frac1{8\,4^j}+\frac{A-1}{2}+\frac{A(6-A)}{9(2-A)}(4/9)^j+\frac{A(3A-2)}{2-A}4^j.$$

For $T=A/(2-A)$, define

$$D_{k,j}=\frac{T+1}{9\,9^j}+\frac{2T+3-4/A}{8\,4^j}+\frac{4/A-1}{72\,36^j}+\frac1{8A\,16^j}-\frac1{72A\,144^j}.$$

The exact scalar values are

$$S_m=\sum_{j=0}^m(-1)^j\lambda_{m-j}(\pi/3)^{2m-2j}C_{m-j,j}\zeta(2j+3),$$

$$B_m=\sum_{j=0}^m(-1)^j\lambda_{m-j}(\pi/3)^{2m-2j}D_{m-j,j}\zeta(2j+3).$$

For example, $S_0=5\zeta(3)/3$, $B_0=\zeta(3)/2$,

$$S_1=\frac{19}{54}\pi^2\zeta(3)-\frac{77}{18}\zeta(5),\qquad B_1=\frac1{162}\pi^2\zeta(3)-\frac7{108}\zeta(5).$$

The supplementary multiplier is independently tested by convolving the sine-normalization and cosine Taylor series, including the half-angle relation. This test checks a second construction of the coefficients rather than replaying the multiplier formula.

## Generators and the six-resolvent identity

The entire generators are

$$U_j(x)=\sum_{n\ge1}\frac{H_{jn}}{n^2\binom{2n}{n}}\prod_{k<n}(1+x^2/k^2),\qquad j=1,2.$$

Write $Z(x)=\sum_{k\ge1}1/[k(k^2+x^2)]$ and $c=\cosh(\pi x/3)$. Raghava's master relation is

$$4U_1(2x)+2cU_2(x)=-\frac{c}{36}Z(x/6)+\frac{c-1}{9}Z(x/3)+\frac c4Z(x/2)+(1-c)Z(x)+\frac{8c^2+2}{9}Z(2x/3)+(8c^2-6)Z(2x).$$

Near zero, $Z(x)=\sum_{j\ge0}(-1)^j\zeta(2j+3)x^{2j}$. The master therefore turns six rational argument scales into all the exact coefficients above. The normalizing factor $a(x)=(\pi x/3)/\sinh(\pi x/3)$ obeys $a(2x)c=a(x)$, and the normalized left side has coefficients $S_m$. The implementation encloses left and right independently in both hyperbolic and oscillatory conventions. Its master evaluator retains $|x|<1/2$, the common disk of all resolvent expansions. It never evaluates an individually singular resolvent and asserts that the finite result follows from cancellation.

The direct $U_j$ evaluator instead accepts real rational $|x|\le16$. It computes the original finite products. In the oscillatory convention it evaluates $U_j(ix)$ and correctly terminates when $x$ is a nonzero integer; for instance, $U_1(i)=1/2$ and $U_2(i)=3/4$. The normalization evaluator permits hyperbolic $|x|\le32$ and sine $|x|<3$, stopping before the latter's first pole. These domains are evaluator budgets; the entire functions themselves are not confined to them.

## Formal normal forms and preservation of the earlier 120 identities

At fixed weight $2M+3$, use the formal coordinate vectors $\pi^{2(M-j)}\zeta(2j+3)$. The vectors $\pi^{2(M-k)}S_k$ give a triangular basis because their diagonal is

$$(-1)^k\frac{72\,144^k+40\,16^k+9\,9^k-1}{72\,36^k}\ne0.$$

`canonical_second_basis` performs exact back substitution and reconstructs the original coordinate vector. It accepts arbitrary homogeneous rational input through $M=32$. Uniqueness is a formal statement about coefficient vectors; it does not assume algebraic or numerical independence of odd zeta values. Equal vectors prove an expression identity, while unequal vectors do not prove that the resulting real numbers are unequal.

For the two-selected-order construction, put $1\le r<s$, $D=b_{r-1}b_{s-1}$, $A=D+b_{r-1}+b_{s-1}$, and

$$\kappa=(\pi/3)^{2s-2r}\lambda_{s-1}/\lambda_{r-1}.$$

Its value is exactly

$$S_{s-1}+DB_{s-1}-\kappa(S_{r-1}+DB_{r-1}).$$

This equality holds before summation: each relevant $b$ satisfies $b+D(1+b^{-1})=A$. All 120 retained pairs $1\le r<s\le16$ are checked against the earlier independent Lidstone/Fourier implementation, matching the harmonic polynomials, harmonic insertion constants, and complete zeta evaluations.

## Rational enclosures and global bounds

`family_partial` computes the original inverse-binomial summands as a polynomial in $\pi^2$ and bounds its entire signed omitted tail. It uses $e_r(n)\le2^r/r!$, $H_{jn}\le jn$, $\binom{2n}{n}\ge4^n/(2n+1)$, and $\pi<22/7$. `family_interval` independently evaluates the finite zeta formula with rational Machin bounds for $\pi$ and positive Euler-transformed eta bounds for $\zeta$. If $K$ Euler terms are retained, the omitted eta tail is at most $2^{-K}$. Reversing the finite transform reduces its evaluation to $K$ weighted rational Dirichlet terms instead of a quadratic array of large rational differences. The two evaluations have no shared fitted decimal values.

For direct generator evaluation, the absolute product bound $\prod_{k<n}|1\pm x^2/k^2|\le3^{\lceil2x^2\rceil}$ gives an omitted tail at most $j3^{\lceil2x^2\rceil}4^{-N}$. Hyperbolic summands are nonnegative and give a one-sided enclosure; oscillatory summands use the absolute two-sided bound.

For $t\ge0$, define $V(t)=a(\sqrt t)U_2(\sqrt t)+2a(2\sqrt t)U_1(2\sqrt t)$. The cited complete-monotonicity theorem gives $(-1)^rV^{(r)}(t)>0$ and hence $(-1)^mS_m>0$. Taylor's integral remainder gives the global inequalities

$$\sum_{m=0}^{2N+1}S_mt^m<V(t)<\sum_{m=0}^{2N}S_mt^m\qquad(t>0).$$

Their validity does not require convergence of the infinite Taylor series at the chosen $t$. `global_taylor_bounds` independently encloses the coefficients first and applies these polynomial inequalities for any nonnegative rational $t$ within precision and degree budgets. `global_generator_interval` directly evaluates $V(t)$ by squared-parameter arithmetic for $0\le t\le64$, avoiding a numerical square root. Tests compare the independent bounds at $t=1,4,9$, beyond the initial local resolvent disk.

The exact arithmetic checks establish the implemented finite computations. The analytic theorems remain supported by the cited paper and the mathematical arguments above; the recovered engine does not claim Lean-kernel verification or a new independent hypergeometric summation principle.
