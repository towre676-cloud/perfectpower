# From branch topology to explicit differentials and period intervals

Subsequent Lean formalization now proves the finite/infinity regularity arithmetic, checks all 1,939 collision profiles and twelve saved full representative profiles, and proves convergence, the tail bound and formal differential equation for the Legendre series. The analytic normalization/basis-completeness and Euler-period identities remain open. See [the completed proof sweep](LEAN_BACKLOG_MONOGRAPH.md).

PerfectPower now computes actual algebraic holomorphic differential formulas on the compact complex normalization of a cyclic curve, rather than retaining only their dimension. It links those formulas to the existing genus, monodromy and period-contract layers. A second executable computes exact rational enclosures of the normalized periods of the real Legendre family. These are classical mathematical constructions made available as reproducible repo computations. This release adds no Lean source and does not claim new mathematical theorems. The positive-geometry Lean handoff remains assigned to the separate formalization session.

## The component equation

Start with a nonzero integer polynomial P and d between two and sixty-four. Write the monic squarefree blocks as F_r, with each distinct root in F_r having multiplicity r. Their coefficients are rational, and the existing exact Yun decomposition checks re-expansion. Put c=gcd(d, all root multiplicities), with c=d for a nonzero constant. The compact complex normalization has c components. On one component, after choosing a complex scalar, use the equation

\[
z^n=R(x),\qquad n=d/c,\qquad R(x)=\prod_r F_r(x)^{r/c}.
\]

This reduced monic equation describes every component up to isomorphism over the complex numbers. It is not a claim that each component or its scalar normalization descends to the rationals. The integer factor and signed-content information stays in the original geometry packet. Let e_a=r_a/c, M=deg R and delta=gcd(n,M). The existing ramification computation supplies the genus g. The differential constructor retains that independent value as a cross-check.

## A basis with every pole removed

For each character j from one through n-1, form the exact polynomial

\[
N_j(x)=\prod_a(x-a)^{\lfloor je_a/n\rfloor}
      =\prod_r F_r(x)^{\lfloor j(r/c)/n\rfloor}.
\]

The second expression computes the polynomial without approximating or splitting any roots. Write A_j=deg N_j. The resulting differential candidates are

\[
\omega_{i,j}=x^i N_j(x)\frac{dx}{z^j},\qquad
0\le i<h_j,\qquad
h_j=\max\left(0,\left\lfloor\frac{jM-nA_j-\delta}{n}\right\rfloor\right).
\]

Here is the regularity calculation. At a root a of reduced multiplicity e, let h=gcd(n,e). There are h places above a. A local parameter gives ord(x-a)=n/h, ord(z)=e/h and ord(dx)=n/h-1. Thus N_j dx/z^j has order

\[
\frac{n\lfloor je/n\rfloor+n-je}{h}-1
=\frac{n-(je\bmod n)}{h}-1\ge0.
\]

The inequality follows because h divides the remainder and that remainder is at most n-h. Multiplication by x^i creates no finite poles. If a=0, it adds ni/h to the order at each place over that root. If zero is unramified, it adds i at each of n points. The receipt separates the base finite orders from these additional zeros, recording their total degree ni.

At each of the delta places over infinity, ord(x)=-n/delta, ord(z)=-M/delta and ord(dx)=-n/delta-1. The order of the differential is therefore

\[
\operatorname{ord}_\infty(\omega_{i,j})
=\frac{jM-n(A_j+i)-n}{\delta}-1.
\]

The stated bound on i is exactly its nonnegativity condition. It also shows that the next monomial would have a pole. Within a character, independent polynomials of increasing degree give independent differentials. Distinct characters give independent eigenspaces. Conversely, expressing a meromorphic differential on the component in the cyclic function-field basis and imposing regularity forces the indicated numerator divisibility and infinity degree bound. This is the classical valuation description of the basis. The implementation checks that the number of produced forms equals g. It also checks, form by form, that the total divisor degree is 2g-2. These executable checks are exact rational and integer arithmetic; the analytic classification argument is documented here and is not a Lean theorem in this release.

For a squarefree polynomial of degree m, all e_a=1, so N_j=1 and h_j=floor((jm-gcd(d,m))/d). The construction reduces to the familiar superelliptic monomial basis. For y^2=x^5-x, it gives dx/y and x dx/y, with infinity orders two and zero. For y^2=(x-1)^2(x^5-x), it gives (x-1)dx/y and x(x-1)dx/y. Dividing y by x-1 on the normalization recovers the same two forms on the genus-two curve. Omitting that cancellation would give a pole and fail the regularity test.

For y^4=x^6, the two components have reduced equations z^2=x^3. Their compact normalizations have genus zero, and the basis is empty. This retains the distinction between a singular affine presentation and its smooth normalization. A nonzero constant gives d spheres and an empty basis on each.

## Character information useful for Jacobians

The component deck transformation z maps to zeta*z multiplies omega_{i,j} by zeta^{-j}. The packet labels the actual eigenvalue exponent modulo n. Its holomorphic dimension in that character is h_j. Complex conjugation reverses characters, so the complex first-cohomology dimension in the same character is h_j+h_{n-j}. The sums are g and 2g, respectively. This organizes future period calculations by symmetry without claiming that every character is already an algebraic Jacobian factor over a particular number field. Arithmetic descent and endomorphism-ring computation need additional arguments.

The constructor also provides a polynomial-coefficient differential equation for each form coefficient H(x)=N(x)/z(x)^j. On a local branch away from the roots,

\[
\left(nR(x)N(x)\frac{d}{dx}
+jR'(x)N(x)-nR(x)N'(x)\right)H(x)=0.
\]

It follows by differentiating z^n=R and using the product rule. The apparent zeros of the leading coefficient are retained; this is an equation on the local branch, not a claim of an everywhere nonsingular scalar connection. Tests clear denominators and replay the polynomial identity exactly. The differential itself is H dx. This supplies an explicit interface between algebraic regularity, deck transport and holonomic equations.

## Connecting the two existing atlases

The builder computes character packets for all 12,320 existing quartic/exponent profiles. It stores one full differential packet for each of the twelve root-multiplicity/exponent patterns, using an actual catalogue representative, and stores a per-equation character index. These full packets are representative formulas, not the actual numerator polynomial for every other curve of that pattern. The command-line constructor produces the full formulas for any requested input. The source catalogue hash ties the index to its coefficients.

The positive-geometry push added collision strata. For each saved stratum, this release computes the differential character dimensions on its normalized collision polynomial and cross-checks the genus and component count. Synthetic distinct cluster locations are used for this dimension calculation. The packet does not assert that those locations reproduce a metric degeneration, nor that differential spaces on the normalization are the complete limiting differential space of a stable curve. Node residues and dualizing differentials are separate work.

The normalize_in_basis function accepts a packet and exactly g supplied normalization conditions for one component. Rows of the supplied matrix are cycles, columns are the explicit differential forms. It reuses the existing exact period-contract solver to attach the correction coefficients to those actual forms. A rational test matrix does not become an analytic period matrix merely because it is invertible. The integration step must independently supply and justify the period data. Split components must be treated individually or assembled with an explicitly specified block system.

## An actual analytic family: Legendre periods

For the smooth real Legendre curve y^2=x(x-1)(x-lambda), with rational 0<lambda<1, the real cycle over [0,lambda] has period 2*pi*F(lambda). A complementary cycle oriented to give positive imaginary ratio has period 2*pi*i*F(1-lambda). Define the complete elliptic integral using the parameter convention, not the modulus convention:

\[
F(\lambda)=\frac{2K(\lambda)}{\pi}
=\sum_{k\ge0}a_k\lambda^k,\qquad
 a_k=\frac{\binom{2k}{k}^2}{16^k}.
\]

Substitution x=lambda*t in the real branch integral gives the Euler integral of F. Substitution on the complementary interval gives the second period. The factor two comes from traversing the return sheet of the closed cycle. This is the classical analytic identity underlying the computation. The explicit orientation fixes the sign of the imaginary period. The standard period ratio is tau=i*F(1-lambda)/F(lambda).

The program needs no floating-point integration. It uses the exact recurrence

\[
a_0=1,\qquad a_{k+1}=a_k\frac{(2k+1)^2}{4(k+1)^2}.
\]

All coefficients are positive and decreasing. If S_N is the sum through k=N-1, the omitted terms obey

\[
0\le F(\lambda)-S_N
\le a_N\frac{\lambda^N}{1-\lambda}.
\]

The proof compares every later coefficient with a_N and sums the geometric tail. The interval endpoints are rational numbers computed exactly. A separate enclosure is computed at 1-lambda. Positivity permits division of intervals: if A is the interval for F(lambda) and B that for F(1-lambda), then Im(tau) lies between B_lower/A_upper and B_upper/A_lower. The routine does not approximate pi; it reports the periods normalized by 2*pi, and tau itself has a rational enclosure of its imaginary part. At lambda=1/2 the two functions agree, so the exact mathematical ratio is i. The enclosing packet retains the computed interval around one as a useful replay of the bound.

Parameters zero and one are singular curves and are rejected by the period packet. The standalone series routine accepts zero, where it returns the exact interval [1,1]. Close to either singular endpoint, eighty terms can leave a wide interval; the saved error bound exposes that loss. The user may increase terms up to ten thousand. This is a rigorous mathematical enclosure under the Euler identity, not a Lean-certified analytic integration algorithm. The general compact-curve period solver remains open.

## Rebuilding and formalization boundary

Run `PYTHONPATH=python python -m perfectpower branched-geometry --coeff=0,-1,0,0,0,1 --d=2 --differentials` for the explicit genus-two packet. Run `PYTHONPATH=python python -m perfectpower legendre-period-bounds --lambda 1/2 --terms 80` for normalized Legendre period bounds. Coefficients run from constant upward. The optional k shift on branched-geometry is applied before constructing the differential basis.

Run `PYTHONPATH=python python python/build_holomorphic_basis.py` to rebuild the catalogue character index, representative bases, collision character index, examples and Legendre interval packets. The focused test file exercises squarefree degree/exponent grids, randomized repeated-root and split-component inputs, numerator cancellations, polynomial operator identities, exact normalization contracts and nested series enclosures. The full Python suite includes the parallel positive-geometry release.

The most direct Lean tasks are the finite valuation inequalities, the sum of character dimensions, the decreasing-coefficient recurrence and the geometric-tail estimate. Their analytic interpretations require the cyclic normalization, local parameter and Euler-integral theorems; they must not be hidden inside an assumption-free theorem name. No previous Lean certificate has been relabeled by this push. The separate positive-geometry handoff is preserved unchanged.

The standard squarefree basis and its role in period algorithms are described in Pascal Molin and Christian Neurohr, [Computing period matrices and the Abel-Jacobi map of superelliptic curves](https://arxiv.org/abs/1707.07249), Section 3.4. Their work goes substantially further, including rigorous integration and symplectic reduction. The repeated-multiplicity formula used here is derived above from normalization valuations. Our current contribution is the executable connection to this repository's existing arithmetic catalogue, collision data and exact operator machinery, with a concrete interval-computed analytic example.

The completed corpus contains 12,320 profile indices, twelve full representative bases, 42,846 differential dimensions summed across profiles, 1,939 collision-stratum packets and nine Legendre interval packets at eighty terms. The full Python suite passed 498 tests with four existing skips, and all eight focused tests passed. The separate existing quartic ledger remains at 2,686 checked lists, with 394 uncompiled; this release does not change that ledger.
