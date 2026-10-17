# Coxeter Mellin traces: a complete real-zero classification and a weight tuner

The E8 cancellation extends to a classification covering every irreducible reduced crystallographic root system. The extension also supplies a tunable family: for any integer weight k at least two, a suitable B or C root system has an exactly vanishing Mellin integral at weight k. At weight four the rank is seven, and the logarithmic companion is the particularly simple value minus pi to the fourth times log two divided by 5145. These are derived identities with exact computational support. No claim of priority, a higher categorical colimit, or a Lean proof is made.

## From an actual Coxeter lift to the spectrum

Work over the complex numbers. Let G be a connected simple algebraic group, T a maximal torus, R its root system, r its rank, h its Coxeter number, c a Coxeter element in the Weyl group, and g any lift of c in the normalizer of T. The elementary-looking distinction between a permutation of roots and the adjoint action on root spaces matters: g can multiply root vectors by scalars as it permutes their root spaces. A dimension match alone does not identify their spectra.

Adams and He, *Lifting of elements of Weyl groups*, Proposition 5.1.1, give the needed theorem: the h-th power of g is the principal central involution. Its adjoint action is therefore the identity. Their section 5.1 also records that Coxeter elements are regular. These standard Lie-theoretic results are cited inputs to the following argument, not new results of the Python calculation.

Choose a regular Coxeter eigenvector v with primitive eigenvalue zeta_h. If a root alpha were fixed by c to the power d, invariance of the pairing would give

\[
(1-\zeta_h^{-d})\langle\alpha,v\rangle=0.
\]

Regularity means that the second factor does not vanish, so h divides d. Every root orbit thus has exactly h members. There are r such orbits because the root count is rh. On one orbit, choose a nonzero root vector X and use X, Ad(g)X, ..., Ad(g)^(h-1)X as a basis. The vectors belong to distinct root spaces, and Ad(g)^h X=X. In that basis the action is the regular h-cycle, including its closing coefficient. This resolves the possible root-vector signs and scalars.

On the Cartan subalgebra the eigenvalues are zeta_h to the reflection exponents m_1,...,m_r. Consequently the adjoint eigenvalue multiset consists of r full h-cycles together with those r Cartan eigenvalues. The resulting dimension is r(h+1), the dimension of the simple Lie algebra. A different central quotient of G has the same adjoint representation and the same trace.

The exact module independently constructs the simple reflections, their Coxeter product, reflection closure of the simple roots, and the actual root orbits. It compares the integer matrix characteristic polynomial against the polynomial obtained from the stated exponents. This finite evidence checks the implemented data, while the cited theorem and preceding argument establish why those data describe the adjoint spectrum.

## The Mellin identity

Let C denote that finite-order adjoint operator. Its resolvent trace kernel is

\[
K_R(x)=\operatorname{Tr}\bigl(C(I-xC)^{-1}\bigr),\qquad 0<x<1.
\]

For complex s with real part greater than one, the geometric series and the classical polylogarithm Mellin integral give

\[
Z_R(s):=\frac{1}{\Gamma(s)}\int_0^1(-\log x)^{s-1}K_R(x)\,dx
=\zeta(s)\,r h^{1-s}+\sum_{j=1}^r\operatorname{Li}_s(\zeta_h^{m_j}).
\]

The condition on s controls the possible 1/(1-x) singularity from the eigenvalue one. It also justifies absolute convergence of the series used in the derivation. The identities concern the normalized integral Z_R; a raw integral has the additional Gamma(s) factor. The code keeps that normalization explicit.

The regular-cycle contribution follows from summing a complete root-of-unity fiber. The exceptional exponent contributions reduce by the same divisor filters already used by the E8 and cyclotomic engines. Since the spectrum is rational, the final coefficient of zeta(s) is a finite combination of real positive bases to the power 1-s. At integer weights every such coefficient is rational.

## The complete classification for real s greater than one

Write t=s-1, so t is positive. For each type the following table gives a positive scale times Z_R(s)/zeta(s). Since zeta(s) and the omitted scale are positive for real s>1, the displayed numerator alone determines the sign and zeros.

| Type | Coxeter number h | Displayed numerator | Positive denominator | Unique real zero s>1 |
|---|---:|---|---|---|
| A_n, n>=1 | n+1 | n+1-(n+1)^t | (n+1)^t | 2 |
| B_n or C_n, n>=2 | 2n | n+1-2^t | (2n)^t | 1+log(n+1)/log(2) |
| D_n, n>=4 | 2(n-1) | n+1-2^t-(2^t-1)(n-1)^t | [2(n-1)]^t | 2 |
| E6 | 12 | 6-(3^t-1)(4^t-2^t+1) | 12^t | 2 |
| E7 | 18 | 7-(2^t-1)(9^t-3^t+1) | 18^t | 2 |
| E8 | 30 | 8-(2^t-1)(3^t-1)(5^t-1) | 30^t | 2 |
| F4 | 12 | 4+(2^t-1)(3^t-1) | 12^t | none |
| G2 | 6 | 2+(2^t-1)(3^t-1) | 6^t | none |

Here n is the rank, and the standard irreducibility ranges remove the low-rank repetitions. The B1 and C1 boundary case is A1 and is included separately by the tuner when k=2. Noncrystallographic finite reflection groups and nonreduced root systems are outside this classification.

For A the numerator is strictly decreasing and is zero at t=1. For D, both subtracted terms are strictly increasing and positive for t>0; the value at t=1 is n+1-2-(n-1)=0. For E6, both positive factors in the product are strictly increasing: the derivative of 4^t-2^t is log(2)(2*4^t-2^t), which is positive. For E7 the same argument applies to 9^t-3^t. For E8 all three positive factors are strictly increasing. In each exceptional E case the product takes the value r at t=1. Thus A, D and E have a positive normalized trace for 1<s<2, exactly one zero at s=2, and a negative normalized trace for s>2.

For B and C the numerator decreases strictly from n to minus infinity, and its sole zero solves 2^t=n+1. F4 and G2 have positive numerators for every t>0 and no real zero in this domain. This proves completeness of the real-zero classification once the displayed finite reductions are established. It says nothing about zeros at nonreal s.

## Recovering the reductions from exponent fibers

For A_n the Cartan exponents are all nonzero residues modulo h=n+1. Their polylogarithm sum is (h^(-t)-1)zeta(s). Adding the n regular cycles gives the A numerator in the table.

For B_n and C_n the exponents are all odd residues modulo 2n. The full 2n-fiber minus the even n-fiber gives ((2n)^(-t)-n^(-t))zeta(s). Adding n regular cycles gives

\[
Z_{B_n}(s)=Z_{C_n}(s)
=\zeta(s)n^{1-s}\left((n+1)2^{1-s}-1\right).
\]

For D_n the odd residues modulo 2(n-1) occur together with the additional exponent n-1. That extra exponent must be counted even when it duplicates an odd exponent. Its polylogarithm is Li_s(-1)=(2^(-t)-1)zeta(s). This gives the displayed D formula. Omitting the duplicate exponent in even rank would produce a false answer.

For E6 the exponents modulo 12 comprise the primitive 12th roots and the two primitive cube roots. For E7 the exponents modulo 18 comprise the primitive 18th roots and the additional phase -1. For E8 all eight exponents are primitive modulo 30. The divisor filters respectively give the three factorizations in the table. F4 and G2 have the primitive exponents modulo 12 and 6; after adding their regular cycles the surviving product has a plus sign. These statements can be checked entirely through rational cyclotomic polynomials and integer Coxeter matrices, without floating eigenvalue calculations.

## Prescribing the vanishing weight

For any integer k>=2 set

\[
n=2^{k-1}-1.
\]

Then the B_n and C_n zero occurs at exactly s=k. This is an infinite family in the mathematical statement. The implementation accepts arbitrary integer weights within a caller-visible rank bit budget and computes n symbolically without allocating rank-n matrices. The default budget allows 4096-bit ranks, hence target weights through 4097. Increasing the explicit budget extends the implementation range; the theorem itself has no such ceiling.

The corresponding rational kernel has an elementary closed form:

\[
\boxed{K_n(x)=n\,\frac{(2n+1)x^{2n-1}-x^{n-1}}{1-x^{2n}}.}
\]

One way to see this is to use the Cartan characteristic polynomial u^n+1. Its resolvent trace is -n*x^(n-1)/(1+x^n). The n regular Coxeter cycles contribute 2n^2*x^(2n-1)/(1-x^(2n)). Combining denominators gives K_n. The kernel changes sign once on (0,1), at x=(2n+1)^(-1/n); the Mellin weight controls how its positive and negative portions balance.

Differentiating the unnormalized Mellin integral at the tuned zero gives a logarithmic companion. The Gamma derivative and zeta derivative terms disappear because they multiply the vanishing factor. What remains is

\[
\boxed{\int_0^1(-\log x)^{k-1}\log(-\log x)K_n(x)\,dx
=-\Gamma(k)n^{1-k}\zeta(k)\log 2.}
\]

This derivative identity is valid for the exact tuned n. The normalization is essential: the formula includes Gamma(k), unlike the derivative of the normalized Z. Since n>0 and zeta(k)>0, the logarithmic companion is strictly negative.

At k=4, n=7, the actual B7 and C7 adjoint spectra have dimension 105 and Coxeter number 14. Their common kernel is

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

At k=3 the rank is three, so B3/C3 already provide a weight-three cancellation with logarithmic companion -2*zeta(3)*log(2)/9. At k=8 the rank is 127. These examples make the scaling cost visible: choosing a larger vanishing weight grows the required rank exponentially, even though the symbolic factor remains compact.

## Exact implementation and reproducibility

The implementation is `python/perfectpower/coxeter_mellin.py`. Its `zeta_factor(family, rank, s)` returns the exact rational coefficient of zeta(s) at integer weight s. `even_pi_coefficient` converts an even-weight trace to its rational coefficient of pi^s. `bernoulli_pi_coefficient` independently sums Bernoulli polynomials over every root-cycle and Cartan phase. The comparison does not reuse the closed zeta-factor reduction.

`cartan_matrix`, `roots`, `coxeter_matrix`, and `root_orbits` construct the finite geometry in simple-root coordinates through rank sixteen. `geometry_receipt` checks the root count, the actual orbit partition, the exact order of the Coxeter matrix, and its characteristic polynomial against the exponent polynomial. An independent B/C calculation starts with the Euclidean roots plus or minus e_i plus or minus e_j and the axial roots, then applies the signed coordinate cycle e_i to e_(i+1), e_n to -e_1. It obtains n complete 2n-cycles without using the Cartan closure. E8 root coordinates and its operator also agree exactly with the earlier dedicated E8 module. The complete receipt has 64 geometry cases: A1 through A16, B2 through B16, C2 through C16, D4 through D16, and the five exceptional systems.

`bc_zero_tuner(k)` returns the tuned rank, dimension, Coxeter number and normalization as a JSON-safe record. A rank-bit guard protects allocation of the rank integer. `zeta_factor` and `bc_kernel` separately check exact-exponentiation budgets before constructing large rational powers. Those resource limits are explicit implementation limits, not restrictions on the identities.

Run the independent focused checks with `PYTHONPATH=python python3 -m unittest python/tests/test_coxeter_mellin.py -v`. The tests cover all 64 finite geometries, five even Bernoulli weights on 27 systems, exact E8 agreement, tuning at every integer weight from 2 through 128, the 4096-bit rank boundary, the weight-four logarithmic value, and the B/C rational kernel. The exact finite computations use the Python standard library and the existing rational polynomial machinery. They do not invoke numerical root finding or require SymPy.

## Sources and scope

Jeffrey Adams and Xuhua He, *Lifting of elements of Weyl groups*, [arXiv:1608.00510](https://arxiv.org/html/1608.00510v1), section 5.1, Proposition 5.1.1, supplies the central power of a Coxeter lift; section 1 defines the central principal involution. The application to the root-space cycles is the argument given above.

Mark Reeder, *Cyclotomic structures on root lattices*, [author-hosted paper](https://www.math.utah.edu/~ptrapa/math-library/reeder/reeder-cyclotomic-root-lattices-2008.pdf), section 3.2, relates reflection exponents to cyclotomic spectra and gives exceptional exponent data. The implemented matrices and roots provide an independent finite check of the displayed data.

The [NIST Digital Library of Mathematical Functions, section 25.12](https://dlmf.nist.gov/25.12), supplies the standard polylogarithm Mellin representation and root-of-unity identities. The reductions, sign argument, and zero tuner in this note are derived from these inputs. A separate literature study would be needed before asserting that the classification or a particular presentation is new. No equation here identifies unrelated 240-dimensional objects, proves the Claude artifacts' proposed categorical colimit, or establishes a physical E8 model.
