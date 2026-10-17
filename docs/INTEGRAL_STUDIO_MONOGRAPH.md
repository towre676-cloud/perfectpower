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
