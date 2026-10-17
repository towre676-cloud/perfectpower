# The cyclotomic integral studio: exact mathematics and numerical meaning

This studio studies one defined positive quadratic form. Every plotted density,
phase, coefficient and ellipsoid comes from that form. Its new analytic
identities below have mathematical proofs and independent numerical checks.
They are not being represented as new Lean results. The repository's earlier
Coxeter, phase-fiber and induction theorems remain a separate formal layer.

## The master integral

Put

\[
Q_\pm(x)=4x^2+(1\mp\sqrt5)x-\frac{3\pm\sqrt5}{2},\qquad
Q(x)=Q_+(x)Q_-(x)=16x^4+8x^3-16x^2-8x+1.
\]

Let \(u(x)=\pi^2/4-(\arcsin x)^2\), and define

\[
A=\log|Q|,\quad K=\log|Q_+/Q_-|,\quad
P=u^2,\quad R=u^2(u+\pi^2/2).
\]

For real \(a,b,c,d\), the object being visualized is

\[
\mathcal E(a,b,c,d)=\int_{-1}^{1}
\frac{(aA(x)+bK(x)+cP(x)+dR(x))^2}{\sqrt{1-x^2}}\,dx
=\mathbf t^T G\mathbf t,
\qquad \mathbf t=(a,b,c,d)^T.
\]

Under \(x=\cos\theta\), \(0\leq\theta\leq\pi\), the measure becomes
\(d\theta\), and \(u=\theta(\pi-\theta)\). Thus the plotted transformed
density is exactly \((aA+bK+cP+dR)^2\); it has no additional Jacobian.
The four interior logarithmic singularities are at
\(\theta=\pi\{1,7,11,13\}/15\). They are ordinary improper integrals:
\(\log^2|\theta-\theta_0|\) is locally integrable. Their pointwise heights
are unbounded, and a display may crop their visible height without changing
the formula or numerical integral.

## The complete exact Gram matrix

Write \(L_s=L(s,\chi_5)\), where the real primitive character modulo five
takes values \(0,1,-1,-1,1\) on residues \(0,1,2,3,4\). Then

\[
G=\begin{pmatrix}
\dfrac{8\pi^3}{45}&-\dfrac{4\pi^3}{75}&
\dfrac{832\pi}{1125}\zeta(5)&\dfrac{157976\pi}{28125}\zeta(7)\\[5pt]
-\dfrac{4\pi^3}{75}&\dfrac{8\pi^3}{15}&
\dfrac{41\pi\sqrt5}{54}L_5&\dfrac{1825\pi\sqrt5}{324}L_7\\[5pt]
\dfrac{832\pi}{1125}\zeta(5)&\dfrac{41\pi\sqrt5}{54}L_5&
\dfrac{\pi^9}{630}&\dfrac{4\pi^{11}}{3465}\\[5pt]
\dfrac{157976\pi}{28125}\zeta(7)&\dfrac{1825\pi\sqrt5}{324}L_7&
\dfrac{4\pi^{11}}{3465}&\dfrac{101\pi^{13}}{120120}
\end{pmatrix}.
\]

Off-diagonal contributions to \(\mathcal E\) occur twice, for example
\(2acG_{AP}\). The exact gradient is \(\nabla\mathcal E=2G\mathbf t\).
The orthogonality challenge follows immediately:
\(\langle A,3A+10K\rangle=3G_{AA}+10G_{AK}=0\). Equivalently,
the second factor is \(\log|Q_+^{13}/Q_-^7|\).

The form is strictly positive for every nonzero real parameter vector. To see
linear independence, logarithmic coefficients at a root of \(Q_+\) and then
at a root of \(Q_-\) force \(a+b=a-b=0\). The remaining relation
\(cP+dR=0\) forces \(c+d(u+\pi^2/2)=0\) on an interval of \(u\), hence
\(c=d=0\). The positivity is an analytic fact, independent of the numerical
eigensolver. Numerically its eigenvalues are approximately
\(0.06164909,5.03904724,16.25496961,2489.49615516\).

## Why the constants appear

Let \(c_q(n)\) denote the Ramanujan sum. The two logarithms have cosine
series in \(L^2(0,\pi)\):

\[
A(\cos\theta)=-\sum_{n\ge1}\frac{c_{30}(n)}{n}\cos(n\theta),\qquad
K(\cos\theta)=-\sqrt5\sum_{n\ge1}
\frac{\chi_5(n)c_6(n)}{n}\cos(n\theta).
\]

Indeed \(\log|\cos\theta-\cos\alpha|=-\log2-
2\sum_{n\ge1}\cos(n\theta)\cos(n\alpha)/n\). Summing the four roots
gives the primitive-thirtieth-root trace; subtracting the two golden sectors
gives its quadratic Gauss sum. Parseval applies to these \(L^2\) functions.
Since \(c_3(n)^2=1+3\mathbf1_{3\mid n}\), it gives

\[
\langle A,A\rangle=\frac\pi2\zeta(2)
\prod_{p\mid30}\left(2-\frac2p\right)=\frac{8\pi^3}{45},
\]

\[
\langle K,K\rangle=\frac{5\pi}{2}
(1-5^{-2})(1+3^{-1})\zeta(2)=\frac{8\pi^3}{15}.
\]

For the mixed entry, the character vanishes on multiples of five, so
\(c_{30}(n)c_6(n)\chi_5(n)=-c_3(n)^2\chi_5(n)\). Therefore

\[
\langle A,K\rangle=-\frac{\pi\sqrt5}{3}L(2,\chi_5)
=-\frac{4\pi^3}{75},\qquad
L(2,\chi_5)=\frac{4\pi^2}{25\sqrt5}.
\]

The Bernoulli polynomial identities supply the selectors:

\[
P(\theta)=\frac{\pi^4}{30}-3\sum_{k\ge1}\frac{\cos(2k\theta)}{k^4},
\qquad
R(\theta)=\frac{\pi^6}{42}-\frac{45}{2}
\sum_{k\ge1}\frac{\cos(2k\theta)}{k^6}.
\]

The mean of each logarithm is zero. Pairing these series gives, for
\(m=2,3\) and \(P_2=P,P_3=R\),

\[
\langle A,P_m\rangle=
\frac{(2m)!\pi}{2^{2m+1}}
(1-3^{-2m})(1-5^{-2m})\zeta(2m+1),
\]

\[
\langle K,P_m\rangle=
\frac{(2m)!\pi\sqrt5}{2^{2m+1}}
(1+3^{-2m})L(2m+1,\chi_5).
\]

Finally, \(\int_0^\pi u^k\,d\theta=
\pi^{2k+1}(k!)^2/(2k+1)!\). Expanding \(P^2,PR,R^2\) proves the last
three rational multiples of powers of \(\pi\). These ten calculations prove
the entire master integral.

## The actual spectral connection

For the existing integral E₈ Coxeter matrix \(C\), its characteristic
polynomial is \(\Phi_{30}\) and its eigenphases are
\(2\pi e/30\), \(e=1,7,11,13,17,19,23,29\). The exact identities are

\[
e^{4i\theta}Q(\cos\theta)=\Phi_{30}(e^{i\theta}),\qquad
\det((2x+2)I-(2I+C+C^{-1}))=Q(x)^2.
\]

The two quadratics divide the phases by \(\chi_5(e)=\pm1\). In particular
\(H=I+C^6+C^{24}\) has eigenvalues
\((1+\sqrt5\chi_5(e))/2\), so \(H^2=H+I\). Thus the golden split is an
operator relation, not a decorative choice of coefficients. It does not by
itself identify arbitrary E₈ objects or supply a new physical theory.

The logarithmic determinant expansion
\(\log\det(I-zC)=-\sum_{n\ge1}\operatorname{Tr}(C^n)z^n/n\)
is valid for \(|z|<1\); boundary logarithms here follow in \(L^2\).
Finite trace recurrences connect this spectrum to the repository's exact
linear-machine and inverse-binomial work. These links describe the stated
operators and sequences, without asserting that every associated analytic
function has a finite rational realization.

## Numerical implementation and test boundary

`web/integral-studio/math-engine.mjs` uses stable sine-factor logarithms
rather than subtracting nearly equal cosines. Independent integration splits
at all four roots. On each interval it applies Gauss–Legendre quadrature after
the map \(q=t^4/(t^4+(1-t)^4)\); this makes endpoint logarithmic stiffness
vanish cubically. It does not integrate the closed-form Gram expression.

All calculations use JavaScript binary64, roughly fifteen significant digits.
The displayed difference of two quadrature orders is an error indicator, not
a rigorous interval bound. Direct samples do not resolve infinite peak
heights. The test suite independently checks every Gram entry, signed mixtures,
partial integrals at singular boundaries, stable roots, exact Fourier
coefficients, gradients, and the symmetric eigensystem. Run it with
`node --test web/integral-studio/math-engine.test.mjs`.
