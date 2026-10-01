# Salvage from old notes

An archive of 43 text files was reviewed for material that PerfectPower can check exactly. This
page records what was kept, what was corrected, and where each piece now lives. The review's
checks were re-run here (`python/tests/test_archive_salvage.py`).

## Kept, as exact regression examples

| source | content | check |
|---|---|---|
| `galois.txt`, `galois2.txt` | a 4×4 determinant of powers of the golden ratio $\varphi$, including negative powers | equals exactly $335$, computed with integer pairs in $\mathbb{Z}[\varphi]$ |
| `padov.txt` | forward and backward Padovan recurrences | $P(n+3)=P(n+1)+P(n)$ for $-98\le n<98$; the plastic-number unit $\alpha^{-1}=\alpha^2-1$ for $\alpha^3=\alpha+1$ |
| `feigen.txt` | finite-difference filter weights | the five-point derivative weights satisfy the moment equations for degrees 0 to 4 exactly, and a perturbed weight fails |
| `integ.txt` | an integral the notes call intractable | closed form below; Simpson quadrature agrees to $10^{-6}$ (a numerical cross-check, not a certificate) |

The plastic-number order has one real embedding and unit rank one. The unit-generation machinery
here is for totally real cubic orders of rank two, so that example is a regression for arithmetic
only.

**The integral.** The complex factors multiply to $(1+ix^2)(1-ix^2)=1+x^4$. The weights satisfy
$1/(1+4^x)+1/(1+4^{-x})=1$, so symmetrizing removes them:

$$
\int_{\mathbb{R}}\frac{\cos^2(ax)}{(1+ix^2)(1+4^x)(1-ix^2)}\,dx
=\frac{\pi}{4\sqrt2}\Big(1+e^{-\sqrt2\,|a|}\big(\cos(\sqrt2\,|a|)+\sin(\sqrt2\,|a|)\big)\Big).
$$

## Corrected: powers from a projector certificate

**The false claim.** `Document.txt`, `SVD.txt` and `Buildit.txt` claim that singular values
determine powers. The matrix $\begin{pmatrix}0&1\\0&0\end{pmatrix}$ has singular values $1$ and
$0$, but its square is $0$.

**The fix** (`PerfectPower/PowerCertificate.lean`). A certificate is a matrix $P$ and a rational
$\rho<1$ with

$$
P^2=P,\qquad MP=PM=P,\qquad \lVert M-P\rVert\le\rho .
$$

Then:
- `pow_eq_of_projector`: in any ring, $M^k=P+(M-P)^k$ for $k\ge1$;
- `norm_pow_sub_le_of`: in any normed ring, $\lVert M^k-P\rVert\le\rho^k$.

The exact checker `python/perfectpower/power_certificate.py` accepts integers and fractions only,
and uses the induced $\infty$-norm (the maximum absolute row sum). The tests accept an oblique
projector, $P\neq P^{\mathsf T}$, and check 64 powers exactly. They reject a forged projector, an
understated $\rho$, a binary float and $\rho=1$.

Not yet done: a Lean decision procedure for the rational matrix conditions, and a consumer whose
observable and error contract this certificate would serve.

## Corrected, recorded as counterexamples

- **Decay.** $0.95^3\approx0.857$ is not negligible. Reaching $10^{-15}$ takes 674 steps.
- **Projected control** (`in.txt`). Projecting an input away from bad modes does not keep the
  state safe. With $A=\begin{pmatrix}0&0\\1&0\end{pmatrix}$, the safe input $(1,0)$ leads to the
  bad state $(0,1)$. The missing condition is $(I-P)AP=0$, together with conditions on the input
  map and disturbances.
- **Overlaps** (`roxy.txt`). On the filled triangle with $\mathbb{F}_2$ coefficients, every cocycle
  is a coboundary, so $H^1=0$. Odd parity means the cocycle condition fails; it does not mean a
  nontrivial class.
- **Localization.** $10\cdot\tfrac{30}{13}-23=\tfrac1{13}$, so
  $\mathbb{Z}[30/13]=\mathbb{Z}[1/13]$. The primes of the numerator are not inverted.

## Leads only

- `parametric.txt` is a published Autodesk paper on constraint generation for CAD. Whether its
  real-coordinate constraints fit this exact-arithmetic pipeline has not been assessed.
- The archive's speed-up claims are not supported by the exported material and are not repeated
  here.
