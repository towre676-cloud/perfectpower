# The actual E8 adjoint Coxeter lift

This note restores the exact E8 construction described in the retained deep integral monograph after transient workspace maintenance removed its unpublished source. The reconstruction has been recomputed from the saved mathematical specification, and its present tests and arithmetic receipts are fresh. Its purpose is to settle a specific mathematical condition: the earlier root-permutation-plus-Cartan integral model has the same cyclic representation as an explicitly constructed **actual inner automorphism of the E8 Lie algebra**. Root-space signs are computed from brackets; they are not discarded or inferred from the number 248.

The implementation is `python/perfectpower/e8_lift.py`. It reuses the 240 actual E8 roots, fixed simple system, Cartan matrix, and Coxeter ordering in `e8_periods.py`. Everything is sparse exact integer arithmetic, with exact fractions available for nonintegral exponential parameters. This is an executable mathematical construction in Python, not a Lean-kernel theorem.

## The cocycle and the Lie algebra

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

All other root brackets vanish. This is the classical simply-laced Frenkel–Kac construction in the negative opposite-root normalization. Geck's Theorem 3.3 and Example 3.4 describe this construction; the cocycle here is chosen explicitly instead of importing a sign table. The root decomposition and connected E8 Cartan matrix identify the resulting complex Lie algebra as E8.

In particular, the normalized simple triples are

$$E_i=e_{\alpha_i},\quad F_i=-e_{-\alpha_i},\quad H_i=h_i,$$

$$[E_i,F_i]=H_i,\qquad [H_i,E_i]=2E_i,\qquad [H_i,F_i]=-2F_i.$$

The sign of $F_i$ matters. A lift built with the wrong middle exponential would not be the Weyl lift claimed below.

## Finite exponentials and Tits lifts

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

## The signed Coxeter orbits

Use the same ordering as the geometric root action:

$$N=n_8\cdots n_1,$$

where $n_1$ acts first. Its restriction to the Cartan is the existing eight-dimensional Coxeter matrix with characteristic polynomial

$$\Phi_{30}(X)=X^8+X^7-X^5-X^4-X^3+X+1.$$

The actual lifted action has 128 negative root images. The deterministic signed root-space orbit data are:

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

Every primitive 30th-root eigenvalue has multiplicity nine, and every other 30th-root eigenvalue has multiplicity eight. The program separately verifies $N^{30}=I$ and rules out each proper divisor of 30 as its order. Adams–He, Proposition 5.1.1, provides the independent group-theoretic order explanation: a Coxeter lift to the Coxeter number gives the principal central involution, which is trivial for E8.

There is an independent height-spectrum comparison. Count the simple-root heights of all 240 actual roots modulo 30 and add eight Cartan eigenvalues of phase zero. Every one of the resulting 30 multiplicities equals the lifted spectrum above. In the root-length-two normalization, half the positive-root sum has squared length $\|\rho\|^2=620$; the 120 positive-root heights sum to 1240 and their squares sum to 18600. These three values are recomputed from coordinates, and do not come from the signed cycles.

## The adjoint integral and its nonzero logarithmic derivative

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

## Fresh reproduction and scope

Run `PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_e8_lift.py -v` for the eight tests. Run `PYTHONPATH=python python3 -m perfectpower.e8_lift --exhaustive` to recompute the complete JSON receipt. Without `--exhaustive`, the receipt explicitly marks the large root-pair, Jacobi, and lift-bracket counts as unexecuted, while still recomputing the lifts, signed cycles, gauge, Tits relations, traces, height comparison, and order.

The full checks comprise 248 alternating basis values, 30,628 skew-symmetry basis pairs, all 57,600 ordered root-pair cocycle signs, all 2,511,496 distinct unordered basis triples for Jacobi, and all 245,024 simple-lift bracket-preservation pairs. Alternation and trilinearity extend the checked Jacobi identities to repeated indices and all vectors. The full bracket-preservation checks include zeros. The tests additionally check all 240 root exponentials, all eight simple reflection actions, eight normalized $\mathfrak{sl}_2$ triples, the exact Tits relations, and the actual Coxeter spectrum.

This resolves the actual E8 adjoint-lift condition for the stated spectral integrals. It does not identify the separate 240-dimensional field-conjugate fiber with the 240 E8 root spaces, provide the categorical trace 264, or prove unspecified higher-category claims in the motivating visualizations. Those require their own constructions. Classical provenance is retained and no historical novelty claim is made for the Lie construction or its integral specialization.

Sources: Meinolf Geck, [On Lusztig's canonical bases of simple Lie algebras](https://arxiv.org/html/2602.19632v1), Theorem 3.3 and Example 3.4; Jeffrey Adams and Xuhua He, [Lifting of elements of Weyl groups](https://arxiv.org/abs/1608.00510), Proposition 5.1.1. Root coordinates, Coxeter geometry, and analytic normalizations are documented separately in `e8_periods.py` and the integral monograph.
