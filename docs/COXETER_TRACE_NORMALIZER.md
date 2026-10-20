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
