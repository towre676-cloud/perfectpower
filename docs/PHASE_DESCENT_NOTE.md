# Exact phase descent, linear morphisms, and the 384–264–240 bridge

The recovered implementation is `python/perfectpower/phase_descent.py`. It makes a precise portion of the earlier categorical and cyclotomic aspirations executable. It constructs a finite linear category with actual matrices, a conductor colimit with its ordinary universal property, the induction–restriction adjunction on actual Hom spaces, and an injective family of full complex Mellin traces. These results do not assert the existence of an unspecified higher category, a new E8 adjoint identification, or a categorical equivalence merely from matching dimensions. All arithmetic checks here are exact Python computations, rather than Lean proofs.

## Canonical phase classes and their colimit

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

## Actual linear objects and morphisms

A `PhaseSpace` is a finite rational vector space with a rational phase grading,

\[
 V=\bigoplus_{q\in\mathbb Q/\mathbb Z}V_q,
 \qquad \dim_{\mathbb Q}V_q\in\mathbb Z_{\ge0}.
\]

Each graded piece has a fixed ordered basis. A `PhaseLinearMap` is an actual collection of rational matrix blocks \(f_q:V_q\to W_q\). The constructor checks every matrix dimension and forbids blocks between distinct phases. Identity maps are identity matrices. Composition is matrix multiplication. Direct sum uses block diagonal matrices, tensor product uses the graded Kronecker construction, and duality reverses the arrow, transposes each matrix, and negates its phase. When distinct phase pairs have the same tensor-product grade, the implementation preserves their separate basis positions; it does not merge different vectors simply because their grades coincide.

The underlying rational-vector-space functor is faithful: assembling the blocks into an ordinary matrix retains every block entry. It is generally not full, since an arbitrary underlying linear map may mix distinct phases. Passing from `PhaseSpace` to its `PhaseClass` records dimensions and forgets morphisms; this decategorification is not a faithful functor. Two unrelated maps can have the same source and target class.

This is a split rational spectral model. After complexification, one can attach the finite-order operator acting by \(e^{2\pi iq}\) on the grade \(q\). A phase \(1/3\) does not mean that multiplication by a primitive cube root is already a rational scalar on a one-dimensional ordinary rational representation. Rational forms of actual cyclic representations impose additional Galois conditions. The distinction prevents the convenient rational block model from being mistaken for every representation category over \(\mathbb Q\).

The finite categories embed fully faithfully as the conductor grows, because phase-preserving inflation introduces no new grades between old objects and no new matrix blocks. Every finite object and every finite collection of its matrix morphisms therefore occurs at a common finite stage. This explains the concrete directed-union category used here. It supplies no higher cells or higher-categorical universal property beyond this ordinary construction.

## Induction, inflation, and Frobenius reciprocity

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

## Full complex Mellin traces and exact recovery

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

## Reproduction and scope

Run `PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_phase_descent.py -v` from the repository root. The checks include canonical conductor equality, finite cocone overlap and uncovered-phase rejection, actual matrix identities and compositions, contravariant duality, direct sums, tensor bifunctoriality with colliding grades, induction versus inflation, induction/restriction functoriality, explicit Frobenius inverse maps and both naturality directions for 28 cyclic inclusions, exact DFT inversion across 37 conductors up to 64, full-complex orientation, and the artifact-conductor root-order factorization.

`descent_receipt()` returns a compact JSON-safe summary for the live research feed. Its claim is an ordinary exact finite linear construction and its proved conductor descent. The relation to higher-category drawings remains a precisely stated classical realization; the drawings alone do not supply associators, higher morphisms, coherence laws, or an E8 representation-theoretic identification.
