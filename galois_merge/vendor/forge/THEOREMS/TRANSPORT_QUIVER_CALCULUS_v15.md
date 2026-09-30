# Transport quiver calculus — v0.15

Let \(A=\operatorname{End}^{*}(Q6)_{\mathbb Q}\) be the characteristic-zero star-compatible five-context transport algebra.  The exact carrier sequences from v0.13 have

\[
0\to K_+\to V_+\to C_+\otimes\mathbb Q^5\to0,
\qquad (\dim K_+,\dim C_+)=(1,2),
\]

and

\[
0\to K_-\to V_-\to C_-\otimes\mathbb Q^5\to0,
\qquad (\dim K_-,\dim C_-)=(15,3).
\]

After choosing splittings, every element of \(A\) has the unique block form

\[
T_+=\begin{pmatrix}a&b\\0&I_2\otimes S\end{pmatrix},\qquad
T_-=\begin{pmatrix}A&B\\0&I_3\otimes S\end{pmatrix},
\]

with
\[
a\in\mathbb Q,\quad A\in M_{15}(\mathbb Q),\quad S\in M_5(\mathbb Q),
\quad b\in M_{1\times 10}(\mathbb Q),\quad B\in M_{15\times15}(\mathbb Q).
\]

The dimension count is
\[
1+10+225+225+25=486,
\]
which equals the exact characteristic-zero dimension already proved in v0.13.  Hence every displayed parameter occurs and the block description is exact.

## Theorem 1 — Radical-square-zero structure

The Jacobson radical is

\[
J=\left\{(a,A,S,b,B):a=A=S=0\right\}
\cong M_{1\times10}(\mathbb Q)\oplus M_{15\times15}(\mathbb Q),
\]

so

\[
\boxed{\dim J=235,\qquad J^2=0.}
\]

The semisimple quotient is

\[
\boxed{A/J\cong \mathbb Q\times M_{15}(\mathbb Q)\times M_5(\mathbb Q).}
\]

This corrects the v0.14 shorthand that called the full 450-dimensional kernel of the minus projection a “radical.”  That kernel contains the full semisimple \(M_{15}\) block and is only a row-kernel ideal.  The true Jacobson radical has dimension 235.

## Theorem 2 — Morita basic algebra

The plus radical bimodule has dimension 10 and is two copies of the simple \((\mathbb Q,M_5)\)-bimodule.  The minus radical bimodule has dimension 225 and is three copies of the simple \((M_{15},M_5)\)-bimodule.  Therefore \(A\) is Morita equivalent to the radical-square-zero path algebra of the quiver

\[
\text{row}\;\overset{2}{\longrightarrow}\;\text{plus},
\qquad
\text{row}\;\overset{3}{\longrightarrow}\;\text{minus},
\]

with all paths of length at least two zero.  Its basic algebra has

\[
\boxed{3\text{ vertices}+5\text{ arrows}=8\text{ dimensions}.}
\]

Thus the 486-dimensional matrix algebra is a matrix amplification of an eight-dimensional basic quiver algebra.

## Theorem 3 — Functorial compression of the degree-nine wall

Let \(K_{9,-}\) be the exact-length-nine coefficient space that vanishes after projection to the minus algebra.  Then

\[
\dim K_{9,-}=37.
\]

The remaining plus defect maps onto the complete 11-dimensional row-kernel of the plus algebra, giving an exact sequence

\[
\boxed{0\to H_{26}\to K_{9,-}\to N_+\to0,}
\qquad
(26,37,11).
\]

Hence the 26 homogeneous degree-nine syzygies are exactly the kernel of this one-sided defect map.

For the filtered 386-dimensional boundary, let \(N_-\) be the 450-dimensional minus row-kernel.  In an adapted splitting

\[
N_-\cong \operatorname{End}(K_-)\oplus\operatorname{Hom}(V_-/K_-,K_-),
\qquad 225+225.
\]

The old 64-dimensional boundary \(B_{64}\) projects injectively with rank 64 to each summand and is therefore the graph of an isomorphism between two 64-dimensional subspaces.  Consequently

\[
\boxed{
0\to\operatorname{Hom}(V_-/K_-,K_-)\to N_-/B_{64}
\to \operatorname{End}(K_-)/U_{64}\to0,
}
\]

with dimensions

\[
225\to386\to161.
\]

Dually the two 225-dimensional factors can be exchanged.  Therefore

\[
\boxed{412=26+386=26+225+161.}
\]

The 412 degree-nine rules are not a new intrinsic representation species.  They are the shadow, in the frozen two-generator presentation, of the tiny radical-square-zero quiver calculus above.

## Evidence boundary

The characteristic-zero block structure follows from the exact rational carrier identities and dimensions already established in v0.13.  The frozen prime \(p=1{,}000{,}003\) is used to construct and independently verify adapted bases, the degree-nine defect sequence, the 64-dimensional graph subspace, and all stated ranks.  No claim is made that the presentation-dependent 64-dimensional subspaces have a canonical basis over \(\mathbb Q\).
