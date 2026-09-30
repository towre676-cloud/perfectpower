# L3(4) matched-selector theorem — v24 closure inside Wilson Forge

Let
\[
V=M(L_3(4))_{(2)}/2M(L_3(4))_{(2)}\cong\mathbb F_2^2.
\]
Formation v23 proves that a `4_1` selector line and a `4_2` selector line are matched exactly when their primitive characters have the same nonzero reduction in \(V\).  In the matched case they generate \(C_4\times C_2\), of order eight; in the transverse case they generate \(C_4^2\), of order sixteen.

The named ambient selectors are:

* `M22`: the index-22 outer extension is `L3(4).2_2`, and the lifted order-four cover is of type `4_1`;
* `U4(3)`: the relevant extension is `4_2.L3(4).2_3 < 4.U4(3).2_3`.

The remaining question is therefore whether outer types `2_2` and `2_3` have the same fixed nonzero line on \(V\).

## Theorem — the named selectors are matched

The outer automorphism group of \(L_3(4)\) is the dihedral group of order twelve, equivalently \(C_2\times S_3\).  CTblLib chooses `L3(4).2_1` as the normal order-two extension whose remaining outer factor is \(S_3\).  Thus `2_1` is the central outer involution.

In the standard multiplier marking used by v23, the outer element of order three cycles the three nonzero elements of \(V\).  Hence its image in \(GL(V)=GL_2(2)\cong S_3\) has order three.  The centralizer of this order-three subgroup in \(GL_2(2)\) is the subgroup itself, which has no nontrivial element of order two.  Since `2_1` is central and has order two, it follows that

\[
\rho(2_1)=1\quad\text{on }V.
\]

The two other involution types differ by `2_1` inside the outer Klein four subgroup, equivalently they are the same modulo the extension by `2_1`.  Therefore

\[
\boxed{\rho(2_2)=\rho(2_3)\text{ on }V.}
\]

Their common image is nontrivial: after quotienting by the central `2_1`, it is a transposition in the faithful \(S_3\cong GL_2(2)\) action.  A transposition of \(GL_2(2)\) has exactly one fixed nonzero vector.  Any primitive order-four selector extending through the corresponding outer involution has mod-two reduction on that fixed line.  Hence the `M22` `4_1` selector and the `U4(3)` `4_2` selector have the same nonzero mod-two reduction.

By v23's mod-two criterion they are matched.  Consequently

\[
\boxed{
\langle L_{M_{22}},L_{U_4(3)}\rangle\cong C_4\times C_2,
\qquad
|\langle L_{M_{22}},L_{U_4(3)}\rangle|=8.
}
\]

For Wilson Forge this means that the two named ambient channels jointly expose exactly

\[
\boxed{8/16}
\]

Schur frequencies, not 16/16.

## What this does not prove

This closes the relative marking of the named ambient `4_1` and `4_2` selector lines.  It does **not** compute the still-open internal even 2-primary induced maps
\[
M(A_6)_{(2)}\to C_4^2,
\qquad
M(L_3(2))_{(2)}\to C_4^2.
\]
Those remain two explicit induced-\(H_2\) rows.

## Source audit

The external label facts used here are the current CTblLib/ATLAS conventions for `L3(4).2_1`, `L3(4).2_2`, `L3(4).2_3`, the `M22.2` index-22 subgroup, and the `4_2.L3(4).2_3` subgroup of `4.U4(3).2_3`.  The multiplier marking and matched/transverse criterion are imported from the byte-preserved formation-polarization-theorem v23 package.
