# Transport solution category theorem — Forge v0.12

At the frozen good prime `p=1,000,003`, let `A = End^*(Q6)` denote the full linear solution space of triples `(S,T_+,T_-)` satisfying all five raw star-transport equations for the species-3 carrier.  Direct nullspace computation gives `dim A = 486`.

## Fiber-product structure

The three coordinate projections have exact image dimensions

`dim A_S = 25`, `dim A_+ = 36`, `dim A_- = 475`,

while the combined `(T_+,T_-)` projection is injective.  Their kernels have dimensions `461,450,11`, respectively, and the one-sided kernels map to zero under `S`.  Consequently the row-action map is a common full quotient `M_5(F_p)` and

`A ~= A_+ x_{M_5(F_p)} A_-`.

This is an exact finite-field algebra statement, not a numerical embedding.

## Two-generator transport ISA

A deterministic exact pair `g,h in A` (seed `202619`) generates all of `A`.  The cumulative span of binary words in `g,h` through lengths `0,...,8` has dimensions

`1,3,7,15,31,63,127,255,486`.

Thus there is no linear word relation through degree 7.  The 511 formal words through degree 8 have a 25-dimensional exact relation space.  The package freezes both a 486-word basis and the 25 relation vectors.

The common centralizer of `g,h` inside `A` has dimension one.  Since `g,h` generate `A` and scalars are central, `Z(A)=F_p`.

## Positive component as a functorial category

For `Q_i in {Q6,Q7,Q57,Q58,Q107}`, choose the exact v0.11 gauge `w_i:Q_i -> Q6` (identity for `Q6`).  Then every morphism space is identified with the same algebra by

`Phi_ij(a) = w_j^{-1} a w_i`.

All 25 Hom spaces are therefore 486-dimensional and composition is transported to multiplication in `A`:

`Phi_jk(b) o Phi_ij(a) = Phi_ik(ba)`.

The release checks all 125 object-triple coherence identities directly on the raw five-block matrices.

## Degeneracy divisor

An element is an isomorphism precisely when `S,T_+,T_-` are all invertible.  Hence the nonunit locus is

`Delta(a)=det S(a) det T_+(a) det T_-(a)=0`,

where `Delta` has total degree 46 on the 486-dimensional affine solution space.  Because the identity has `Delta=1`, this is a proper Zariski-closed degeneracy locus.  The hard negative pairs `Q2/Q35` and `Q159/Q160` remain outside the input to this algebra: their characteristic-zero canonical-factor/projective-determinant semi-invariants are retained as the certified boundary data separating objects whose five-context shadows collide.
