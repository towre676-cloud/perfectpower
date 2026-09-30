# Characteristic-zero transport gluing and the degree-eight M5 wall — Forge v0.13

Let `L=L_Q6` be the exact integral primitive relation matrix of the species-3 base object, with five context blocks ordered `E,RX,RY,LX,LY` and star dimensions `(11,30)`.  Write `F_+ : Q^11 -> (Q^5)^5` and `F_- : Q^30 -> (Q^5)^5` for the vertically stacked plus/minus block maps.

## Exact context tensor factors

The exact integer matrix satisfies

- `E_+ = 0`, `RX_+ + LX_+ = 0`, `RY_+ - LY_+ = 0`;
- `RX_- - LX_- = 0`, `RY_- + LY_- = 0`.

Hence `im F_+` lies in `C_+ tensor Q^5`, where `C_+` has dimension 2, and `im F_-` lies in `C_- tensor Q^5`, where `C_-` has dimension 3.  At the frozen prime `p=1000003`, the stacked ranks are exactly 10 and 15.  A nonzero modular minor is a nonzero integer minor, so the rational ranks are at least 10 and 15; the tensor-factor identities give matching upper bounds.  Therefore

`im F_+ = C_+ tensor Q^5`, `im F_- = C_- tensor Q^5`.

The kernels have dimensions 1 and 15.

## Rational fiber product

For either star sign, the row action `S in M5(Q)` acts on `C_± tensor Q^5` as `1 tensor S`, so every `S` lifts through `F_±`.  Once one lift is chosen, all other lifts differ by an arbitrary linear map from the source into `ker F_±`.  Thus

`dim A_+ = 25 + 11*1 = 36`,
`dim A_- = 25 + 30*15 = 475`.

Consequently the characteristic-zero star endomorphism algebra is

`End^*(Q6)_Q ~= A_+ x_{M5(Q)} A_-`

and has dimension `36+475-25=486`.

The defining integral transport system has rank 560 both over `Q` and modulo `p`, so `p` is a good reduction point for the kernel.  Reduction from the localized kernel over `Z_(p)` onto the 486-dimensional modular algebra is surjective.

## Two generators and characteristic-zero word filtration

The frozen modular generators `g,h` of v0.12 therefore admit lifts `g~,h~` to the localized characteristic-zero algebra.  Word-rank cannot decrease when passing from their modular reductions to characteristic zero.  Since the formal word counts give the opposite upper bound and the ambient algebra has dimension 486, the characteristic-zero filtration is exactly

`1,3,7,15,31,63,127,255,486`.

Hence `g~,h~` generate `End^*(Q6)_Q`; there is no relation through degree 7, and the first filtered relation space has dimension 25 in degree 8.  The common centralizer of the reductions has dimension one, so the characteristic-zero common centralizer has dimension at most one.  Scalars give equality, and because `g~,h~` generate, `Z(End^*(Q6)_Q)=Q`.

## The degree-eight relation wall is the M5 gluing quotient

Let `F_{<=7}` be the span of words through degree 7 and `F_8` the 256-dimensional homogeneous degree-8 word space.  The lifted pair has

`rank ev(F_{<=7})=255`, `rank ev(F_8)=256`, `rank ev(F_{<=8})=486`.

Therefore

`E_8 := ev(F_8) cap ev(F_{<=7})`

has dimension 25.  Let `R_8=ker(ev:F_{<=8}->A)`; then `dim R_8=25`.  Since `ev|F_8` is injective, taking the degree-8 leading term and evaluating it defines an isomorphism

`beta:R_8 -> E_8`.

Let `sigma:A->M5(Q)` be the common row-action quotient.  The package computes at the good prime that `sigma|E_8` has rank 25.  Good reduction of the filtered relation module lifts this nonzero 25x25 determinant to characteristic zero.  Hence

`boxed:  sigma o beta : R_8 ~= M5(Q)`.

This is the precise sense in which the 25-dimensional first relation wall *is* the M5 gluing quotient.  It is a filtered vector-space identification attached to the chosen two-generator presentation and common row-action quotient.  It is **not** an algebra isomorphism: the 25-dimensional overlap `E_8` is not closed under multiplication.  The construction is natural under invertible homogeneous `GL2` changes of the generator pair.

The release freezes a modular normalization in which the 25 boundary images are the 25 matrix units of `M5`.
