# Rational two-isogenies on the actual elliptic point groups

PerfectPower 0.9.3 proves that the rational degree-two map and its normalized dual preserve Mathlib's elliptic-point addition. Their composition is actual doubling, including infinity and the exceptional affine points. The corrected index identity consequently applies to these actual maps. A separate theorem computes the doubling quotient from an explicit free-plus-finite group decomposition and applies that computation to these elliptic groups. This release does not prove the squareclass-to-quotient identification or construct the Mordell–Weil decomposition for the retained curves. The 99 numerical rank-zero results therefore retain their previous classical descent status; they have not become unconditional Lean rank theorems.

The source is in `PerfectPower/TwoIsogenyPointMap.lean`, `PerfectPower/TwoIsogenyDual.lean`, and `PerfectPower/DescentRankBridge.lean`. There are 42 audited theorem declarations. The gate accepts only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; there are no additional mathematical axioms or admitted proofs in these modules. Run `make isogeny-point-groups-kernel` with Lean 4.20.0 and the pinned Mathlib to reproduce the compilation, declaration audit, and five acceptance/rejection controls.

## The models and the exceptional points

Write

\[
E_{a,b}: y^2=x(x^2+ax+b),\qquad
E'_{a,b}: v^2=u(u^2-2au+a^2-4b).
\]

The hypotheses are rational coefficients, \(b\ne0\), and \(a^2-4b\ne0\). The `smooth` theorem proves directly that every rational solution on the first model is nonsingular. If the ordinate is nonzero, the derivative with respect to the ordinate is nonzero. At ordinate zero, the abscissa zero case uses \(b\ne0\). In the other case, simultaneous vanishing of the cubic and its derivative forces \(a^2-4b=0\), contradicting the hypothesis. The corresponding hypotheses for the isogenous model follow from

\[
(-2a)^2-4(a^2-4b)=16b.
\]

For an affine point with nonzero abscissa define

\[
X=x+a+b/x,\qquad Y=y(1-b/x^2).
\]

The arithmetic equation identity from the preceding release proves that this point lies on the target curve; nonsingularity then supplies an actual Mathlib point. Infinity maps to infinity. An affine point with abscissa zero maps to infinity, and the curve equation forces its ordinate to be zero. Thus `phi_eq_zero_iff` identifies the full set-theoretic kernel as exactly infinity and \(T=(0,0)\). After `phiHom` is constructed, this is the kernel of an additive group homomorphism.

The sign in the ordinate formula matters. On \(E_{0,3}\), the point \((1,2)\) maps to \((4,-4)\). Its normalized dual image is \((1/4,-7/8)\), agreeing with doubling. The negative controls reject the reversed ordinate signs.

## Addition compatibility, including tangents

The proof begins with addition by \(T\). Mathlib's group law gives

\[
(x,y)+T=(b/x,-by/x^2).
\]

Substitution shows that this translation leaves both isogeny coordinates unchanged. The theorem `phi_add_T` proves the equality of actual points, and `phi_add_of_kernel` covers any summand in the kernel. Negation compatibility is proved separately.

For two nonkernel affine points whose sum is not infinity, let \(l\) be Mathlib's secant or tangent slope, \(n=y_1-lx_1\), and \(r\) the abscissa of their sum. The original chord intersects the cubic at the two summands and the negative of their sum. The `chord_roots` theorem extracts the coefficients of Mathlib's exact addition-polynomial factorization. It gives

\[
x_1+x_2+r=l^2-a,
\quad x_1x_2+x_1r+x_2r=b-2ln,
\quad x_1x_2r=n^2.
\]

The polynomial factorization counts roots with multiplicity. This is why the same argument covers the tangent case rather than assuming distinct abscissas.

When \(r=0\), the product identity forces \(n=0\), and the pair identity gives \(x_1x_2=b\). Substitution shows that the two image points are inverse points. Both sides of addition compatibility are therefore infinity.

When \(r\ne0\), the nonzero summand abscissas force \(n\ne0\). Put

\[
L=l-b/n,\qquad N=n-al+bl^2/n.
\]

The `image_line` theorem uses the original curve equation to show that each image lies on \(Y=LX+N\). The `image_root_sums` theorem transports the sum and pair of roots:

\[
X_1+X_2+X_r=L^2+2a,
\quad X_1X_2+X_1X_r+X_2X_r=a^2-4b-2LN.
\]

These identities determine the target secant or tangent. If the first two image abscissas agree, they have the same ordinate because they lie on the same line. The root identities give the derivative identity defining the tangent slope. Nonsingularity rules out an ordinate zero with derivative zero. This addresses the extra case in which distinct source points have the same image, as well as ordinary doubling. The theorem `line_slope` proves the needed target slope and excludes a vertical target line in this branch.

The image of the source sum has ordinate \(-Y_r\), while the target addition formula produces precisely that ordinate and abscissa \(X_r\). `phi_add` consequently proves addition compatibility for all actual points, without an addition-compatibility hypothesis. `phiHom` packages this proof as an additive group homomorphism.

## The normalized dual and doubling

Applying the same degree-two construction to the target curve produces the model with coefficients \(4a\) and \(16b\). Its coordinates return to the original model by

\[
(u,v)\longmapsto(u/4,v/8).
\]

`scaleBack_add` proves that this normalization preserves the actual group law. The slope divides by two, the abscissa by four, and the ordinate by eight. `rawDualHom` and `dualHom` then construct the raw and normalized dual homomorphisms. Coefficient transport is explicit and preserves the coordinates of affine points.

The `dual_phi` theorem proves that the normalized dual of the first image equals \(P+P\). Infinity is handled directly. The source point \(T\) maps to infinity and doubles to infinity. Other points with ordinate zero double to infinity, and their first image has abscissa zero, so the dual also maps them to infinity. For the remaining points, the first image abscissa is nonzero and both the normalized abscissa and ordinate agree with Mathlib's tangent addition formulas. The ordinate identity uses the curve equation and retains the required sign.

`dual_comp_phiHom` states the resulting equality of additive homomorphisms. `actual_doubling_index` applies the corrected subgroup-index theorem to these maps. Unlike the earlier generic bridge, this theorem no longer asks the caller to provide elliptic addition compatibility or dual composition.

## What the rank theorem proves and what remains

Let \(G\simeq F\times T_f\) be an explicit additive group isomorphism, where \(F\) is a finite free integer module and \(T_f\) is a finite additive group. The free part has

\[
|F/2F|=2^{\operatorname{rank}F}.
\]

For the finite part, the kernel and cokernel of doubling have equal cardinality. Product subgroups and transport by the isomorphism then give

\[
[G:2G]=2^{\operatorname{rank}F}|T_f[2]|.
\]

These are proved in `DescentRankBridge.lean`, using Mathlib's finite free-module quotient theorem and subgroup index results. Combining them with the actual elliptic maps \(\phi\) and \(\psi\) yields `elliptic_descent_rank`:

\[
[\operatorname{im}\phi+\ker\psi:\operatorname{im}\phi]\,
2^{\operatorname{rank}F}|T_f[2]|=
[E':\operatorname{im}\phi][E:\operatorname{im}\psi].
\]

The explicit decomposition is a structural mathematical input, rather than an assumed numerical rank equation. It has not been constructed here for the retained rational point groups. Also still required are the squareclass homomorphisms, the identification of their kernels with the respective isogeny images, the associated finite image bounds, and the torsion/kernel cardinality calculation leading to the customary divisor four. The prior primitive-cover restrictions provide arithmetic inputs to those image bounds. This release does not bypass these remaining steps or substitute finite candidate counts for proved group quotient sizes.

## Verification scope

The new gate recompiles all three modules, audits all 42 theorem declarations, accepts general actual addition and the correct normalized dual ordinate, and rejects both reversed ordinate signs and a dropped torsion factor. Evidence is bound to the exact module, audit, gate, and control sources by SHA-256. The installed wheel includes the three modules and their audit receipt. Earlier arithmetic evidence retains its original separate source binding. The complete historical release-verification suite is not asserted to have been rerun.
