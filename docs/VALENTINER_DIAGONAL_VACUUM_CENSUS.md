# Exact diagonal link vacua and full-field stability

The canonical Valentiner link action has additional zero-energy minima beyond its scaled group-matrix branch. For generic real nonzero a and b, its complete complex diagonal F-flat census contains 108 nonzero matrices and the origin. A nonunitary family has a strictly positive full eighteen-real-field mass matrix at the declared benchmark. A common negative scalar mass favors this competing family over the nominated group alignment at first order. This is an exact vacuum-selection constraint, obtained without inserting a CKM angle or a golden coefficient.

The historical B5 input-audit obligation was to differentiate the actual scalar potential instead of treating a holomorphic sextic as an energy. That obligation is already closed in the canonical F-term calculation. This chapter extends the resulting genuine complex 3.A6 link action; it does not identify this representation with the signed-permutation B5 representation. The exact 52-operator scalar-loop proof is also already available in the exact-running chapter.

## Declared action and scope

The link K is an unconstrained complex three-by-three matrix with canonical Kahler metric. Matter, Higgs and source backgrounds vanish. The specified degree-six truncation is

\[
W=a\det K+b\overline{I}_6(K)+c(\det K)^2,\qquad V_F=\sum_{i,j}|W_{K_{ij}}|^2.
\]

The bar on the invariant denotes conjugated polynomial coefficients, not conjugated fields: W remains holomorphic. Parameters a, b and c are real in the previously checked CP convention, with a b nonzero. The generic count excludes c=-16b and c=-5b/2. These statements concern this isolated link sector and this truncation, rather than the complete coupled flavor model.

## The exact diagonal restriction

For K=diag(x,y,z), direct contraction of the stored sextic tensor gives the rational polynomial

\[
J=x^6+y^6+z^6+\frac{3}{2}\sum_{\rm sym}x^4y^2+4x^2y^2z^2.
\]

All sextic tensor entries have even coordinate populations. Every off-diagonal first derivative at a diagonal matrix therefore vanishes: changing a single input/output pair would require two incompatible parity populations. The receipt explicitly checks all nine first derivatives. Determinant and determinant-squared off-diagonal first derivatives vanish there too. Consequently solving the three derivatives of W restricted to the diagonal solves all nine complex F equations, rather than only constrained stationarity.

Let X=x squared, Y=y squared and Z=z squared. Subtracting weighted derivatives cancels both determinant terms:

\[
xW_x-yW_y=3b(X-Y)[2X^2+3XY+2Y^2+2Z(X+Y)+Z^2].
\]

The cyclic counterparts are checked as polynomial identities. A nonzero rank-one diagonal matrix is excluded by its nonzero sextic derivative. At a rank-two diagonal matrix with z=0 and x y nonzero, W_z=a x y is nonzero. Every nonzero diagonal solution therefore has full rank.

## Exhaustive ratio classification

If all three squared entries coincide, write the projective representative as (1,epsilon,delta), with both signs independently plus or minus one. The common radius obeys

\[
r^3=-\frac{a\epsilon\delta}{32b+2c}.
\]

Four independent projective signs and three nonzero cube roots give twelve distinct matrices. These are the familiar equal-square diagonal branch.

If exactly two squared entries coincide, choose their ratio to the third as (1,1,q). The remaining weighted-difference equation is

\[
2q^2+5q+5=0,\qquad q=\frac{-5\pm i\sqrt{15}}{4}.
\]

Writing p squared=q, representatives are (1,epsilon,delta p), allowing the three positions of the unequal entry. Since x J_x at (1,1,p) reduces to (15+13q)/2, their radius is

\[
r^3=-\frac{a\epsilon\delta p}{b(15+13q)/2+2cq}.
\]

Three positions, two q roots, four relative signs and three radial cube roots give 72 matrices. For real b nonzero and real c, the denominator cannot vanish: dividing it by q gives -3bq-b+2c, whose imaginary part is nonzero. Their singular-value ratios are 1,1,(5/2) to the one-quarter power. Thus these matrices are genuinely nonunitary up to scaling and cannot be scaled finite-group matrices.

If all squared entries are distinct, the differences of the bracket equations force X+Y+Z=0. Substitution then forces X squared+X Y+Y squared=0. The squared ratios are therefore the two orders of (1,omega,omega squared), with omega a primitive cube root. Representatives can be taken as (1,epsilon omega,delta omega squared), or with omega and omega squared interchanged. They obey

\[
r^3=-\frac{a\epsilon\delta}{5b+2c}.
\]

Two orders, four signs and three radial cube roots give 24 matrices. Their invariant-to-determinant-squared ratio is 5/2, whereas the group branch has ratio 16. These are additional scaled-unitary solutions, not members of the original group-matrix branch.

The three mutually exclusive cases exhaust the ratios. None use x, y or z equal to zero. Together with the origin, this proves the generic count of 109 distinct diagonal F-flat matrices. At c=-16b the twelve equal-square matrices disappear, leaving 97 including the origin. At c=-5b/2 the 24 distinct-square matrices disappear, leaving 85. The assumptions a b nonzero remain necessary in both exceptional cases.

## Independent finite-algebra count

At a=b=1 and c=0, an independent rational grevlex Groebner calculation gives 27 basis polynomials, pure-power bounds 5,9,13 and exactly 125 standard monomials in the three-variable gradient quotient. The receipt retains every basis polynomial, leading exponent and standard monomial. Each nonzero diagonal solution has nonsingular diagonal Jacobian, as witnessed by the three-by-three diagonal Hessian determinants and the sign/permutation symmetries of J. The exhaustive 108 nonzero simple roots therefore leave diagonal local multiplicity 17 at the origin. Multiplicity refers to the three-variable diagonal algebra; it is not the multiplicity of the full nine-variable origin.

## Full-field mass certificates

The calculation differentiates the original tensor, not merely J, to produce all 81 entries of the complex nine-by-nine superpotential Hessian. Parity separates a three-dimensional diagonal block from three two-dimensional blocks on the off-diagonal pairs (12,21), (13,31) and (23,32). Determinant terms respect the same blocks. At F flatness with canonical kinetic terms, scalar mass-squared eigenvalues are the squared singular values of this Hessian, each repeated twice. Thus a nonzero full Hessian determinant proves a strict local minimum in all eighteen real link coordinates.

At the benchmark a=b=1,c=0, divide the Hessian by r to the fourth power. The equal-square representative has diagonal determinant 497664 and all three off-diagonal determinants -5184. Its singular values are 96 once and 72 eight times, agreeing with the previously derived singlet/octet formula.

The distinct-square representative has diagonal determinant 4860, but each off-diagonal block has determinant zero and rank one. Its exact full complex rank is six. Its singular values are 63 three times, 18 twice, 15 once and zero three times. It is a global zero-energy minimum of the isolated nonnegative F-term potential, but quadratic analysis does not prove isolation. Higher-order behavior in its three complex massless directions is not inferred from a vanishing determinant.

For the two-equal-square representative with the positive imaginary q root, the diagonal determinant is (304965+15795 i sqrt(15))/16. The first off-diagonal determinant is (891-243 i sqrt(15))/2; the other two are (1215-3159 i sqrt(15))/4. All four are exactly nonzero in the stored algebraic field. The nine normalized singular values are approximately 76.8405 twice, 68.4516 once, 40.0015 twice, 36 once, 18 twice and 15.7776 once. This provides an exact full-field stability certificate for a competing nonunitary minimum. Numerical enumeration checks ranks of all 108 sign, permutation and radial copies; the exact certificate states its representative and benchmark explicitly.

Every listed F-flat solution has V_F=0 and hence globally minimal energy for the isolated link F-term action. This energy statement does not establish a full-matrix census, uniqueness, cosmological occupation, or stability after coupling the link to nonzero source backgrounds. The origin also has zero energy and nine complex modes without quadratic mass.

## A universal scalar mass does not rescue the original selection

Consider the symmetry-allowed CP-even soft perturbation delta V=m_soft squared times Tr(K dagger K). At a=b=1,c=0, the cubes of the squared Frobenius norms N=Tr(K dagger K) on the three branches are

\[
N_{\rm equal}^3=\frac{27}{1024},\quad N_{\rm distinct}^3=\frac{27}{25},\quad N_{\rm nonunitary}^3=\frac{145+46\sqrt{10}}{160}.
\]

Their squared norms are approximately 0.297638,1.02599 and 1.21990 respectively. The exact ordering follows already from sqrt(10)>3. Positive mass favors the origin at first order. Negative mass favors the nonunitary family over both scaled-unitary families among these diagonal F-flat solutions. The strict nonunitary and equal-square minima persist under sufficiently small perturbations by the implicit-function theorem; their leading energy shifts are the displayed mass term. The massless branch requires separate perturbative analysis, but its leading norm does not overturn the nonunitary competitor's advantage. This is a first-order comparison of the specified vacua, not a theorem classifying the perturbed full matrix potential globally.

The concrete mechanism constraint is therefore stronger than local stabilization of a selected group frame: an interaction must distinguish that frame from an explicit, equally F-flat, fully stable nonunitary competitor. A common scalar mass alone supplies the wrong preference. Neither the 66-degree CKM phase, physical CP selection nor the golden relation follows from this census.

## Executable verification

Run `python python/develop_valentiner_diagonal_vacua.py` to reproduce the complete scientific receipt. Run `python -m pytest -q python/tests/test_valentiner_diagonal_vacua.py python/tests/test_valentiner_susy_vacua.py` for ten focused checks. The new checks enumerate 108 distinct roots at three generic parameter points, test all transverse F derivatives and the full Hessian against the original tensor evaluator, inspect the full ranks of all benchmark copies, independently compare every branch norm, and replay the exact rank and quotient witnesses. A fresh checkout reproduction retains the receipt byte for byte.
