# Arithmetic bridges for rational two-isogeny descent

PerfectPower 0.9.2 formalizes the arithmetic passage from rational points to primitive integral quartic covers, the exhaustiveness of local projective charts, both retained real-place exclusions, the rational isogeny coordinate identities, and the corrected group-index formula. These are separate mathematical statements. The exact axiom audit contains 2,651 theorem declarations. The arithmetic corpus contains 1,478 distinct excluded covers and 576 distinct rational curve models drawn from the 306 original two-isogeny packets. Each retained model has a theorem restricting its nonzero rational points to the surviving squareclasses. The numerical rank statement is not an unconditional theorem about the actual elliptic point group in this release.

## From a rational point to an integral cover

Consider the integral model

\[
 E_{a,b}: y^2=x(x^2+ax+b).
\]

The central theorem starts with a rational point satisfying this equation and the hypothesis that x is nonzero. It does not ask the caller for a squareclass, a divisor of b, an integral quartic witness, or a descent-dimension identity. It constructs integers d,u,v,w satisfying

\[
 d\text{ squarefree},\quad d\mid b,\quad u\ne0,\quad v>0,\quad \gcd(u,v)=1,
\]

\[
 x=\frac{du^2}{v^2},\qquad
 y=\frac{duw}{v^3},\qquad
 w^2=du^4+au^2v^2+\frac bd v^4.
\]

Here squarefree and coprime are genuine Mathlib predicates on integers. The sign of d is unrestricted. The constructed w retains the sign needed to reconstruct the original y. Consequently the theorem describes both points above a nonzero x-coordinate, including the case y=0. It does not lose a sign by replacing y with an arbitrarily chosen positive square root.

Squareclass extraction first applies the natural-number squarefree decomposition to the absolute value of a nonzero integer. A sign case supplies its signed integer representative. For a nonzero rational x, the integer to decompose is the product of its numerator and denominator. If this product is d times s squared, then x equals d times the square of s divided by the denominator. Normalizing that rational square root by its own reduced numerator and positive denominator supplies primitive u,v. This use of reduced fractions proves primitivity rather than assuming it.

A rational number whose square is an integer has denominator one: the denominator of its square is the square of its reduced denominator. The proof uses this denominator identity to produce an integer root. Applied to the actual curve equation after substituting x=du²/v², it makes the quantity yv³/u integral. Squarefreeness of d then forces that integer to be divisible by d, yielding the integral w without changing y's sign.

The delicate support step is d dividing b. Merely writing the quartic equation with b/d would assume the desired conclusion. Instead, the proof initially works with

\[
 dw^2=d^2u^4+adu^2v^2+bv^4.
\]

Let g be the integer gcd of d and v. Since g divides the squarefree d, g is squarefree. The displayed equation implies g squared divides dw squared, and the squarefree divisibility lemma forces g to divide w. Write d=gD, v=gV and w=gW. Cancellation of g squared gives an equation implying g divides D squared times u to the fourth power. Squarefreeness of gD proves g and D relatively prime, so g divides u. Primitivity of u,v makes g a unit. Thus d and v are relatively prime, and the original equation now forces d to divide b. Only after this proof is integer division by d used in the normalized quartic.

The exceptional point with x=0 is deliberately outside the nonzero chart. On this model its curve equation forces y=0. The identity point at infinity also requires the projective elliptic point representation and is not described as a finite rational pair.

## Finite candidate completeness

A signed squarefree divisor of a nonzero b has absolute value at most the absolute value of b. This bounds the integer search interval. To avoid delegating mathematical trust to a factorization routine, a finite certificate supplies candidate integers and a list of square-divisor tests. Squarefree d fails none of these nonunit square tests. Lean checks the finite implication that every bounded divisor passing those tests belongs to the candidate list. The tests need not be declared prime: their being at least two is enough for the squarefree implication, and the finite table proves that they suffice for the particular coefficient.

This separates discovery from verification. Python discovers the tests and emits the candidate list. Ordinary kernel-reduced finite decisions check the implication. A missing signed divisor, an inadequate square test, or an altered candidate list makes that implication fail. The generic rational-point theorem is then connected to this finite exhaustion proof.

For each retained model, excluded candidates are eliminated using the actual quartic equation of the constructed primitive cover. Remaining candidates are listed as survivors. A survivor is still unresolved by these sieves; it is not asserted to have a rational point, nor to be an element of a complete Selmer group. This distinction remains valid even though the restriction on every actual rational point is now formally proved.

## Prime-power charts are exhaustive

Fix a prime p and any natural exponent k. A primitive integer pair cannot have both coordinates divisible by p. A coordinate coprime to p remains coprime to p to the kth power, hence is a unit in ZMod of that modulus. This proves that at least one residue coordinate is a unit. The theorem includes k=0; the retained tables use positive depths.

Quartic homogeneity supplies the normalization identity. Multiplying u,v by t and w by t squared preserves the quartic equation. If v is a unit, choose its inverse and obtain the chart v=1 with arbitrary u. If v is not a unit, u must be a unit; normalizing u gives u=1 and a nonunit v. A product that is a unit has unit factors, so the second normalized v stays nonunit. No primitive residue branch is silently discarded.

The finite exclusion certificate checks that no square occurs in the first chart and that no square occurs in the second chart at a nonunit coordinate. The second table uses existence of a multiplicative inverse as a computable finite predicate. Its equivalence with being a unit is proved through the standard inverse criterion. Thus table evaluation is a finite decision inside Lean, while its applicability to every primitive integral cover follows from a general theorem.

The retained local obstructions use moduli 5, 7, 8 and 9. Their statements quantify over all integer u,v,w satisfying primitivity, rather than merely recording a list of modular survivors. The original integer equation is transported to the residue ring by the integer cast ring homomorphism, which is sufficient even though this cast is not injective.

## Both real-place exclusion branches

The quartic has the form d u to the fourth power plus a u squared v squared plus c v to the fourth power. Negative d and c, together with nonpositive a, make it negative whenever u or v is nonzero. This was the previously formalized branch.

The new branch admits positive a when its square is less than 4dc. Its proof uses the exact identity

\[
 4d(du^4+au^2v^2+cv^4)
 =(2du^2+av^2)^2+(4dc-a^2)v^4.
\]

If v is nonzero, the right side is positive, forcing the quartic to be negative because d is negative. If v is zero, the nonzero-u leading term is negative directly. Therefore it cannot equal w squared. These statements over rational coordinates are enough to refute rational points; a real analytic flow or an order completion is not required.

## Isogeny coordinates and group indices

The coordinate theorem proves that

\[
 X=x+a+b/x,\qquad Y=y(1-b/x^2)
\]

satisfy the isogenous equation with coefficients minus 2a and a squared minus 4b whenever x is nonzero and the original curve equation holds. A second theorem proves that the normalized dual x-coordinate equals

\[
 \frac{(x^2-b)^2}{4y^2}
\]

when y is nonzero. This is the expected doubling x-coordinate. These are identities for the actual rational coordinate formulas. They do not by themselves establish an elliptic-group homomorphism or define its values at exceptional points.

For additive-group homomorphisms f:G→H and g:H→G, the independent group theorem proves

\[
 [G:\operatorname{im}(gf)]
 =[H:\operatorname{im}(f)+\ker(g)]\,[G:\operatorname{im}(g)].
\]

The relative index of im(f) in im(f)+ker(g) supplies the correction between the first factor and the index of im(f). If the composition is a supplied doubling endomorphism, multiplying by that correction yields the exact corrected index relation. Kernel containment gives the simpler product formula as a separate theorem with an explicit containment hypothesis. It is never assumed without a premise. Mathlib's index convention also supports infinite groups; interpreting these natural-number indices as nonzero finite cardinalities requires finiteness hypotheses later.

## What still connects this to rank

The remaining group work is concrete: define the two isogenies on the actual rational elliptic point groups, cover the identity and rational two-torsion exceptions, prove addition compatibility and normalized dual composition as point-group maps, identify their kernels and the squareclass homomorphism images, and connect the finite doubling quotient to the Mordell–Weil rank and torsion contribution. The coordinate and index theorems are inputs to this work. They do not replace any of it with a renamed rank assumption.

In particular, the 99 retained rank-zero conclusions continue to depend on classical two-isogeny descent reasoning in the Python rank calculation. This release proves the arithmetic restrictions used by that calculation for the retained models. It does not mark those rank conclusions as unconditional Lean elliptic-group theorems.

## Reproduction and evidence

Run make descent-bridges-kernel with Lean and Mathlib 4.20.0. The gate regenerates all emitted modules and rejects byte differences, compiles the four hand-written modules and 39 generated modules in dependency order, then audits every theorem declaration. It rejects incomplete audit output, unexpected compiler output, custom axioms, sorryAx and native reduction axioms. Only propext, Classical.choice and Quot.sound are permitted. The receipt binds source files, the retained input corpus, generator and audit script by SHA-256.

Six acceptance and rejection controls check complete signed support, omission of negative support, the insufficiency of the unit-denominator chart alone, an altered isogenous coefficient and a reversed reconstructed y sign. Separate tests verify that each unique excluded cover and each distinct retained curve has its corresponding declaration and that saved hashes match the current files. Focused Python execution tests remain a separate form of evidence. The complete archive contains the repository, installed wheel and this monograph, and its independent ZIP parts must all be extracted into the same directory. This release does not claim that the full historical release-verification suite was rerun.

## Subsequent actual point-group proofs

PerfectPower 0.9.3 proves addition compatibility for both actual rational point-group maps, normalized dual composition as doubling, and the resulting corrected quotient index identity. See [the point-group monograph](ISOGENY_POINT_GROUPS_MONOGRAPH.md). The new rank bridge computes the doubling index from an explicit free-plus-finite group decomposition. The squareclass quotient identification and construction of that decomposition remain required for unconditional Lean rank conclusions.
