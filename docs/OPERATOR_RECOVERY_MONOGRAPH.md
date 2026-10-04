# Operator recovery: exact sections, transients and all-future identities

This recovery push takes the operator-level machinery from the September Wilson Forge and Formation discussions and applies it to the integer repository's actual recurrence atlas and field-756 packets. It supplies constructive task sections, invisible-state witnesses, simultaneous transport equations, Fitting decompositions and an exact test for identities of supplied recurrence definitions. The calculations use rational arithmetic and the Python standard library. Existing Lean proofs and imported exponent bounds retain their original status.

## The recovered distinction: rank, transport and task recovery

The September 18 primitive-transport work screened one context, then projected pairs, then zero-Hom obstructions, then the full context family. Its central lesson is that equal ranks do not supply a commuting map. For square source operators A_i and target operators B_i, an actual transport satisfies

\[T A_i=B_i T\quad\text{for every context }i.\]

`intertwiner_space` constructs the complete rational solution space of these simultaneous equations and returns a basis, the constraint rank and the number of variables. A zero-dimensional space gives a concrete arithmetic obstruction to any nonzero linear transport for those supplied operators. A positive-dimensional Hom space alone does not assert an isomorphism. Each returned basis element is substituted back into every equation. The variable budget stops an oversized computation before a result is claimed.

`context_profile` computes the ranks of all nonempty vertical stacks of a named context family. Five contexts give 31 profiles, as in the older Wilson discriminant work. The profiles are descriptive invariants; they are not substituted for the intertwiner equations.

The September 30 task-section discussion supplies a separate constructive criterion. Given f:W→Y and g:V→Y, a lift T:W→V with gT=f exists exactly when im(f) is contained in im(g). An injective lift exists exactly when that containment holds and

\[\dim\ker f\leq\dim\ker g.\]

`task_section` checks image containment column by column. An image obstruction returns a left annihilator of g with nonzero pairing against the failing target column. An injective-dimension obstruction records both kernel dimensions. For a successful injective lift, the implementation extends a basis of ker(f) to a basis of W, sends its kernel part to independent vectors of ker(g), lifts the complementary image directions and transforms back to the original coordinates. It checks both gT=f and the constructed rank.

This is rational linear algebra. A constructed rational lift with denominators need not settle whether a different integral lift exists. `injective_coordinates` makes the stronger integer conclusion only for a full-column-rank carrier: its coordinate vector is unique, so a nonintegral coordinate really rules out membership in that carrier's integer column lattice.

The dual recovery problem is implemented by `target_factor`. For observation G and target F on a common state space, it constructs L with F=LG or returns a vector v with Gv=0 and Fv≠0. The latter is an explicit invisible state that changes the target. Fibonacci's next term can be recovered from its two state coordinates; Padovan's third state coordinate cannot be recovered from only its first two coordinates for arbitrary states.

## Fitting decomposition is more than a kernel check

The old Wilson kernel-free/Fitting correction becomes an executable decomposition. For an n-dimensional rational operator A, find the first k for which rank(A^k)=rank(A^(k+1)). Then

\[V=\ker(A^k)\oplus\operatorname{im}(A^k).\]

A is nilpotent on the first summand and invertible on the second. `fitting_decomposition` builds both bases, the change of basis and its inverse, the conjugated operator, and the complementary commuting projectors. It checks idempotence and commutation exactly. An invertible operator stabilizes at k=0. A length-two nilpotent chain has a two-dimensional eventual nilpotent part even though its ordinary kernel has dimension one.

The actual staged scan has 149 sequence files, 135 reconstructed recurrence candidates and 14 rejected prefixes. All 135 companion operators receive a Fitting calculation. Twenty-nine have a nonzero nilpotent transient: 19 have dimensions (nilpotent,stable)=(1,2), seven have (2,2), and three have (1,3). The remaining 106 have entirely reversible companion states. These facts concern the explicitly reconstructed models, and do not establish their OEIS definitions.

## From finite agreement to an identity of supplied definitions

A scalar recurrence can be represented as a companion-state orbit. To compare two definitions, take their direct-sum state operator, concatenate their seeds and use the difference of their first-coordinate readouts. The outputs vanish for every n≥0 exactly when the readout vanishes on the reachable Krylov space.

`orbit_identity` follows v, Av, A²v, and so on. At the first dependence, the span of the preceding orbit vectors is invariant under A. If every basis readout is zero, closure gives an all-future identity. The returned independent orbit vectors and closure coefficients permit exact replay. If a nonzero output appears first, the result records its earliest index and exact value. This algorithm terminates within the supplied state dimension, rather than treating a long sample as an infinite argument.

All seven translated rational generating-function models now agree for every future index with their paired reconstructed recurrence definitions: A048739, A052995, A078057, A128588, A176981, A212804 and A373566. A128588 starts at offset one; the source GF's initial state is advanced by that offset before comparison. The status establishes equality of the two supplied formal definitions. It does not independently prove that the OEIS prose or mathematical object satisfies either definition. The prior atlas promotion policy is unchanged.

## Five arrows, square-zero radical and the unit gate

The September 19 native Wilson ISA discussion gives three vertices and five arrows, with radical square zero. The basic scalar model now has two arrows from the shared S vertex to a and three from S to A. Elements consist of three diagonal scalars and five arrow coefficients. Multiplication retains the diagonal product and the two diagonal actions on each arrow; products of two radical elements vanish. Units are exactly the elements with all three diagonal entries nonzero, and their inverses are constructed explicitly.

`ArrowElement` provides both the left regular representation and a faithful scalar block carrier with diagonal a, A, and six copies of S. Their determinants must be distinguished:

\[\det(\text{left regular})=a^3A^4S,
\qquad \det(\text{block carrier})=aAS^6.\]

The second replays the scalar shape of the historical discriminant a det(A) det(S)^6. The original 15-by-15 and 5-by-5 matrix blocks, and the full Wilson carrier, are not reconstructed by this basic model. Tests check associativity, both representation homomorphisms, two-sided inverses and radical-square-zero multiplication.

## Two saved cubic models expose a transport obstruction

A second source is the saved June 18 reader `level_deformation_monograph_v4_20_0.html`, Appendix DBL and DBM, read at lines 12688–12700. It distinguishes the cubic x³−2x²−x+1 of discriminant 49 from x³−4x²+5x−1 of discriminant −23. This push imports those polynomial coefficients and independently recalculates their discriminants and multiplication-by-x matrices using the existing quotient-algebra core.

The five powers of each multiplication operator have identical 31-subset rank profiles: every stack has rank three. Nevertheless the simultaneous cross-cubic intertwiner space is zero. Each self-Hom space has dimension three. This supplies a source-backed arithmetic example of why full context ranks do not determine transport. The reader's state-integral and knot-theoretic interpretations are not reproduced or extended here.

## Application to the actual field-756 Thue packets

The repo's `receipts/field756_bound.json` supplies θ³=6θ+2, the two units −5+θ² and 11+θ−2θ², seven binary cubic forms, their φ elements and norm seeds. `field_operator_replay` turns these into exact commuting multiplication matrices. Both units have norm −1, both inverses preserve the supplied coefficient order, and their simultaneous centralizer has rational dimension three.

For each binary cubic with leading coefficient c₀, the carrier is

\[\alpha=c_0a-b\phi,\qquad N(\alpha)=c_0^2M.\]

The implementation reconstructs the homogeneous norm cubic from four exact evaluations and checks every coefficient against the supplied form. It then uses the recovered unique-coordinate machinery to decode signed unit products ±γ ε₁ʳ ε₂ˢ back into integer (a,b), retaining wrong norms, vectors outside the rational plane and nonintegral coordinates as separate outcomes. Every accepted pair is substituted into its binary cubic.

Across the seven classes, the signed exponent box −3≤r,s≤3 contains 686 seed/sign/exponent trials. The replay recovers all 14 listed source points, two per class, and independently reconstructs those points from their norm carriers. Negative-norm units require the sign and norm gate; the code does not silently assume norm one. These bounded results do not reprove the external Matveev bounds or assert that the 14 points are a globally complete Thue list. The existing Lean and external-bound routes remain available with their original premises.

## Reproduction and artifacts

From the repository root, set `PYTHONPATH=python` and run the following commands. The committed receipts contain the outputs of these runs and the focused and full regression logs.

```sh
python -m perfectpower operator-atlas --seq-dir data/oeis/seq
python -m perfectpower fitting --matrix '[[0,1,0],[0,0,0],[0,0,2]]'
python -m perfectpower task-section --target '[[1,0,0],[0,0,0]]' --carrier '[[1,0,0,0],[0,0,0,0]]' --injective
python -m perfectpower recurrence-identity --left-coeff 1,1 --left-initial 0,1 --right-coeff 0,1,1 --right-initial 0,1,1
python -m perfectpower norm-operator-replay --packet receipts/field756_bound.json --radius 3
python -m unittest discover -s python/tests -v
```

The final validation records the exact test counts and source hashes. Randomized conjugation tests exercise Fitting projectors, randomized lift tests exercise image containment and injectivity, and independent direct orbit iteration checks the earliest nonzero output. Corrupted source formulas and listed points are rejected. The new all-future conclusions are constructive rational calculations; no new Lean proof is claimed.

The integrated base includes commit ecea836, which supplies Lean reconstruction uniqueness, quotient-projector identities and recurrence foundations from the parallel session. Those files are preserved. This recovery batch adds Python constructions and applications rather than extending those Lean declarations.

The final integrated Python suite runs 419 tests successfully with four skips in 42.531 seconds. All 16 focused operator tests and all 29 integrated operator/sequence recovery tests pass. Python compilation and whitespace checks pass.
