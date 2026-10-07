# Complete bounded residue patches

## The gap closed

An auxiliary polynomial that vanishes on a supplied point list need not vanish on every solution of the original equation. The previous residue-determinant push supplied exact interpolation and rational kernel spanning, but did not establish exhaustive coverage of a curve. This push connects the two interfaces within an explicit closed rectangle and prime residue class. A typed Lean CoverPacket carries an equality between the source-defined finite solution set and the returned literal point list. The general relation_on_box theorem transports every checked relation to any integer solution satisfying the declared bounds and congruences.

The implementation preserves the concurrent thermal-wall and all-prime local power-free additions present at base 7b5fd27a3015f34ae8e861515b19607d1113354a. The new public operations are bounded_residue_patch, verify_bounded_residue_patch and native_bounded_residue_patch. Existing query operations and certificate formats retain their interfaces.

## Source binding and a correction

The source is an exact sparse integer polynomial, with terms given as coefficient and two nonnegative exponents. Every returned solution is tested against that source equation. The earlier Mordell example wrongly described (129,1465) and its negative ordinate as points on y squared = x cubed - 2. They are not: the defining polynomial evaluates to -462. Those two inputs have been removed from the previous corpus and its description. Their interpolation certificates established relations on literal data, but did not establish the asserted curve membership. The corrected earlier sample contains (3,5) and (3,-5); the new packets additionally prove their complete bounded source interpretation.

## Smooth first lifts

For a prime p and base residue (a,b), the producer expands the source exactly. It rejects a base point unless p divides F(a,b), and rejects this chart unless the vertical derivative is a unit modulo p. TaylorPacket stores integer constant, horizontal and vertical coefficients, an exact polynomial remainder, the universal expansion identity and a Bezout witness for vertical invertibility.

$$
F(a+pu,b+pv)=p(c+d_xu+d_yv)+p^2R(u,v)
$$

The general first_lift theorem proves that divisibility of the source by p squared is equivalent to divisibility of the linear residue expression by p. The vertical_unique theorem cancels the invertible vertical coefficient: two successful vertical residues differ by a multiple of p. Thus each horizontal residue determines a unique vertical residue modulo p for the lift coordinates. This concerns the first lift only; no arbitrary-depth analytic Hensel theorem is asserted.

The producer uses the unique lift to enumerate candidate ordinates directly modulo p squared. The independent replay checker enumerates every pair in the coarser residue grid, filters by divisibility by p squared, and then filters by the exact source equation. Equality of these independently obtained lists detects omissions in lift discovery as well as omissions in the final solution list. Native certificates recompute the source-defined finite sets inside Lean with decide +kernel.

## Complete covering and auxiliary relations

residueValues is the closed integer interval filtered by the declared congruence. coarse is the product of the two filtered intervals; lifts adds divisibility by p squared; solutions adds source equality to zero. solutions_complete proves the exact membership biconditional without smoothness or primality assumptions. The complete box argument therefore does not rely on trusting the Python lift optimization.

CoverPacket.complete exposes that biconditional for the returned list. relation_on_box takes a relation proved at every returned point and obtains its vanishing at any original-source solution in the declared rectangle and residue class. empty_box proves exclusion when the certified list is empty. The rectangle is a premise, not a derived global bound.

The existing integral-kernel producer supplies auxiliary relations on the complete point list. Its rational spanning guarantee remains rational spanning: primitive integral vectors need not generate the saturated integer kernel lattice. The new relation theorem does not need an integral saturation claim. Generated polynomial relations are checked directly on the complete literal list before they are transported to arbitrary bounded source solutions.

## Worked corpus

The parabola F = y - x squared uses prime five, residue (1,1), x between -10 and 10 and y between zero and 100. Its complete point list is (-9,81), (-4,16), (1,1), (6,36). The basis 1,x,y,x squared yields the defining parabola relation throughout this patch, rather than merely on a selected sample.

The two Mordell charts use prime seven, residues (3,5) and (3,2), x between zero and 35 and y between -220 and 220. They return (3,5) and (3,-5), respectively. A third Mordell rectangle with x between 10 and 20 and y between -20 and 20 is empty in residue (3,5), giving a native exclusion theorem. The signed quartic F = y squared - x to the fourth uses prime three, residue (1,1), and a box covering six positive-ordinate solutions. The cubic superelliptic source F = y cubed - x squared - 1 supplies a smooth derivative of three modulo five and a separate nonlinear remainder test.

## Reproduction and trust boundary

Run make check-bounded-residue-patch on the pinned Lean 4.20.0 and Mathlib source specified by lake-manifest.json. The script regenerates all six packets, runs twelve focused Python tests, compiles the reusable module, checks every native source and rejects proof dependencies outside propext, Classical.choice and Quot.sound. It also rejects sorryAx and Lean.ofReduceBool. The earlier residue-determinant checks must be rerun after the Mordell correction.

Producer budgets are explicit: primes from two through 257, total degree at most twelve, at most 24 input terms, axis widths at most 8192, coarse grids at most 4096 pairs and complete solution lists at most 64 points. Oversized inputs are rejected; no list is truncated. Empty solutions are supported. Singular vertical charts are rejected rather than treated as smooth.

Each exported source has universal exact Taylor and Bezout proofs, checked primality, equality of the complete lift set with its literal candidates, equality of the complete solution set with its literal outputs, and an arbitrary-coordinate complete theorem. Every generated auxiliary relation or empty-box exclusion is audited. A packet's execution_verified flag stays false: a returned source string is not evidence that Lean has executed it. The repository validation receipt records actual execution separately.

## Next bounded push and independent obligations

The next natural extension is chart switching: if the vertical derivative is singular but the horizontal derivative is invertible, swap the coordinate roles while retaining the same source and box semantics. Add a horizontal Taylor packet, a symmetry theorem for the finite cover and native certificates demonstrating both charts agree on their overlapping domains. Validate a source such as x - y squared, negative coordinates, empty overlap and corrupted chart labels. Fully singular residues need a separate branching lift algorithm retaining every branch.

Global Mordell bounds, explicit Matveev premises, complete ambient elliptic rank, integral kernel lattice saturation, general JSON parsing and source-to-native compiler refinement remain independent obligations. This push establishes exact bounded source coverage and its auxiliary-relation consequence. It does not remove a global height premise from the broader research program.
