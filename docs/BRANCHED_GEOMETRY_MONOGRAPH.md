# Perfect powers as branched surfaces and exact connection operators

The subsequent Lean backlog sweep closes all remaining 394 literal-list obligations: **all 3,080 quartic lists and all 3,080 packet equalities are now kernel checked**. The original catalogue source hash is unchanged. The stronger cutoff and preserved exceptional fibre are described in [the proof-sweep monograph](LEAN_BACKLOG_MONOGRAPH.md).

The new module attaches an exact geometric description to the same polynomial equations PerfectPower already studies. Its input is a nonzero integer polynomial P and an exponent d at least two. Its outputs describe the normalization of y^d=P(x), the sheet changes around the roots, a finite connection Laplacian, a closed polyhedral cell model of the resulting topological type, and the integer content obstruction to a polynomial root. These outputs are useful together because each answers a different question. The module preserves those distinctions in its data and its theorems.

The connection between superelliptic curves, periods and sheet topology is standard mathematics. Molin and Neurohr's paper, Computing period matrices and the Abel–Jacobi map of superelliptic curves, develops the analytic period computation for these curves: https://arxiv.org/abs/1707.07249. Kenyon's Spanning forests and the vector bundle Laplacian develops connection Laplacians and their determinant interpretation: https://arxiv.org/abs/1001.4028. This implementation does not compute period matrices or cycle-rooted spanning-forest determinants. It uses exact finite transport and kernel calculations that can support such work later.

## The result that is now a Lean theorem

The principal new theorem is bouquet_cyclic_iff. It constructs a finite graph with one common vertex and a triangular cycle for each supplied root multiplicity. A primitive d-th root of unity supplies the edge transports. The theorem says that its connection Laplacian has a nonzero kernel exactly when every supplied multiplicity is divisible by d. This is a theorem about an actual explicitly defined incidence matrix, rather than a verbal interpretation of a small numerical eigenvalue.

The graph's vertex set is Option(i × Fin 2), where None is the common vertex and each root label i contributes two other vertices. Its incidence rows are f(None)-f(left_i), f(left_i)-f(right_i), and f(right_i)-U_i*f(None). The first two rows force both branch vertices to have the common value. The last row forces that value to survive the corresponding cycle transport.

The Laplacian is BᴴB. The gram_energy theorem proves that its quadratic expression is the sum-of-squares expression of the incidence residuals. The gram_kernel theorem proves that BᴴB*f=0 is equivalent to B*f=0. These finite-dimensional statements work for arbitrary complex incidence matrices; using positive edge weights can be handled by absorbing their square roots into the rows.

A nonzero parallel vector on the connected bouquet must have a nonzero common value. If that value is z, then z=U_i*z for every cycle. Cancellation forces U_i=1. Conversely, if every transport is one, the constant vector gives a nonzero kernel element. The primitive-root theorem then converts zeta^r=1 into d dividing r. This proves the exact faithful-character obstruction.

The primitive-root hypothesis is essential. A nonfaithful character can miss monodromy. For example, taking the trivial character makes every transport one regardless of multiplicity. The theorem therefore does not replace a primitive root by an arbitrary numerical phase. The Python implementation uses the standard cyclotomic polynomial to represent the faithful phase exactly.

The polynomial interpretation requires that the supplied multiplicities actually describe every complex root of P. Over the complex numbers, a nonzero polynomial has a d-th polynomial root exactly when all its root multiplicities are divisible by d; its nonzero scalar coefficient has a complex d-th root. The Lean spectral theorem formalizes the finite graph and divisibility statement. The Python Yun decomposition and the passage from multiplicity data to normalized algebraic curves are exact computations and classical mathematics, not a Lean formalization of the normalization theorem.

## Repeated roots and connected components

For a squarefree polynomial of degree m, each finite root contributes d-1 to ramification. There are gcd(d,m) points above infinity, with total infinity contribution d-gcd(d,m). Riemann–Hurwitz therefore gives chi=d+gcd(d,m)-m(d-1), and genus (2-chi)/2. These familiar formulas require squarefreeness and connectedness.

Repeated roots demand a more careful computation. Let the distinct complex roots have multiplicities r_i, and put c=gcd(d,r_1,...,r_s). The normalization has c connected components over the complex numbers. Each component has covering degree n=d/c. Its reduced root multiplicities are e_i=r_i/c, and its total reduced polynomial degree is M=sum e_i.

The finite ramification contribution per component is sum(n-gcd(n,e_i)). The infinity contribution is n-gcd(n,M). Thus chi_component=2n-sum(n-gcd(n,e_i))-(n-gcd(n,M)). The genus per component is (2-chi_component)/2, and total Euler characteristic is c times the component value. The components are related by multiplication of y by roots of unity and have the same complex topological type.

Yun's squarefree decomposition computes the multiplicity blocks using rational polynomial gcds and derivatives. A squarefree factor of degree h in the multiplicity-r block accounts for h distinct complex roots of multiplicity r. The module re-expands every decomposition and checks that it recovers the original polynomial. It does not need floating-point root coordinates to obtain these multiplicities.

For a nonzero constant polynomial there are no finite branch roots. The component count is d, the component covering degree is one, and every component is a sphere. The zero polynomial is rejected: y^d=0 is nonreduced, so treating it as an ordinary d-sheet covering would be wrong.

As an example, y^4=x^6 has c=2 components. Each component has covering degree two and reduced multiplicity three. Its finite and infinity contributions are each one, giving chi_component=2 and genus zero. The affine components have cuspidal presentations, but their compact normalizations are spheres. The faithful d=4 monodromy is nevertheless nontrivial, so the faithful character Laplacian has zero kernel dimension.

## Arithmetic content remains necessary

Complex sheet transport does not see the signed integer content of the polynomial. Both (x-1)^2 and 2(x-1)^2 have trivial square-root monodromy and two normalized complex components. The first has the integer polynomial root x-1. The second requires the scalar square root of two and has no integer polynomial square root.

The module computes the signed content as the gcd of the absolute coefficients, with the sign of the leading coefficient. It checks whether this integer is a d-th power with the appropriate sign convention. Negative content is permitted for odd d and is excluded for even d. The root-multiplicity condition and this content condition are recorded separately.

When both conditions hold, the module constructs a candidate from the monic multiplicity factors and an exact root of the leading coefficient. It checks that every resulting coefficient is an integer and that raising the candidate to d reproduces P. The returned polynomial is one canonical root, with positive leading coefficient for even d; it is not a list of all scalar root-of-unity multiples.

The lack of an integer polynomial root does not mean that isolated integer hits do not exist. For example, 2(x-1)^2 has the integer hit (1,0). Conversely, trivial complex monodromy alone does not imply density one for integer perfect-power hits. The content condition prevents that error.

Even complex curves with identical genus and branching can have different integral behavior. The conics y^2=x^2+1 and y^2=2x^2+1 are isomorphic after a complex rescaling of x. The first has only the integer input zero; the second has infinitely many Pell inputs. The new geometric layer is not an integer-height theorem or a generic effective solver.

## Exact finite transport and cyclotomic matrices

The Python graph has a triangular cycle for each root label. Its positively labeled cycle runs from the common vertex to the right vertex, to the left vertex, and back. The transport from the common vertex to the right vertex is zeta^r. Its residual rows differ from the first two Lean rows only by a sign, so their Hermitian Gram matrices agree.

transport_certificate constructs spanning-tree potentials modulo d. Every edge then has a cycle residual equal to its voltage plus the potential at its source minus the potential at its target. All residuals are zero exactly when a gauge can remove every transport. The gcd of d and those residuals counts connected components in the full sheet lift.

The implementation independently constructs the entire d-sheet graph for small instances and counts its connected components by traversal. This checks the gcd computation without reusing its formula. Gauge-change tests alter every voltage by an endpoint-potential difference and confirm that the cycle residuals and component count are preserved.

The faithful connection Laplacian is represented in Q[zeta]/Phi_d(zeta). Every cyclotomic polynomial is constructed by exact polynomial division from x^d-1 and its proper-divisor cyclotomic factors. Every entry is an exact rational coefficient vector. Multiplication matrices turn the operator into a rational block matrix, whose rank is computed by exact elimination.

A one-dimensional kernel over the cyclotomic field has dimension phi(d) over the rationals. The receipts explicitly distinguish character kernel dimension from rational block nullity and from the number of components of the full sheet graph. These are different quantities and must not be silently identified.

The exact matrix work has explicit limits: d at most twelve and at most twelve supplied root labels. The topology calculation supports d through sixty-four. An oversized matrix request raises a work-limit error; it does not switch to floating-point eigenvalues or return a partial result labeled exact.

## Cells, dual graphs and finite Hodge operators

cell_surface constructs a closed oriented cell model of a prescribed genus. The sphere uses the boundary of an octahedron. For positive genus, the module triangulates the standard polygon with boundary word a_1 b_1 a_1^-1 b_1^-1 ... a_g b_g a_g^-1 b_g^-1, retaining the edge identifications. This is a delta-complex with loops and possibly multiple edges. It is not represented as a planar simple graph with those identifications discarded.

For positive genus the model has one vertex, 6g-3 edges, and 4g-2 faces. Its Euler characteristic is 2-2g. Every edge occurs in two triangles with opposite orientations. The boundary matrices D1 and D2 satisfy D1*D2=0. The generated GeometryCells.lean file checks that identity in the Lean kernel for every included model.

The dual graph has one vertex per triangle and one edge across each primal edge. Every dual vertex has degree three, with a loop counted twice if it occurs. The dual face sizes are recorded with edge multiplicity. For the positive-genus one-vertex model, its sole dual face has 3(4g-2) sides. For the octahedral sphere, its six dual faces have four sides each.

For a trivalent closed cellular decomposition, 3V=2E and sum q_f=2E. The face charge sum(6-q_f) therefore equals 6(V-E+F)=6chi. The Lean trivalent_charge theorem proves this algebraic identity from its explicit incidence-count hypotheses. The generated model charges are also checked as exact integer identities.

Giving every triangle unit side length produces a polyhedral metric on the model. Its area is F*sqrt(3)/4, its boundary length is zero, and its total angular-defect curvature is 2*pi*chi. The receipts record area as its rational coefficient of sqrt(3), and curvature as its integer coefficient of pi. Their Lipschitz–Killing convention is L0=chi, L1=half boundary length, and L2=area.

This model metric is not claimed to be compatible with the original curve's complex structure. The dual is a combinatorial dual, not a computed intrinsic Voronoi tessellation. A true intrinsic Voronoi construction would require metric choices, geometric coordinates, cut loci, and numerical or exact predicates for cells. The current model preserves the required vertices, edges and disk faces, and gives an exact testbed for the topology and finite Hodge identities.

The finite Hodge matrices are L0=D1*D1^T, L1=D1^T*D1+D2*D2^T, and L2=D2^T*D2. Exact rational elimination checks their kernel dimensions as (1,2g,1). For multiple normalized components, the topological Betti dimensions are multiplied by the component count.

The Lean hodge_one_kernel theorem proves that a vector is in the kernel of the middle Hodge Laplacian exactly when it is killed by both D1 and D2ᴴ. It obtains the result by stacking those two incidence operators and applying the Gram kernel theorem. The numerical rank calculations for the particular models remain exact Python execution; the generic kernel identity and generated chain identities are Lean proofs.

No smooth heat-trace equality, continuum spectral convergence, period matrix, or Jacobian computation is claimed in this push. Those require additional analytic machinery. The topological alternating harmonic dimension in the finite models nevertheless agrees with their Euler characteristic, giving the correct finite counterpart to investigate.

## The integrated collection

The existing 3,080 complete quartic equations now have 12,320 geometry profiles, at exponents two, three, four and six. Each row is linked to the source curve index and source-file hash. The same quartic used for arithmetic solution lists can therefore be inspected for normalized component count, genus, finite ramification, infinity ramification, signed content and complex polynomial-power status.

Those profiles fall into twelve distinct multiplicity-and-exponent patterns. The collection computes an exact cyclotomic connection matrix for every pattern and independently verifies the sheet-lift component count. Ten additional examples illustrate genus two, genus three, split curves, a content obstruction, cuspidal components, a nonmonic integer square root, signed constant obstructions, and the two conics with different arithmetic behavior.

The represented genera are zero, one, two, three, four and seven. For each genus there is a complete cell model with oriented triangles, boundary matrices, Hodge matrices, dual edges, dual face sizes, harmonic dimensions, and the polyhedral Lipschitz–Killing data. The generated Lean checks verify the boundary-square and face-charge identities for all six models.

## Lean work recovered from recent pushes

The recent integer-lifting implementation used Smith certificates and unimodular changes of coordinates in Python. IntegerLiftRecovery now proves the central coordinate transformation over arbitrary finite rectangular integer matrices. If D=U*A*V, Ui*U=I, and V*Vi=I, then A*x=b is equivalent to D*(Vi*x)=U*b. All hypotheses are exact matrix identities that a concrete packet can check.

A companion theorem transports any solved diagonal coordinate vector back to an integer solution through V. An affine-fibre theorem explains how a complete kernel parameterization gives every solution by adding kernel vectors to one particular solution. Its complete-kernel hypothesis remains explicit: the theorem does not magically prove that an arbitrary proposed basis is saturated.

Five actual Smith packets now have kernel-checked integer left and right inverses and a theorem transferring every x and every right-hand side b. They include a one-row coprime system, a one-row divisibility obstruction, a rectangular two-row system, a rank-deficient square system, and a diagonal lattice. The two_three theorem also gives the complete concrete family 2x+3y=1 iff x=-1+3t and y=1-2t for an integer t. The four_six_no_point theorem proves that 4x+6y=1 has no integer solution.

The divisor-sum atlas still contained uncompiled literal point lists. This push resumes that work with bounded batches, preserving the original source hash and each successful case index. The updated validation records the exact number checked; no blanket claim about all emitted sources replaces that ledger.

## Running the module

From the repository root, `PYTHONPATH=python python -m perfectpower branched-geometry --coeff=0,-1,0,0,0,1 --d=2 --connection --cells` produces the complete geometry packet for y^2=x^5-x. Coefficients run from the constant term upward. The optional k argument adds a constant shift before analysis.

`PYTHONPATH=python python python/build_branched_geometry.py` rebuilds the integrated profiles, pattern matrices, examples and cell models. `PYTHONPATH=python python python/make_lean_integer_lifts.py` rebuilds the five integer-coordinate proof packets. `scripts/check_branched_geometry.sh` compiles the two new Lean modules, checks the seventeen generic theorem reports, checks twelve model identities and five coordinate packets, and runs the focused Python tests.

The durable mathematical result is an exact finite connection operator with a proved multiplicity obstruction, attached to the repository's arithmetic equations. The surrounding collection makes component topology, cells and integer content inspectable together. Further geometric sophistication can now be added to a concrete mathematical representation without losing the arithmetic distinction that makes PerfectPower useful.

## Verification of this release

The two generic modules, six literal cell models and five literal Smith packets produced 34 audited Lean theorem reports, all using only propext, Classical.choice and Quot.sound. The complete Python suite passed 474 tests with four existing skips; the ten new focused geometry tests passed separately. This is targeted compilation of the new modules and certificates, not a claim that every historical Lean source in the repository was rebuilt.

The resumed quartic ledger now checks 2,686 complete solution lists and their packet equalities, adding 679 newly checked cases. The remaining 394 emitted lists are explicitly uncompiled. The original catalogue source hash is unchanged.
