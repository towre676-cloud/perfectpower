# Shared-factor residue intersections

## The missing operation

The existing atlas product joins complete prime-power atlases for one source polynomial at distinct primes. Its Cartesian-product count is correct because the moduli are coprime. An intersection of two products can share factors, and the source polynomials can differ. Multiplying the periods or multiplying all root counts then gives the wrong answer.

Let A and B be complete canonical root sets in two coordinates, with positive periods m and n. Set g=gcd(m,n) and L=lcm(m,n). The simultaneous modular domain consists of the common integer points whose reductions belong to both sets. For systems of equations, every exact common zero survives every local constraint; an empty intersection proves that the system has no integer solution.

## Fiber compatibility and unique reconstruction

A pair of local roots a and b can come from a common point exactly when their first coordinates agree modulo g and their second coordinates agree modulo g. Thus the correct input to reconstruction is the fiber product, consisting of compatible pairs, rather than all of A times B.

For one coordinate write M=m/g, N=n/g. These integers are coprime. Compatibility means b-a=g*t. Choose u and v with u*M+v*N=1. Then z=a+m*u*t is congruent to a modulo m and to b modulo n. Its canonical representative modulo L is independent of the Bezout choice. If two reconstructions have both prescribed projections, their difference is divisible by both m and n, hence by L. Therefore compatible pairs correspond bijectively to simultaneous residues modulo L, coordinate by coordinate.

Partition A and B by their reductions c modulo g in both coordinates. If A_c and B_c denote these fibers, the number of simultaneous roots is the sum, over all common fibers c, of |A_c| times |B_c|. Empty fibers contribute zero. In the coprime case there is one fiber, recovering the old Cartesian-product formula. For nested periods the reconstruction retains exactly the stronger-period roots that satisfy the weaker constraint, even when their source polynomials differ.

## Exact implementation

The module perfectpower.residue_atlas_intersection accepts one through eight complete local atlases or existing atlas products. Product packets are flattened to their verified local constraints, preserving all source equations. At each step it buckets the next roots modulo the gcd, joins only matching fibers, and reconstructs the result modulo the lcm. Intermediate periods, gcds, lcms and compatible counts are recorded. The final canonical roots are sorted and contain no duplicates because the projection pair determines the input pair uniquely.

The traversal is bounded by an explicit work budget, including root bucketing, existing-root visits and compatible joins. Exhaustion raises an error and never returns a partial cover. The roots are stored explicitly; this extension does not promise compressed storage for an arbitrarily large final root set. Verification rebuilds the packet from independently replayed local atlas evidence and compares the complete JSON encoding, preserving the distinction between boolean and integer values and rejecting extra fields.

The JSONL operations are intersect_residue_atlases, verify_residue_atlas_intersection, residue_intersection_population, residue_intersection_select and residue_intersection_rank. Population is an integer; selection and rank use canonical root order, followed by increasing x and y inside each residue cell. Selection outside the population and ranking a point outside the modular domain fail explicitly.

## Rectangle arithmetic

For a canonical residue r modulo L, the number of integers in a closed interval [lo,hi] with that residue is floor((hi-r)/L)-floor((lo-1-r)/L). A two-coordinate cell contributes the product of its two axis counts. Distinct roots give disjoint cells, so summing these products counts the entire modular candidate population without iterating over the rectangle. This works for negative endpoints and extremely large bounds. The count is of modular candidates; exact source equalities still require evaluation, and no global height bound is asserted.

## Worked intersections

The constraints x-y=0 modulo 4 and x+y=0 modulo 8 have four simultaneous roots modulo 8: (0,0), (2,6), (4,4) and (6,2). Their two local atlases have four and eight roots, respectively. The shared gcd is 4, so 32 Cartesian pairs reduce to four compatible pairs. The resulting period is 8, rather than the incorrect product period 32.

The composite products x-y=0 modulo 12 and x+y=0 modulo 40 share gcd 4. Their intersection has 60 roots modulo 120. Direct enumeration of the 120-by-120 residue square independently matches the constructed root set. Reversing the two input products gives the same canonical roots. The box [-10^30,10^30] in each coordinate has 16666666666666666666666666666700000000000000000000000000001 modular candidates, computed entirely with integer arithmetic.

The constraints x=0 modulo 2 and x=1 modulo 2 have individually nonempty atlases but an empty intersection. This gives a genuine simultaneous-system obstruction, rather than a failure of one input atlas.

## Formal boundary and validation

PerfectPower.ResidueAtlasIntersection proves three generic theorems. The joined_card theorem proves that a lift with its two correct projections maps compatible pairs injectively, hence preserves their exact count. The joined_complete theorem proves membership equivalence from the projection laws and the recovery law. The shared_factor_reconstruction theorem proves both congruences of the unreduced Bezout formula under the explicit relation u*M+v*N=1.

These are generic kernel proofs, not assumptions that Python execution is correct. The canonical lcm reduction and the concrete Python packet compiler have not yet been connected to the generic projection and recovery hypotheses by an all-input Lean refinement theorem. The mathematical proof above and exhaustive runtime checks cover that reconstruction at the present release boundary; execution_verified remains false in every packet.

The focused and neighboring suite passes 54 tests. The generalized CRT test compares all residue pairs for every pair of moduli from 1 through 16 against a direct canonical-period census. Further tests cover distinct sources, shared composite products, input reversal, nested periods, negative residues, huge populations, rank/select round trips, empty intersections, exhausted budgets and literal JSON tampering. The Lean module builds and its three theorem dependencies are audited without admitted proofs.

Run PYTHONPATH=python python -m unittest python.tests.test_residue_atlas_intersection python.tests.test_residue_atlas python.tests.test_residue_atlas_product. Run python python/develop_residue_atlas_intersection.py to reproduce the three retained packets. Run lake build PerfectPower.ResidueAtlasIntersection and lake env lean python/audit_residue_atlas_intersection.lean with the repository's Lean toolchain.
