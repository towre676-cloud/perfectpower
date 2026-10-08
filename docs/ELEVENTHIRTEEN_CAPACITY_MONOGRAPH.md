# Prime division and exact Mordell charts

## Scope and results

This push extends complete rational division, subgroup preimages and bounded saturation from primes 2, 3, 5 and 7 to 11 and 13. It also supplies exact projective changes of coordinates for the stored Mordell quartic covers. These are bounded executable operations with independent receipt replay. They are not new Lean theorems and do not prove automatic termination of global saturation.

The frontier ledger now distinguishes an externally determined rank from a matching explicit rational-point basis. All 457 historical conditional frontier rows have equal PARI ellrank lower and upper bounds. Of these, 365 have matching explicit point witnesses; 92 do not. The missing constructive data comprise 91 rank-one curves with no retained point and the rank-two curve k = -9257 with one retained independent point. No integral-point list is promoted by this change.

## Complete prime fibres

For a nonsingular rational elliptic curve E and rational point Q, the fibre of multiplication by p is empty or an anchor translated by the rational p-torsion kernel. The producer discovers candidates, but the verifier independently reconstructs the division polynomials from the original Weierstrass coefficients, checks every reported point, and replays a complete rational-root certificate for the torsion polynomial. Exact multiplication validates the anchor and the entire coset.

The p-torsion polynomial has degree (p²−1)/2. A finite division equation has degree p². Thus p = 13 needs degree 84 for the kernel and degree 169 for the finite equation; p = 11 needs degrees 60 and 121. The Sturm subsystem now accepts degree at most 256. The residue-atlas default degree limit remains 64. Raising a limit does not remove coefficient, node or work budgets.

Hensel discovery uses modular integer Horner evaluation, independently compared with exact polynomial evaluation. Necessary rational-root numerator/denominator divisibility filters reject impossible reconstructions before exact evaluation; tests retain nonintegral, negative and zero roots. These changes reduce intermediate sizes without changing residues or the final exact candidate check.

The producer retains a bounded cache of serialized complete torsion-root proofs. Every access returns fresh mutable data. A cached proof still charges its node count against the caller's budget, and no verifier depends on the producer cache or discovery routines. Budget exhaustion raises WorkLimit rather than emitting a partial complete packet.

A negative rational-divisibility result can also follow from good reduction. The verifier enumerates the finite group at a certified small prime, checks the original curve and target reduce there, and checks that no point multiplies to the reduced target. The search now permits good-reduction primes through 997. Failure to find a local obstruction proves nothing.

For primes 11 and 13, local-obstruction mode can also certify a trivial rational p-kernel from a good reduction group whose order is coprime to p. This is prime-to-good-reduction torsion injectivity: properness extends a rational point to the local integral model; the reduction kernel is the formal group. Multiplication by p on that formal group has linear coefficient p, a local unit when the reduction prime differs from p, and is an invertible power series. A p-torsion point reducing to zero is therefore zero. Its finite reduction must be zero when the finite group order is coprime to p, proving the rational kernel is trivial.

The verifier re-enumerates the finite group, requires good integral reduction and a different reduction prime, and checks the stated order and coprimality. No root nodes are used by this proof; finite enumeration charges the separate replay work budget. Ordinary single-fibre mode and any unsupported local case retain the full Sturm proof. A rational five-torsion example verifies that no coprime-order certificate is produced when torsion is present. Corrupted orders and reduction primes are rejected.

## Mixed subgroup relations

For r source generators, every nonzero coefficient vector modulo p has a unique normalized representative whose first nonzero entry is one. The preimage operation examines every projective coefficient line; it never substitutes a sample or drops residue combinations. With four generators, p = 13 requires 2,380 lines. A budget failure leaves this task unfinished.

Divisible projective lines give relations in the coefficient lattice. Existing row reduction, Hermite and Smith presentations supply replacement points and replayable integer coordinate equations. Actual subgroup indices additionally require certified coordinates in the ambient witnessed subgroup, including the existing torsion-aware relation mechanism. An abstract coefficient index alone is not an actual elliptic subgroup index.

The worked rank-one example on y²+y=x³−x recovers P=(0,0) from 143P. The composite fibre factors as 11 followed by 13. The bounded saturation packet records five stages with primes 11, 11, 13, 11, 13 and ends with both primes jointly closed. Closure at all six supported primes is separately tested.

Mixed-generator tests use the rank-two curve y²=x³−4x+1, with P=(0,1), Q=(2,1). At 11, the source rows (3,1) and (1,4) have determinant 11; the normalized relation (1,8) yields 11(P+3Q). At 13, source rows (3,1) and (−1,4) have determinant 13; relation (1,3) yields 13Q. Small determinant presentations keep coordinate growth within the documented budget while testing genuinely hidden mixed divisibility. These mixed tests supply known candidate anchors to discovery; exact multiplication, complete kernel proofs and independent replay still establish every fibre. Separate single-fibre tests exercise discovery without hints.

## Exact quartic chart transport

Let a stored cover be z²=R(t), with x=Nx(t)/z² and y=Ny(t)/z³. The quartic-map checker establishes the rational-function identity y²=x³+k before any new chart is accepted. A nonsingular integer matrix with rows (a,b), (c,d), together with a nonzero integer ordinate scale e, defines t=(as+b)/(cs+d) and z=e w/(cs+d)².

The new cover is obtained by homogeneous binary-form substitution of degrees 4, 4 and 6. Its quartic is divided by e²; the x and y numerators are divided by e² and e³. The transformed quartic must have integral coefficients. The exact identity is checked again after substitution, so an accidental coordinate or scale mismatch is rejected.

For a rational chart point s=u/v, the source weighted projective coordinates are (au+bv, cu+dv, e w v²). Primitive normalization divides the first two entries by their common divisor and the last entry by its square. The sign convention makes the denominator nonnegative. Source infinity is retained: a finite chart point at cs+d=0 can map to a valid projective source point and a finite original Mordell point. Zero ordinates are exceptional and are not divided through.

On the k = −2 cubic cover, translation t=s+3 exposes the original point (3,5) at chart height two. Reciprocal and nonunimodular charts recover the same original point exactly. A separate reciprocal chart transports a genuine source point at infinity. SymPy independently checks the binary substitutions, and malformed maps, corrupted packets and points off the cover are rejected.

The source numerator/denominator height is at most the maximum absolute row sum of the matrix times the chart height. The inverse inequality follows from its adjugate. Primitive normalization can decrease height. These are safe search bounds, not a claim that an arbitrary chosen chart minimizes height.

## Denominator boxes and discovery status

The search wrapper exposes PARI hyperellratpoints boxes with a numerator bound and either an upper denominator bound or a closed denominator interval. Timeout, no returned point, an exceptional zero ordinate and a verified point are separate statuses. A returned point is rechecked against both the transformed cover and the original Mordell equation using exact fractions.

A completed empty bounded search is not a global emptiness proof. A timed-out search is not even a completed bounded census. The packet explicitly retains global_empty_proof=false and integral_point_completeness=false. New chart searches did not add a frontier witness in this push; the constructive count therefore remains 365.

## Rank evidence and trust boundary

PARI documents ellrank output as [r1,r2,s,L], with r1 ≤ rank ≤ r2. Its lower bound is not required to be the number of points returned in L. In particular, a rigorous nonzero lower bound can determine a rank even when the point search has not found a generator. The retained descent packets preserve the backend certification fields and exact lifts; the rank ledger now respects both kinds of evidence.

The legacy ranks_determined_by_two_descent field remains the historical count 365 of matching point witnesses. New fields ranks_determined_by_backend_bounds=457 and ranks_with_matching_point_witnesses=365 state the distinction explicitly. Twelve historical census ranks differ from the equal backend endpoints, including k = −9257, where the original census said one and both backend endpoints say two. This is external computation evidence, not a Lean-certified descent theorem or a complete Mordell–Weil basis.

Primary reference: PARI/GP manual, Elliptic curves, ellrank, and Hyperelliptic curves, hyperellratpoints, https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html and https://pari.math.u-bordeaux.fr/dochtml/html-stable/Hyperelliptic_curves.html. Live receipt generation used GP 2.15.4; the wrapper uses its supported box-height API.

## Reproduction and next bounded task

Run PERFECTPOWER_GP=/path/to/gp make check-elliptic-eleven-thirteen. The arithmetic core and receipt replay use Python's standard library; the independent chart substitution test requires SymPy. The live discovery example requires PARI/GP. Large worked JSON receipts are stored as deterministic gzip files; decompress them before feeding them to the ordinary JSON verifier.

The next substantive elliptic task is constructive: obtain explicit points on the 92 witness-deficient curves and certify independence against the retained upper bounds. Exact chart transport and denominator windows now provide the reusable search mechanism. Automatic saturation termination still needs explicit height-pairing index bounds. Arbitrary-prime division remains unsupported beyond 13. General Lean interpreter refinement and source-to-native semantics retain their own obligations.
