# Direct Valentiner stabilizer computation and three exact vacuum curves

## Two central results

The full determinant-one unitary stabilizer of the actual sextic tensor has exactly 1,080 elements. This count is now recomputed directly, without Harui's smooth-sextic classification bound. The calculation constructs an intrinsic degree-45 covariant, proves its factorization into forty-five distinct lines, computes the complete automorphism group of their colored incidence graph, and filters every incidence permutation for exact projective realizability. The result is 360 projective symmetries and three scalar lifts per symmetry.

The unperturbed massless vacuum also lies on three individually exact F-flat curves. A cyclic symmetry transports the previously proved smooth block curve into the other two null directions. Their tangents span the entire three-dimensional Hessian kernel. This establishes that every null direction in the chosen basis integrates to an all-orders family. It does not yet establish a shared three-dimensional flat germ: a union of three curves still has dimension one.

These results concern two different potentials. The positive norm/Gram scalar completion selects a finite set of 1,080 frames. The unperturbed W = I6bar − 5 det has infinitely many zero-F-energy vacua. Keeping their equations distinct is essential when using these results to build a flavor mechanism.

## Recovering the exact line configuration

Generate the known subgroup directly from the four original 3.A6 triplet matrices. Exact closure contains 1,080 matrices. Each generator is unitary with determinant one, and its invariance of the original sextic is checked as a coefficient identity. There are exactly forty-five nonidentity matrices satisfying g squared = I. For each one, g + I has rank one. A nonzero row gives the normal covector of its projective fixed line; normalize the first nonzero entry to one. This produces forty-five distinct lines over Q(sqrt(5),sqrt(−3)).

Compute every one of the 990 pairwise intersections with exact cross products, normalize projective coordinates, and join equal points. The resulting 201 points comprise 120 triple, 45 quadruple and 36 quintuple intersections. Every claimed and excluded point-line incidence is then tested directly against the exact coordinates. No approximate clustering or tolerance is used.

The corresponding colored bipartite graph has 246 vertices. Lines form one color class; points are colored by their multiplicities three, four or five. The nauty graph search returns six generators and group order 1,440. Every returned generator is checked for color and edge preservation. Closing their restrictions on the forty-five line labels independently produces exactly 1,440 permutations. Point permutations have no additional kernel: every intersection point is uniquely determined by its incident lines.

This computation uses pynauty 2.8.8.1, backed by nauty. Its exhaustive graph-automorphism algorithm supplies the complete incidence search. The coordinate arithmetic, generated permutation closure, and projective filtering are separate exact calculations. This is a reproducible computational proof; it is not a Lean formalization.

## An intrinsic divisor supplies the upper bound

Let f be the original sextic. Form H = Hess(f), h = det(H), and b as the determinant of the bordered matrix with upper-left entry zero, top row and left column grad(h), and lower-right block H. Their homogeneous degrees are six, twelve and thirty. Finally form c = det(grad(f),grad(h),grad(b)), of degree forty-five.

Singular computes c over the exact characteristic-zero number field. It has 222 terms. Multiplying the forty-five previously recovered linear forms gives L. The complete polynomial identity c = s L, with s a nonzero field element, is verified exactly. Hence these lines are precisely the reduced zero divisor of an intrinsically constructed covariant; they are not merely a configuration associated with the already known subgroup.

If f(Ax) = u f(x) for an invertible coordinate transformation A, the chain rule gives h(Ax) = u cubed det(A) to the power −2 times h(x), and b(Ax) = u to the power eight det(A) to the power −6 times b(x). Consequently c(Ax) = u to the power twelve det(A) to the power −9 times c(x). Every projective symmetry of the sextic must therefore permute its forty-five lines and preserve their incidence graph. This supplies a finite upper-bound search without a classification theorem.

The factorization and all four original-generator checks are recorded in the committed Singular script and transcript. The covariant identity is verified in all coefficients, not at sampled points.

## Filtering all 1,440 incidence permutations

Choose four normal covectors in projective general position. In the actual enumeration their indices are 0,1,2,3. No three are collinear in the dual plane. An ordered projective frame determines a unique projective transformation. For each of the 1,440 incidence permutations, compute that transformation from the four prescribed images and test it on every line normal. These are exact number-field comparisons.

Exactly 360 candidates pass all forty-five tests; 1,080 fail. For each failure the receipt stores the first line whose prescribed image disagrees. The complete permutation list is regenerated deterministically from the committed graph generators. The accepted set is independently compared with the exact permutation closure of the original four matrix generators acting on the dual lines, and the two sets agree.

Any projectivity over the complex numbers preserving these lines is recovered by the same four-frame calculation. Since the frame coordinates lie in the coefficient field, its unique projective matrix has a representative over that field; searching exact field matrices loses no complex projectivities. The action is faithful because a projectivity fixing the four frame lines is scalar. Thus the full projective sextic symmetry group has order 360.

The original exact matrix subgroup already supplies 1,080 determinant-one unitary tensor symmetries and has projective image 360. A scalar multiple of one of these matrices can preserve determinant one only when the scalar is a cube root of unity. All three such scalars preserve the sextic. Therefore the complete SU(3) tensor stabilizer has order 3 times 360 = 1,080. Complex conjugation transfers the same result to the conjugate tensor used in the selected-frame potential. With the earlier positive norm/Gram equality argument, the selected global matrix vacuum set has exactly 1,080 elements.

This closes the direct-stabilizer recomputation item. It counts matrices before any physically declared gauge or symmetry quotient. It does not derive quark interactions or a physical CP choice.

## Three exact curves through the massless vacuum

The preceding block calculation proved a smooth curve through K0 = diag(1,omega,omega squared), with K = [[x,p,0],[q,y,0],[0,0,z]]. All nine original F-equations vanish, det(K) = 1 and W = −5/2 along it. Its local parameter is q = K21. The crucial ideal identity I:q = I excludes an isolated fat point at K0.

Let A cycle the three coordinates and define T(K) = omega squared A K A inverse. The original 252-term tensor directly verifies W(T(K)) = W(K). Both its cubic determinant and sextic terms acquire trivial overall phases. T fixes K0 and has order three. Consequently C, T(C), T squared(C) are exact smooth F-flat curves through the same vacuum, with determinant one and W = −5/2 on each.

Transport the tangent of C by T and T squared. Exact comparisons identify the three resulting lines with the known null vectors whose free coordinates are K21, K31 and K32. Their rank is three, so they span the full Hessian kernel. Distinct tangents also give pairwise isolated intersections at the base. Each selected coordinate-axis direction is therefore unobstructed to every order, rather than only through the previously checked degree twelve.

The mixed-direction question remains precise: do these curves lie on a common three-dimensional smooth F-flat germ, on lower-dimensional components, or on separate curve branches? The complete degree-twelve cancellation remains valid, and the determinant criterion can still settle that question. The current calculation establishes the three curves and their independent tangents; it does not infer dimension three from a tangent-space count.

## Reproduction and package

Install the optional graph dependency with python3 -m pip install pynauty==2.8.8.1. Run python3 python/develop_valentiner_direct_stabilizer.py --singular /path/to/Singular, then python3 python/develop_valentiner_three_exact_curves.py. The first command regenerates the exact line geometry, graph generators, all projectivity decisions, covariant script, transcript and compact receipt. The second reconstructs the original tensor symmetry and the three transported tangents. Singular 4.3.2 and pynauty 2.8.8.1 were used for this release.

The selected-stabilizer module and its receipt now use the direct count; their radial-loop formulas and model assumptions are retained. Focused tests rerun the complete projectivity filter and exact covariant identity, test the three tangent directions, and check the older all-orders curve, quantum spectra and tensor-loop results. The complete archive includes every tracked repository file, the current full flavor monograph, this standalone paper, and the exact receipts.

For provenance, the line configuration is the classical Wiman arrangement, discussed for example in Bauer et al., Negative Curves on Symmetric Blowups of the Projective Plane, Resurgences, and Waldschmidt Constants, International Mathematics Research Notices 2019, 7459–7514, DOI 10.1093/imrn/rnx329. The present count does not use its group classification as a premise. Graph-engine documentation is at https://github.com/pdobsan/pynauty. The covariant construction and all coordinate identities are rebuilt from our tensor.
