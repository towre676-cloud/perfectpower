# Alternating contractions, smaller covers and constructive Mordell witnesses

## Result

This push turns the invariant-tensor viewpoint in Predrag Cvitanovic's Group Theory: Birdtracks, Lie's, and Exceptional Groups into exact binary-form arithmetic. A typed contraction program now constructs covariants and invariants from homogeneous polynomial coefficients, with rational normalization and explicit tensor degrees. Quartic cover reduction uses that arithmetic to retain smaller integral models and their exact maps to the original Mordell curve. The application closes two constructive witness gaps, k=-6798 and k=-7099. Of the 457 frontier curves, 367 now have explicit point witnesses matching the retained rank upper bounds; 90 remain witness-deficient. All 457 already have equal external PARI rank endpoints. The missing constructive data consist of 89 rank-one witnesses and the second independent point on the rank-two curve k=-9257.

The invariant atlas contains all 1,027 retained covers. Of the 93 covers belonging to the original 92 witness-deficient curves, 29 have a strictly smaller reduction score. Three have smaller absolute discriminant; the other improvements reduce coefficient size. The newly discovered points are nonintegral. Integral-point completeness, complete Mordell-Weil bases and global saturation termination remain separate obligations. This push adds exact executable mathematics and positive witness evidence, with no new Lean theorem.

## From a polynomial to a symmetric tensor

A binary form of degree n is F(x,y)=sum_i f_i x^i y^(n-i). The coefficient f_i equals binomial(n,i) times the corresponding symmetric tensor component. Keeping this normalization matters: treating polynomial coefficients as tensor entries changes contraction factors. The implementation stores the homogeneous degree separately from the affine coefficient list. For example, a cubic affine expression can be a binary quartic with a root at infinity. Trimming its leading zero would destroy that geometric information.

The alternating tensor epsilon contracts one index from each of two symmetric tensors. Its r-fold contraction is the normalized transvectant (F,G)_r. With degrees m and n, it is the sum over j from zero through r of (-1)^j binomial(r,j) times the product of the corresponding mixed partial derivatives, multiplied by (m-r)!(n-r)!/(m!n!). The resulting binary form has degree m+n-2r. This is rational arithmetic; no numerical root selection or diagonalizing basis is needed.

Under F(x,y) -> F(ax+by,cx+dy), a transvectant gains the factor det(M)^r as well as its ordinary output-coordinate substitution. This relative covariance is checked for general rational forms and nonsingular nonunimodular matrices. The signed epsilon convention is fixed by (x,y)_1=1. Odd self-contractions vanish as expected. The bounded compiler composes these operations as an acyclic program, preserving each intermediate homogeneous degree. It accepts at most 32 inputs, 256 nodes and degree 32 at every intermediate node.

## Quartic invariants and covariants

For F=ax^4+bx^3y+cx^2y^2+dxy^3+ey^4, the classical invariants are I=12ae-3bd+c^2 and J=72ace+9bcd-27ad^2-27b^2e-2c^3. The discriminant is (4I^3-J^2)/27. Independent contraction expressions recover I=6(F,F)_4 and J=72(F,(F,F)_2)_4. The normalized Hessian H=(F,F)_2 is a quartic covariant, and (F,H)_1 is a sextic covariant. For a cubic, a successive contraction of its quadratic Hessian produces the cubic discriminant with factor 27/2.

The standard quartic Jacobian model retained by the invariant interface is Y^2=X^3-27IX-27J. This model describes the Jacobian of a smooth quartic double cover; it does not identify the covering with its Jacobian without additional data. In particular, a Jacobian formula does not supply a rational point on a torsor. Existing Mordell maps remain the authoritative coordinate transport for the frontier application.

I and J are useful fingerprints, but equality is not a rational-orbit or integral-orbit certificate. Distinct covers can share a Jacobian and the same invariants while representing different descent classes. The atlas explicitly records that invariants do not establish equivalence. Every accepted reduction retains its actual matrix, ordinate scale and original covering map. No search task is discarded merely because another form has matching invariants.

## Exact reduction of covering models

Write a retained covering as z^2=R(t), with original Mordell coordinates X=Nx(t)/z^2 and Y=Ny(t)/z^3. Its exact defining identity is Ny^2=Nx^3+kR^3. A chart uses t=(as+b)/(cs+d) and z=e*w/(cs+d)^2. Homogeneous substitutions of degrees four, four and six transform R,Nx,Ny, with division by e^2,e^2,e^3 respectively. Every selected chart rechecks the original identity.

The reduction score is the lexicographic triple consisting of absolute quartic discriminant, maximum absolute coefficient and sum of absolute coefficients. Every accepted step strictly decreases this triple. Candidate moves include a bounded GL2(Z) neighborhood, exact coefficient-centering shears, bounded square-content extraction and local p-adic chart proposals at 2,3,5,7. A p-adic chart substitutes (u,v) -> (pu+rv,v), or its reciprocal version, and tries ordinate scales p and p^2. All five resulting quartic coefficients must remain integral. The method retains the unchanged form if no admissible improvement is found.

These are bounded reduction and integral scaling operations. They are not an implementation of the full Cremona-Fisher-Stoll minimisation theorem, and their output is not asserted globally minimal. The default allows eight steps. Combined matrix entries and ordinate scales must remain within the existing chart API's bounds. Square-content extraction uses bounded trial division, followed by an exact square test on the residual content; an unfactored nonsquare remainder is retained.

For a combined matrix M and ordinate scale e, the exact transformation laws are I'=det(M)^4 I/e^4, J'=det(M)^6 J/e^6 and disc'=det(M)^12 disc/e^12. These laws distinguish coefficient reduction from genuine discriminant reduction. All are tested against the explicit transformed model. The three discriminant improvements in this application are local model improvements, with no global minimality conclusion.

## Primitive points, residues and projective infinity

A rational covering point has weighted primitive coordinates (u,v,w), satisfying w^2=R_h(u,v), gcd(u,v)=1 and v>=0. Infinity is represented by (1,0,w). Under the selected chart, the source coordinates are (au+bv,cu+dv,e*w). Primitive normalization divides the first two coordinates by their gcd and the last by its square. Both ordinate signs are retained in the native bounded enumeration. Zero ordinates are explicitly excluded from the Mordell map, which divides by them.

For a modulus m, the square-residue mask retains every primitive pair (u,v) modulo m for which R_h(u,v) is a square. The default native search uses moduli 16,9,5,7. It preserves pairs with v=0 modulo m, since valid rational points can have denominators divisible by a small prime and valid projective points can lie at infinity. A surviving pair is still tested by an exact integer square root. Residue masks are necessary conditions rather than global insolubility tests.

The native enumerator returns the nonzero-ordinate points in a declared projective height box. Larger searches use PARI hyperellratpoints with explicit numerator and denominator bounds. A returned point is transported through the reduced chart and checked again on the original cover and Mordell curve. Timeout and completed empty bounded search remain distinct outcomes. Neither is a global absence theorem.

## Two new witnesses

For k=-6798, the selected chart has matrix [[-1,-1],[-1,0]] and ordinate scale one. It reduces the maximum quartic coefficient from 132 to 91 and the coefficient sum from 315 to 287. The original cover abscissa is 2476090/608289. The lifted Mordell X-coordinate is 11081746842796288071036005383/544715794393731667094113089, and the Y-coordinate is 512020475423829138505436122473009008677475/12713202135182540322307776887658045798687. Exact substitution gives Y^2=X^3-6798. The retained independence certificate establishes a non-torsion rank-one witness matching the existing upper bound.

For k=-7099, the selected chart has matrix [[0,2],[1,0]] and ordinate scale two. It reduces the maximum quartic coefficient from 156 to 96 and the coefficient sum from 301 to 219, preserving the discriminant. The original cover abscissa is 2001792/350905. The lifted coordinates are X=928456106829181905791227111/47606264277422820179924025 and Y=-5867451917702174335904806012358251030766/328470336029793889072825402395080473875. Exact substitution gives Y^2=X^3-7099, and retained independence evidence establishes rank one.

These examples show why cover coordinates matter: modest changes to the quartic model expose original-coordinate points with very large numerators and denominators. The first pass found these witnesses where earlier retained searches had not. This is an observed discovery improvement; no matched timing experiment establishes an overall speedup attributable solely to reduction.

## Search rounds and remaining frontier

The first round searched all 93 covers at numerator and denominator height ten million, with eight seconds per cover and eight workers. It returned the two new points; 91 cover attempts timed out. A second round searched the remaining 91 covers with numerator bound one hundred million and denominator bound one hundred thousand. It completed 65 empty bounded searches and timed out on 26. A third round used numerator bound one hundred million, denominator bound one million and twelve seconds per cover. It completed 57 empty bounded searches and timed out on 34. Neither later round found a further witness. All three rounds had zero processing errors.

The unresolved frontier is now constructive rather than a claim of undetermined backend ranks: 89 rank-one curves need retained non-torsion points, and k=-9257 needs a second independent point. The global tasks remain complete bases and saturation with adequate index bounds, effective integral-point bounds, complete norm representative coverage where required, and formal refinement of the relevant arithmetic programs. Finite chart searches alone do not settle those tasks.

## Reproduction and interfaces

Run make check-quartic-invariants for contraction identities, symbolic cross-checks and original-map receipt checks. The exact arithmetic uses Python's standard library. SymPy is needed for independent symbolic tests. PARI/GP is needed only for large rational-point discovery; set PERFECTPOWER_GP or pass --gp to the runner. The committed discovery run used GP 2.15.4.

Run PYTHONPATH=python python python/develop_quartic_invariants.py --height 10000000 --timeout 8 for a first-round search. The --denominator-max option specifies a rectangular box; --models-only builds the atlas and reduced models without PARI search. Runs append their summaries and preserve the exactly lifted witnesses in the descent packets. Regenerate the ledger with python/reconcile_mordell_frontier.py and the descent summary with python/develop_mordell_two_descent.py --effort 3. Existing solved packets are reused.

The reusable Python interfaces are symmetric_tensor, transvectant, compile_contractions, binary_substitute, quartic_invariants, quartic_covariants and cubic_discriminant in perfectpower.binary_invariants; reduce_cover, projective_residue_mask and search_reduced_box in perfectpower.quartic_cover_reduction. The contraction atlas and three-round search receipt are in receipts/quartic_invariants. The original curves' positive evidence remains in receipts/mordell_two_descent.

## Primary sources

Predrag Cvitanovic, Group Theory: Birdtracks, Lie's, and Exceptional Groups, version 9.0.1, especially chapters 3-6 and section 15.1: https://birdtracks.eu/version9.0/GroupTheory.pdf.

John Cremona, Tom Fisher and Michael Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010): https://arxiv.org/abs/0908.1741. This supplies the arithmetic context and fuller algorithms beyond the bounded operations delivered here.

PARI/GP official manuals, hyperellratpoints and ellrank: https://pari.math.u-bordeaux.fr/dochtml/html-stable/Hyperelliptic_curves.html and https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html.
