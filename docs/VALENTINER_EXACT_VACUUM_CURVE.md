# An exact all-orders Valentiner vacuum curve

## Result and model

The normalized unperturbed link superpotential is W(K) = I6bar(K) − 5 det(K), with the same original 252-term tensor used in the preceding calculations. At K0 = diag(1, omega, omega squared), omega = (−1 + sqrt(−3))/2, there is a smooth, nonconstant complex algebraic curve on which all nine original F-equations vanish exactly. The determinant is one and W is −5/2 throughout that curve. Consequently the unperturbed vacuum set is infinite. The previously certified 130,681 points cannot be its complete census.

This is an all-orders statement about a specified block branch, proved in characteristic zero. It does not assert that the entire three-null-coordinate germ is flat. It also does not apply unchanged to the separately constructed Gram-quartic, soft, or gauged completions. Those additions change the equations being solved. No CKM angle or golden coefficient enters this calculation.

## Exact block reduction

Use K = [[x,p,0],[q,y,0],[0,0,z]]. The determinant is z(xy − pq). Reconstruct W from the original nine-variable tensor before restricting it. Its block restriction has 42 terms. More significantly, the four F-polynomials for K13, K23, K31 and K32 restrict identically to zero, as polynomial identities. Thus solving the five remaining block F-equations solves all nine original equations. This verifies that the block is a consistent F-flat slice rather than a truncation of unconstrained equations.

All coefficients belong to Q(a), a = sqrt(5) + sqrt(−3), with irreducible minimal polynomial a fourth − 4a squared + 64. Here omega = −1/2 + a cubed/32 + a/8. The exact field and original tensor are retained throughout; no finite-field reconstruction or floating-point approximation is used.

## The ideal certificate

In the polynomial ring Q(a)[x,y,z,p,q], with degree reverse lexicographic order, define I = (W_x,W_y,W_z,W_p,W_q,z(xy − pq) − 1). Singular computes a standard basis G with 38 elements and verifies dim(R/I) = 1. A computed lift matrix T satisfies matrix(I) T = matrix(G); every original generator also reduces to zero against G. These two checks establish equality of the generated ideals.

Global dimension alone would be insufficient: a positive-dimensional component could lie away from our nominated point. The decisive additional calculation is I:q = I. The complete quotient ideal is computed, and every one of its generators has zero normal form against G. The reverse containment is automatic for an ideal quotient. Therefore multiplication by q is injective on R/I.

The accompanying script contains the exact block polynomial, the lift check, the quotient check, the base-point check and the full standard basis. Its transcript and compact JSON receipt are committed alongside it. The calculation is small enough to replay directly; it is not a sampled deformation or an extrapolation of Taylor coefficients.

## Why the curve passes through the massless vacuum

The point P = (1,omega,omega squared,0,0) satisfies every generator of I. In the local ring at P, q is a nonunit and remains a nonzero divisor by I:q = I. That local ring therefore has depth at least one, and hence dimension at least one. Its dimension is bounded above by the global dimension one. It follows that the local dimension at P is exactly one. This excludes an isolated fat point at P.

The Hessian submatrix in coordinates x,y,z,p is invertible at P. Its exact determinant in the a basis is (54675/8)a cubed + (32805/2)a squared − (10935/2)a − 109350, a nonzero element of the degree-four coefficient field. The four equations W_x = W_y = W_z = W_p = 0 therefore determine x,y,z,p holomorphically as functions of q near P.

The local ideal has dimension one and embedding dimension at most one, so its local ring is regular. Thus it is a smooth curve, with q as local parameter. On this curve the remaining equation W_q = 0 and determinant condition hold identically. Together with the four omitted polynomial identities this proves all nine F-equations vanish to every order. The family is implicitly parametrized by its exact ideal and local parameter; a rational closed-form parametrization is not claimed.

## Energy and determinant consequences

The original homogeneous identity is sum(K_ij W_ij) = 6W + 15 det(K). On the exact F-flat curve, det(K) = 1, so W = −5/2. Independently, W + 5/2 reduces to zero against the standard basis. Any positive, nonsingular Kähler metric gives zero F-energy on this family. Canonical kinetic normalization therefore does not lift it at tree level. Additional D-terms or soft terms can lift it and require their own analysis.

The preceding 91-node calculation proved that the complete three-variable effective superpotential has no terms through degree twelve. Its determinant criterion remains useful for the mixed directions. The new result is stronger on this one-dimensional branch: there is no obstruction at degree twenty-four or any higher degree. It does not rule out mixed higher-degree obstructions away from this branch.

## Exact loop-table audit

The requested exact proof of the 52-operator source loop table already exists in python/perfectpower/exact_nonet_algebra.py, described in docs/FLAVOR_EXACT_RUNNING_AND_SELECTION.md. Its arbitrary-precision coefficient identities use Q(sqrt(5)); converting the same identities to a second symbolic package would not strengthen them. A fresh run verifies 1,378 source products and 1,891 Higgs-extended products with zero exact residuals. The coefficient-tampering rejection test also passes. This item should be removed from the open-work list rather than duplicated.

## Reproduction and remaining boundary

Run python3 python/develop_valentiner_exact_vacuum_curve.py --singular /path/to/Singular using Singular 4.3.2 or a compatible version, SymPy, and the repository Python modules. With Singular on PATH, the flag can be omitted. The command regenerates receipts/m22_interactions/valentiner_exact_vacuum_curve.sing, its full exact transcript, and the JSON receipt. The generator rejects any Singular error, incorrect dimension, failed lift, nonzero quotient remainder, failed base-point check or singular massive submatrix.

Run python3 -m pytest -q python/tests/test_valentiner_exact_vacuum_curve.py. The portable checks reconstruct the omitted F-identities and independently evaluate the massive Hessian over the exact coefficient field. The optional live-engine check runs when SINGULAR_BINARY names an executable or Singular is on PATH. The ordinary tests also verify the committed script and transcript hashes and the proof markers.

The closed questions are existence of an all-orders nonconstant unperturbed massless branch and finiteness of the unperturbed vacuum census. The full three-coordinate local germ, its global components, and the directly recomputed 1,080-element sextic stabilizer remain distinct mathematical tasks. Deriving a protected quark-source frame, physical CP selection, the golden CKM relation, and a full quantum model remains the physical mechanism problem. This exact family tells that search which degeneracy its added interactions must lift.
