# Recovered covering obstructions and integral lattice arithmetic

## What this release adds

PerfectPower can now replay a concrete globally obstructed genus-one covering example, compute integral presentation invariants without choosing a rational kernel basis, recover exact inverse-image congruences for existing cubic-order maps, and feed those congruences into the signed unit-orbit sieve. It also checks supplied polynomial decompositions while retaining the obstruction to cancelling a noninjective outer polynomial. These are executable transfers of machinery recovered from the July arithmetic programs and the September Wilson work.

All new computations are exact Python and use the standard library. No new Lean declarations, automatic general Selmer algorithm, general Cassels–Tate pairing algorithm, global unit-exponent bound, or Bilu–Tichy converse theorem is asserted. Arithmetic identities and finite computations are replayed; the Fisher example's global interpretation remains explicitly source-backed. The routines do not turn a surviving modular residue into a rational point or interpret a numerical BSD ratio as a proved Sha order.

## Binary quartic conventions and arithmetic

`perfectpower.covering` uses descending homogeneous coefficients `(a,b,c,d,e)` for `a*x^4+b*x^3*z+c*x^2*z^2+d*x*z^3+e*z^4`. This differs from the package's usual ascending univariate convention; it is explicit at the API boundary. The module computes exact invariants, discriminant and Hessian. It uses the existing `QuotientAlgebra` to perform cubic resolvent calculations, including inversion. Reducible quotient algebras remain algebras, and irreducibility is not assumed merely because a modulus is cubic.

The mathematical source is Tom Fisher, *On binary quartics and the Cassels–Tate pairing*, arXiv:2208.14977, Theorem 3.1, Remark 3.3 and Example 3.4: https://arxiv.org/abs/2208.14977 . The generic `fisher_gamma` API verifies a supplied square identity among the three cubic invariants and recomputes the covariant identity before returning the coefficient used in the pairing formula. It rejects mismatched invariants, singular quartics, a false square identity, or a noninvertible supplied element. It does not independently establish Selmer membership or construct the third covering for arbitrary input.

## Replaying the recovered example

The fixture contains the three binary quartics of Fisher Example 3.4 for the elliptic curve `y²+y=x³−x²−929x−10595`. Each has invariants `I=44608`, `J=18842960`, and discriminant `−2338816`. The implementation reconstructs the quadratic gamma form as `(4/9)(5*x²−16*x*z−12*z²)`, checks smooth local witnesses at the five exceptional odd primes, lifts the supplied auxiliary polynomial at two, and evaluates the real contribution. The finite Hilbert-symbol product is `−1`. The source supplies the descent identification and the argument that all unlisted primes contribute trivially; the receipt lists these dependencies rather than treating finitely many witnesses as universal coverage.

The Hensel routine returns root `2416` modulo `4096` for the auxiliary polynomial. Its residue is zero, it is `16` modulo `32`, and the relevant quadratic core has square class `5` at two. At the real witness `(15,4)`, the quartic value is `101` and the core value is `−27`. The replay evaluates each local contribution rather than copying the old saved pairing matrix. The returned matrix is the interpretation of this source-backed example, not an automatically discovered pairing on a user-supplied Selmer group.

`hilbert(a,b,p)` accepts nonzero rational arguments and a prime or the real place. It strips valuations exactly, inverts unit denominators modulo the appropriate modulus, and evaluates the odd-prime or two-adic formula. Its tests check symmetry, bilinearity, square invariance, the identity `(a,−a)=1`, and reciprocity on 150 rational fixtures. A separate finite norm-equation test checks representative odd-prime cases. These checks substantiate the arithmetic implementation; they are not a Lean proof of reciprocity or of the global pairing theorem.

## Two-isogeny covering interface

For a nonsingular model `y²=x³+A*x²+B*x`, and a nonzero integer `d` dividing `B`, the module constructs the quartic `w²=d*u⁴+A*u²*v²+(B/d)*v⁴`. On the chart `v≠0`, its map is `x=d*u²/v²`, `y=d*u*w/v³`. `covering_point` checks the rational input point and then recomputes the target residual. `two_isogeny_point` applies the degree-two rational map on the chart `x≠0` to the model with coefficients `−2A` and `A²−4B`, again checking the output equation. The excluded charts remain explicit; these functions do not enumerate all coverings, identify the full Selmer group, or prove complete rational-point lists. A family test exercises the maps on actual small covering points for many signed choices of `A,B,d`.

The concrete receipt starts from `(A,B)=(-1,1)` and covering point `(u,w,v)=(1,1,1)`. It obtains source elliptic point `(1,1)` and target point `(1,0)` on the model with coefficients `(2,-3)`. The resulting zero y-coordinate is a valid target torsion point, not a failure of the map.

## Integral presentations rather than rational fingerprints

For an integral `m×n` matrix `A`, columns generate a subgroup of `Z^m`. The module computes the determinantal divisors `δ_k`, the gcd of all `k×k` minors, with `δ_0=1`. If the rational rank is `r`, the Smith factors are `δ_k/δ_(k−1)` for `1≤k≤r`. The cokernel has free rank `m−r`; its torsion factors are the Smith factors exceeding one. The gcd of the maximal nonzero minors is the index in the saturated lattice and the order of the torsion part of the cokernel. This is a small-matrix exact algorithm with an explicit minor budget. It does not supply unimodular Smith transformation matrices, polynomial Fitting ideals, or a general large sparse Smith implementation.

`local_torsion_profile(A,p)` extracts every positive p-adic valuation of the Smith factors. For `diag(19,19²)`, it returns lengths `[1,2]`, total length `3`, and rank zero modulo nineteen. The rank loss alone would reveal two affected directions, while missing the longer second direction. This is the precise information recovered from the earlier integral-torsion work.

For rectangular generating sets, `lattice_membership(A,b)` compares the original presentation with the one obtained by appending `b`. Membership holds precisely when the augmented lattice preserves both rational rank and the top determinantal divisor. The inclusion of lattices is automatic, and equal indices in their common saturation force equality. This covers dependent generating columns and proper rational subspaces; it is not merely coordinate inversion for square bases.

For a full-rank square basis, `inverse_lattice_conditions` computes `A⁻¹` rationally, then clears each row's denominators without discarding their common prime powers. Each resulting condition is an exact congruence on the candidate vector. `basis_pullback` returns integral source coordinates when all congruences hold, or explicit row/modulus/residue failures. Thus a norm-preserving map of index greater than one does not silently become an order isomorphism.

## Integration with the current order and orbit machinery

The reproduction script reads all 23 existing entries from `receipts/order_transports.json`. For each map, it compares the torsion order of its coordinate presentation with the previously recorded additive index and emits every inverse congruence. Tests also pull back each basis column and recover the expected standard coordinate vector. The existing universal symbolic order-map tests continue to check multiplication, norm, direction and determinant separately.

`orbit_lattice.order_image_allowed` turns these inverse congruences into additional divisibility tests in the existing unit-orbit filter. It enlarges the requested modulus to a common multiple of the original modulus, leading coefficient, and every relevant inverse denominator. Full matrix periods are recomputed at the enlarged modulus; signed exponents retain their established period-reduction interpretation. The output labels the absence of a global exponent bound. Exact integral image membership is stronger than a norm test; filtering modulo a finite modulus remains a necessary condition for an infinite orbit, not a completeness theorem for it.

The integration fixture `diag(3,1,1)` rejects seed `(1,0,0)` and accepts `(3,0,0)` under the identity unit action. This fixture isolates the lattice condition. The other receipt entries use the actual existing order maps, not generated replacements for their arithmetic.

## Supplied polynomial decomposition

`perfectpower.decomposition.compose` uses exact rational Horner composition. `supplied_decomposition` checks both identities `f=φ∘F` and `g=φ∘G`. A nonconstant affine outer polynomial is injective, so its equality reduces to equality of the inner polynomials' values. For a higher-degree or constant outer polynomial, the checker returns `FORWARD_ONLY` and preserves a distinct-fibre obligation. The counterexample `φ(t)=t²`, `F(x)=x`, `G(y)=−y` prevents a false cancellation rule. This is the usable supplied-certificate front end of the older Bilu–Tichy proposal, not the classification theorem or its converse.

## Reproduction, validation and remaining mathematical work

Run `PYTHONPATH=python python python/covering_lattice_receipt.py` to regenerate the receipt. Installed console commands are `perfectpower covering-replay` and, for example, `perfectpower lattice --matrix '[[19,0],[0,361]]' --vector '[19,19]' --prime 19`. The latter exposes torsion depth and the failed inverse-image condition. Both console commands produce JSON without an external CAS.

The full package suite passed 390 tests, with four skips, in 41.134 seconds. After adding the final prime-depth reporting and CLI interfaces, 39 focused tests passed across covering/lattice, information planning, orbit filtering and existing order maps. Tests include false square certificates, false covering points, singular Hensel seeds, rank-deficient presentations, hard minor budgets, independent augmented-minor membership comparisons on random bases, and invariance under unimodular row/column operations with 120-digit coefficients. Python compilation and whitespace checks passed. No Lean files changed and no Lean build was run.

The next formalization targets are the quartic covariant identity, local Hilbert arithmetic, certified local lifting, and the integral presentation interfaces. A general global obstruction engine still needs proved Selmer membership, covering correspondences, complete local coverage and a formally justified pairing interpretation. A complete Smith transformation algorithm would improve scale and enable constructive rectangular inverse witnesses. Filtered-Pell asymptotics and the general polynomial-decomposition classification remain separate research tasks. The current implementation supplies concrete arithmetic for these directions without reporting them as solved.
