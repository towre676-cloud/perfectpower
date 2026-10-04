# Witness resolvents and graph repairs

This development recovers two constructions from *The Level and the Deformation*: the formal matrix-output resolvents in Appendix DLP and the comparison-defect architecture in RG·14. It turns them into exact Python certificates for the repository's recurrence models and cyclotomic graph measures. The formulas are classical linear algebra. The contribution here is a reusable, checked implementation, its adaptation to the stored workloads, and explicit handling of transients, cancellations and rank loss.

## Source and adaptation

The original `level_deformation_monograph_v4_54_1(5).html` is 4,053,819 bytes, dated July 6, 2026. This development reads windows 14840–14944 and 9060–9101, rather than claiming a new complete reading of that book. The relevant source excerpts and adaptation boundaries are retained in [source_excerpt.json](../receipts/witness_repairs/source_excerpt.json).

DLP writes a witness moment as a matrix coefficient of a power and collects all moments in a rational resolvent. RG·14 propagates an operator comparison through an inverse and a determinant ratio. We retain these exact finite algebraic ideas. The implementation does not inherit physical identifications, modular-category admission, analytic contour results or conductor claims from the surrounding discussion.

The broader linear-representation setting is documented in Stefan Kiefer's [Notes on Equivalence and Minimization of Weighted Automata](https://arxiv.org/abs/2009.01217). The graph repair uses the determinant lemma and Woodbury identity, also described in the author's [WoodburyMatrix documentation](https://stat.ethz.ch/CRAN/web/packages/WoodburyMatrix/vignettes/WoodburyMatrix.html). No novelty of those identities is claimed.

## A finite identity certifies the infinite formal series

For a rational square matrix A, seed s and readout matrix H, define

\[
F(z)=\sum_{n\ge0}H A^n s\,z^n=H(I-zA)^{-1}s.
\]

This identity lives in formal power series over Q; it requires no analytic convergence region. The constant matrix of I−zA is the identity, so its formal inverse exists even when A is singular.

Discovery builds the independent Krylov vectors s, As, …, A^(r−1)s until

\[
A^r s=\sum_{j=0}^{r-1}c_j A^j s.
\]

Set D(z)=1−c_(r−1)z−…−c_0 z^r, and write its coefficients as D_j. Construct the vector polynomial

\[
V_i=\sum_{j=0}^{i}D_j A^{i-j}s\quad(0\le i<r),
\qquad V(z)=\sum_i V_i z^i.
\]

The certificate checker verifies every coefficient of

\[
(I-zA)V(z)=D(z)s.
\]

It checks independence of the V_i as well. These have the same span as the Krylov vectors by a triangular change with diagonal one. The terminal coefficient identity closes that span under A. Zero seeds use V=0 and r=0 explicitly.

For each readout h, the compiler reduces hV/D by an exact polynomial gcd, normalizes the denominator to constant one and records P/Q. The checker verifies coprimality and the cross identity (hV)Q=PD. It does not rediscover a Krylov basis, fit terms, diagonalize A or choose approximate eigenvalues. Invisible modes can cancel separately for different outputs.

## The denominator alone misses finite transients

A nilpotent three-state chain can have output 0,0,1,0,0,…. Its generating function is z², with denominator one. Declaring recurrence order zero from that denominator would erase the sequence.

For a nonzero reduced P/Q with Q(0)=1, the homogeneous chronological recurrence starts with order

\[
r_{\mathrm{output}}=\max(\deg Q,\deg P+1).
\]

Leading zero coefficients encode the finite transient. Identically zero outputs have order zero in the certificate. The existing recurrence executor supplies logarithmic-index evaluation; the new value interface checks rational bit growth during reduced polynomial powering and accepts nonnegative 64-bit indices.

DLP's star matrix provides a useful source example. With p leaf states, one center, and the first leaf as both seed and readout, the exact result is

\[
F_p(z)=\frac{1-(p-1)z^2}{1-pz^2},\qquad
a_0=1,\quad a_{2k+1}=0,\quad a_{2k}=p^{k-1}\ (k\ge1).
\]

For p>1, the denominator has degree two but the complete homogeneous model has order three: the initial term includes a finite zero-eigenvalue contribution. The implementation retains it. It also corrects the source's coefficient wording: with constant-one normalization, the coefficient of z² in the denominator is **−p**, so p is its negative. The checked examples include p=2,3,5,7,11,13 as explicit matrix models; no modular-category classification is inferred from these calculations.

## Equality and arithmetic subsequences

Two checked outputs P₁/Q₁ and P₂/Q₂ agree for every nonnegative index exactly when P₁Q₂−P₂Q₁=0. If this polynomial is nonzero, its first nonzero coefficient gives the earliest differing index and its exact difference, because both denominator constants are one. This catches discrepancies that a short matching prefix can miss.

For offsets b≥0 and steps a≥0, the subsequence h A^(b+an)s is compiled using operator A^a and seed A^b s. Binary exact powering handles singular matrices and step zero. The returned certificate concerns the transformed matrix model; callers retain the sampling parameters. This supplies exact parity subsequences and more general arithmetic progressions without reconstructing a law from samples.

These conclusions concern supplied matrix or recurrence definitions. A reconstructed model agreeing with an OEIS prefix still requires a separate proof that the original sequence follows that definition.

## A small defect repairs an entire graph measure

The existing graph measure uses cyclotomic incidence B, nonnegative rational weights W and L=B*WB. A full-rank base has inverse P=L⁻¹, determinant Z and transfer kernel T=WB P B*. For changed edges J, let Δ contain their signed weight changes. Put

\[
U=B_J^*\Delta,\quad V=B_J,\quad S=I+VPU.
\]

Then L′=L+UV and the determinant lemma gives

\[
Z'=Z\det S.
\]

If S is invertible, Woodbury gives

\[
P'=P-PU S^{-1}VP,
\qquad T'=W'B P' B^*.
\]

Only S, whose dimension is the number of changed weights, needs a new inverse. We never invert Δ, so decreases and edge deletions are supported directly. Updated weights must remain nonnegative. An unchanged graph uses an empty defect and ratio one.

If det S=0, the updated graph has lost full rank. The implementation checks this against the graph's independent support-rank certificate, sets the updated determinant to zero and returns `RANK_DEFICIENT`, with no inverse or probability kernel. It does not manufacture a probability distribution on that support. A rank-deficient base is rejected; there is no hidden pseudoinverse or regularization path.

`verify_reweight` checks the full-rank base through the established measure verifier, checks the displayed S and its supplied inverse, and checks the updated inverse, determinant and kernel against the repair formulas. It does not discover a new inverse or expand a new large determinant. Replay still checks the base and constructs the dense output kernel; the small inverse does not imply that all runtime or storage is proportional to |J|³. No runtime speedup is claimed without a corresponding measurement.

The updated receipt uses the existing measure format, so subsequent inclusion/exclusion events and conditioning continue through the existing API. Basis enumeration remains zero.

## Usage

```sh
python -m perfectpower witness-resolvent \
  --matrix '[[0,1],[1,1]]' --seed '[1,0]' --readouts '[[1,0]]' \
  --index 100 --verify

python -m perfectpower witness-resolvent \
  --matrix '[[0,1],[1,1]]' --seed '[0,1]' --readouts '[[1,0]]' \
  --offset 1 --step 2 --index 25 --verify

python -m perfectpower connection-reweight \
  --vertices 2 --edges '[[0,1,0],[0,1,1]]' --power 3 \
  --weights '[1,1]' --new-weights '[2,1]' --verify

PYTHONPATH=python python python/develop_witness_repairs.py
```

The Python interfaces live in [witness_resolvent.py](../python/perfectpower/witness_resolvent.py) and [connection_updates.py](../python/perfectpower/connection_updates.py). Shapes, coefficient growth, Krylov work, subsequence powering and graph update work have explicit budgets. Exceeding a budget raises an error rather than returning a partially certified result.

## Workload evidence and verification boundary

The rebuild runner retains deterministic certificates and independent comparisons under [receipts/witness_repairs](../receipts/witness_repairs). It compares each stored model to the existing recurrence executor, checks parity subsequences, and compares repaired graph inverses, determinants and kernels to fresh exact constructions. Focused tests exercise direct matrix iteration, repeated poles, cancellations, nilpotent transients, zero seeds, source star matrices, earliest differences, tampering, JSON round trips, rank loss and signed weight changes.

All 135 stored recurrence models receive resolvent and even/odd subsequence certificates. They form 131 canonical rational-function classes. There are 810 independent value comparisons and 1,080 independent subsequence comparisons. Their separate homogeneous orders remain 368 in total; this workload already had minimal individual models, so the new compiler does not claim a further reduction. The earlier shared-machine reduction concerns a different construction and remains separate.

Of 196 stored graph rows, 184 have full-rank base measures and 12 are excluded from this full-rank update route. The runner checks 736 updates, including 184 unchanged baselines and 552 actual changes. It detects 219 resulting rank losses, and compares 1,551 future inclusion/exclusion events on the remaining measures. The retained 10-vertex, 40-edge example changes two weights, replacing a new 10-dimensional inverse discovery with a 2-dimensional defect inverse. Its determinant and full inverse match a fresh exact reconstruction. Neither path enumerates the 847,660,528 possible maximal-minor subsets.

The full Python suite runs 679 tests, with 675 passing and four skipped. A fresh repository archive runs the 21 focused tests with `python -S` from outside the repository and reproduces all five deterministic certificate files byte for byte. [Validation metadata](../receipts/witness_repairs/validation.json) records source hashes, the archive tree and the scope of those checks. The concurrent root/event Lean publication is preserved by integration; it does not change the tested Python implementation or its corpus inputs.

All new certificates are exact Python replay results. This development adds no Lean theorem and claims zero new Lean compilations. The earlier Lean modules keep their recorded status; these new algorithms and their execution are a separate formalization task. The integer solver's supported equation families are unchanged by this addition.
