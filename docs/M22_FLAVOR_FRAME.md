# Recovered M22 geometry and the flavor-frame question

## What was recovered

The repository preserves selected original files from WILSON_FORMATION_FORGE v0.26.0, including its M22/A5 Wilson algebra, Schur-selector theorems, transport-category results, and a 1,023-word exact integer ledger. The provenance manifest is galois_merge/receipts/vendor_sources.json. This is a verified subset of the old work, not recovery of every later Atlas or EQ-LAB release. The saved ledger has SHA-256 1351e514fcb5f23832f65665e0a12d2e172f8131c34875de0e03cddc5aec3093. The large original orbital tensor is absent from the subset; the ledger is nevertheless sufficient to reconstruct its two-generator algebra faithfully.

The carrier is V=C[M22/A5], of dimension 7,392. Its commutant H=End_M22(V) has dimension 152. The complex simple block sizes are 1,3,3,2,5,5,5,3,3,6. Their squares sum to 152. Thus there are four three-dimensional multiplicity carriers available for a frame calculation. They are multiplicity spaces of larger M22 representations, rather than four nontrivial three-dimensional representations of M22.

The recovered Q192 generators are X=A49 and Y=-A12-A48-A59+A95+A116+A125. X is self-adjoint and Y is skew-adjoint. This convention differs from the earlier Q7 signed operator; no Q192 calculation here is silently identified with Q7 or with its exceptional 154 block. Likewise, the three-dimensional minus-context factor in the separate 486-dimensional transport algebra is not identified with a Wilson multiplicity carrier or a physical family triplet.

## Exact reconstruction from the word ledger

The new verifier python/develop_m22_frame.py selects 152 independent ledger rows through word degree eight, inverts their integer coordinate matrix over the rationals, and reconstructs left and right multiplication by X and Y. It also reconstructs the orbital transpose permutation from reversed words and their skew signs. No CKM number, target phase, or golden coefficient enters this reconstruction.

Every available one-step left and right extension of all 511 words through degree eight is checked exactly against the original ledger. The transpose squares to the identity and is an actual orbital permutation. All four left/right generator commutators vanish exactly. Adjointness recovers positive integral orbital subdegrees, normalized at the identity; their sum is exactly 7,392. The recovered regular matrices are integral, not numerical fits.

The exact characteristic polynomial of X is (t-30)^9(t-3)^51(t+2)^65(t+5)^27. The exact Y factorization is recorded in receipts/m22_frame/frame_audit.json. In particular it contains the factors t^2+1452 and t^2+2732 relevant to the two real three-dimensional carriers, and a degree-six factor for the conjugate complex pair. Regular-module multiplicities and physical permutation-module multiplicities are different; only the shared root sets are being used here.

Unitary one-copy carrier extraction is a separate numerical step. A generic Hermitian left-multiplication selector commutes with right multiplication, so its eigenspaces supply right-invariant carriers. Word traces through degree five distinguish the conjugate complex blocks. Even trace data alone would merge that pair incorrectly. The extracted block sizes reproduce all ten expected simple blocks. The largest reported invariance residual is below 3.3e-11. Carrier coordinates and numerical overlap matrices are explicitly not promoted to exact algebraic coordinates.

## Why equivariance alone cannot select the frame

Write V as the direct sum of R_lambda tensor M_lambda, where R_lambda is an irreducible M22 carrier and M_lambda is its multiplicity space. M22 acts as rho_lambda(g) tensor I on this summand. Every operator I tensor A_lambda commutes with M22, for any matrix A_lambda on M_lambda. In a three-dimensional multiplicity carrier the full M3(C) algebra is therefore allowed by M22 equivariance.

For any desired unitary frame W, the two positive operators D_u and W D_d W-dagger are both permitted on such a multiplicity space. Their eigenvalues can be distinct. Their relative eigenframe is W. Consequently M22 equivariance alone accommodates every CKM frame and cannot force the golden relation or a particular CP phase. Canonical orbital geometry supplies distinguished candidate operators, but selecting specific orbital coefficients requires an additional interaction or residual symmetry. Algebra-generation and transport-isomorphism theorems do not perform that selection.

This is a scoped obstruction to using the unbroken commutant as the complete flavor principle. It is not a no-go theorem for M22 breaking, decorated incidence fields, projective carriers, or a more restrictive interaction category.

## The canonical C3/C7 frame fails

The first frame test takes the up-sector Hermitian operator to be X and the down-sector operator to be iY. Positive shifts, positive overall rescalings, and scalar functions that preserve the nondegenerate eigenprojectors do not change this frame test. Both ordinary real three-dimensional carriers have simple spectra for X and iY.

On the first real carrier the X eigenvalues are -5,3,30 and the iY eigenvalues are -sqrt(1452),0,sqrt(1452). Its squared overlap matrix, in increasing spectral order, has rows approximately (0.422078,0.155844,0.422078), (0.196970,0.606061,0.196970), and (0.380952,0.238095,0.380952). On the second real carrier X has eigenvalues -5,-2,3 and iY has eigenvalues -sqrt(2732),0,sqrt(2732). Its rows are approximately (0.00512445,0.98975110,0.00512445), (0.49897511,0.00204978,0.49897511), and (0.49590044,0.00819912,0.49590044).

The equality of the outer probability columns is structural. In a real carrier X has a real eigenbasis, while a real skew Y has conjugate eigenvectors for the opposite eigenvalues of iY. Their squared overlaps with any real X eigenvector are equal. The numerical column differences are below 6e-16. Row and column permutations retain the identical-column obstruction. Two identical probability columns cannot each concentrate near one in different rows, so neither frame has the CKM hierarchy. This statement does not require interpreting a convention-dependent eigenvector phase as the CKM phase.

The other two three-dimensional carriers are a conjugate complex pair, so the preceding real-carrier argument must not be applied to them individually. Both have X spectrum -2,-2,3. The repeated eigenvalue leaves a U(2) freedom and prevents X from selecting a unique family frame. The unique X eigendirection has overlaps approximately 0.0381554,0.5982882,0.3635564 with the iY eigenlines, in reverse order on the conjugate carrier. These overlaps are unchanged by rotations in the repeated eigenspace. Their maximum is below 0.599, so even that fixed direction cannot be a nearly unmixed CKM row under any permutation. The receipt omits a full mixing matrix for these degenerate cases because it would depend on arbitrary eigenbasis choices.

Thus all four available three-dimensional blocks fail for this canonical pair. This does not exclude pairs built from additional unsigned channels, higher words, decorated C5 incidence, or another vacuum-selected Hermitian operator.

## The twelvefold cover supplies a phase carrier

The primary ATLAS data gives M22 Schur multiplier of order twelve and lists its twelvefold cover. The recovered Formation work already tracks separate 2-primary and 3-primary cover restrictions. The full universal cover has central C12. An order-five element of M22 can be lifted to an order-five element of the cover: its fifth power lies in C12, and the fifth-power map is invertible on C12, so a central correction cancels that power. This lift commutes with the center. Their subgroup is C12 times C5, hence C60.

This is a group-theoretic inference from the cover data. It avoids the ordinary-M22 restriction that a single group element has no order sixty. It is not a claim that the old untwisted 7,392-state permutation module sees the central character; that module factors through M22 and its center acts trivially.

A character of this C60 subgroup has phase residue n=5a+12b modulo 60, with a modulo 12 and b modulo 5. All sixty residues occur. The primitive positive phases are 6,42,66,78,102,114,138,174 degrees. The residue eleven, corresponding to 66 degrees, can be written with a=7 and b=3. These are possible character labels, not dynamically selected quantum numbers.

If one retains the previously nominated readout C=1-2 cos(12 theta), the primitive residues n congruent to plus or minus one modulo five give C=(3-sqrt(5))/2=phi^-2. Its exact polynomial is C^2-3C+1. The positive angles on this branch are 6,66,114,174 degrees. Thus the cover supplies both the relevant cyclotomic arithmetic and several competing branches. It neither selects 66 degrees nor derives the equality of this singlet readout with the observable CKM coefficient. The other primitive residues give the larger golden root.

Central phases do not select a residual eigenframe. Multiplying a residual group matrix by a central scalar changes its eigenvalues but leaves all its spectral projectors unchanged. Such scalar factors therefore cancel from projector overlaps. Similarly an overall Yukawa or Yukawa-column phase cancels from YY-dagger. A primitive eigenphase of 66 degrees is not evidence for a physical CKM phase of 66 degrees. Multiple charge-compatible interfering contractions and a nonzero rephasing invariant must be demonstrated explicitly.

## The next interaction calculation

The useful continuation is a decorated order-five incidence construction coupled to the recovered signed C7 channels. First derive the allowed cover characters and local contractions from the actual Schur restrictions. A faithful central character cannot simply be attached to an ordinary A5 triplet without checking its extension and charge constraints. Build the resulting twisted or decorated carrier and identify two Hermitian operators with simple three-dimensional eigenframes. Their coefficients must follow from the permitted contractions or a solved vacuum, rather than from a fitted CKM matrix.

Then compute the relative spectral-projector overlaps and a CP-sensitive closed path invariant. Check whether any central phase survives these neutral observables. Fit only the existing two anchor magnitudes, if the construction admits two independently justified scales; evaluate the remaining CKM magnitude, effective golden coefficient, and physical phase as predictions. Enumerate every allowed orientation and character branch, including CP conjugates and the four golden-angle candidates. Finally enumerate symmetry-allowed counterterms to test whether the frame survives coefficient changes.

The recovered algebra has enough structure to make this calculation concrete. What it currently establishes is an exact operator reconstruction, a failure of the simplest canonical frame, and an order-60 cover route with an explicit branch and rephasing obstruction. A symmetry-protected quark frame has not been derived.

## Reproduction and sources

Run python python/develop_m22_frame.py from the repository root with NumPy, SciPy, SymPy and python-flint installed. The output operator matrices and transpose/subdegree data are in receipts/m22_frame/recovered_operators.json. The diagnostic, exact polynomial factors and phase enumeration are in frame_audit.json. The trusted original object-array archive is the same one used by the byte-preserved Forge verifier; do not replace it with an untrusted NumPy pickle.

Recovered source theorems include RAMANUJAN_WILSON_FAMILY.md, WEDDERBURN_35_RAMANUJAN_REDUCTION.md, RAW_FIVE_BLOCK_STAR_TRANSPORT_v11.md, CHAR0_TRANSPORT_GLUE_M5_v13.md, M22_PRIMARY_SCHUR_SIGNATURES_v11.md and L34_MATCHED_SELECTOR_V24.md under galois_merge/vendor/forge/THEOREMS. The primary external cover reference is the ATLAS M22 page, https://brauer.maths.qmul.ac.uk/Atlas/spor/M22/ . Its multiplier, cover and conjugacy-class data were checked on 5 October 2026. The CKM target and the mediator matching remain those of the existing protected-flavor chapters.
