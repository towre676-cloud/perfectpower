# Audit of the inputs to the golden-CKM search

Audited baseline: `c7cdb4cf9814a7be006c17965678084b85211612`. Date: 6 October 2026. This audit covers the flavor search and its B5, M22, Valentiner, messenger and CP inputs. It is not an audit of every unrelated arithmetic application in the repository. Historical data and numerical examples remain pinned; newer measurements are compared separately.

The mathematical constructions are useful, but their combination is not yet a derived particle theory. The decisive unsupported step remains the identification of a selected scalar or representation invariant with a relation between the canonically normalized up and down quark eigenframes. The audit also identifies a concrete incompatibility in directly combining the ordinary quark example with the proposed supersymmetric messenger sector, and a missing scalar-potential calculation that can already be tested exactly.

## Input ledger

Here “computed” means checked for the specified input object, not established as a law of nature. “Chosen” identifies an additional model assumption. “Missing” means no calculation in this research establishes the required physical identification.

| Input or inference | Audit status | Consequence for the search |
| --- | --- | --- |
| Exact three-generation unitary CKM parametrization | Correct within the three-light-generation decoupling limit | Vectorlike finite-Higgs effects require separate charged-current matching. |
| Relation `s13=C*s12*s23` | Chosen phenomenological hypothesis | CKM unitarity alone does not imply it. |
| Golden value `C=(3-sqrt(5))/2` | Training-nominated candidate | Neither B5 nor M22 has derived its identification with the observable coefficient. |
| `delta=66 degrees` | Training-nominated phase | A scalar angle, a root-of-unity eigenphase and the standard CKM phase are different quantities until matched. |
| Original `Vus=.22431`, `Vcb=.0411` | Pinned historical measured central values | They have uncertainties; the 2026 combined Vcb central value is .0407. |
| Gamma and `Vtd/Vts` training anchors | Explicit measured inputs with assumptions | Gamma helps select 66 degrees; the mixing-ratio extraction assumes SM dynamics. |
| Independent Gaussian/split-normal likelihood | Chosen summary-data approximation | Missing cross-input covariance prevents treating it as a precision global fit. |
| Basis `alpha, alpha_s, pi, phi, mp/me`, rational alphabet, support penalty and phase grid | Chosen search domain and prior | A MAP formula in this domain is not a symmetry theorem or a prior-independent discovery. |
| Excluded observable keys in the training API | Correct software safeguard | Previously published observables were known; the exercise is retrospective, not blinded. |
| B5 action on five exponent axes | Correct combinatorics | Swapping physically labelled constants is not a physical symmetry. B5 supplies no primitive 60th-root eigenphase. |
| Golden extremum of positive-definite symmetric integral 2-by-2 determinant-one matrices | Correct conditional spectral statement | Integrality, determinant, matrix choice, canonical kinetic metric and quark coupling are physical assumptions. |
| Six-harmonic potential selecting plus/minus 66 degrees | Constructed and exactly checked | Its coefficients were found with the desired root known; their physical origin is absent. An additive constant in the implementation does not affect minima. |
| Eight rational stationarity constraints; four on the six-term support | Correct over the rational coefficient field | They are not eight independent equations for arbitrary real couplings at one angle. |
| CP symmetry of the scalar potential | Correct | It permits CP-even deformations and pairs the two signs; it does not select the observed sign. |
| Generic 1% coupling sensitivity | Numerical study of the declared perturbation ensemble | Its interval is not an experimental confidence interval or an invariant measure of naturalness. |
| 20% attraction basin and low-temperature occupation | Conditional dynamics with specified measure | Angular kinetic metric, initial measure, thermal history and CP-sign selection are not derived. |
| Recovered Wilson ledger and M22 algebra | Verified selected archival subset and exact reconstruction | The recovery is not the whole lost archive; provenance checks do not validate all historical physical claims. |
| Three-dimensional M22 multiplicity spaces | Correct | M22 acts trivially on their multiplicity factors, allowing arbitrary frame matrices. They are not faithful family triplets. |
| Canonical decorated A5 transport and orientation cover | Computed geometry and projector splitting | Rank-three parallel projectors do not imply three light quark modes; the canonical connection has zero kernel. |
| Central C60 subgroup in the twelvefold cover | Supported group-theoretic construction | Central phases cancel from neutral spectral-projector overlaps; they do not select a CKM frame. |
| `3.A6` inside `3.A7` inside `3.M22` | Abstract subgroup/cover route supported by character-table data | The specific global twisted quark bundle and its explicit lifted matrices have not been built. |
| Exact Valentiner triplet and low-degree invariant census | Computed for the specified generators and polynomial/tensor spaces | The unique sextic is a classical invariant. Its uniqueness fixes tensor components, not all independent Wilson coefficients. |
| Failure of complete residual frames and the tested two-involution route | Correct scoped obstructions | They exclude those unbroken constructions, not every model with controlled symmetry breaking. |
| Product family symmetry `Gu x Gd` | Added model assumption | It is not a consequence of the recovered single M22 action. |
| Six separately charged source flavons, singlet right-handed quarks and chosen mediators | Added field/charge assumptions | The field content already contains three column labels. Their presence is not a derivation of three families. |
| Global versus gauged family and shaping symmetries | UV realization unspecified | A gauge completion and its anomaly constraints have not been established. Formal selection rules alone do not supply that completion. |
| Product symmetry forbids bare cross-sector overlap quartics | Correct for those representations | It still permits nine dressed degree-six overlaps and other source/link couplings. |
| 58 CP-even renormalizable scalar parameters | Specified nonsupersymmetric scalar-sector count | It is not the parameter count of a supersymmetric completion including messenger scalars, Kähler terms and soft breaking. |
| Positive link alignment at scaled group matrices | Correct for the chosen polynomial potential | Unitarity, determinant stabilization and the degree-twelve completion were supplied; uniqueness and physical vacuum selection were not proved. |
| Renormalizable holomorphic sextic messenger chain | Representation counts and bilinear support the leading contraction | Other allowed self-cubics remain independent. The 17 invariant coefficients belong to the four-species messenger sector, not the whole theory. |
| Supersymmetric messenger superpotential versus quark link example | Separate constructions; direct amalgamation invalid | The quark reverse coupling uses the conjugate link. It cannot be promoted unchanged to a holomorphic superpotential with only the same chiral link field. |
| Source frames and column hierarchies | Chosen backgrounds and couplings | The CP-real basis has real orthogonal freedom. No joint scalar minimum selects its orientation or realistic mass hierarchy. |
| Canonical tree matching at zero Higgs background | Correct within the specified invertible heavy blocks | Thresholds, loop-induced kinetic corrections and finite-Higgs current normalization remain separate. |
| Scale at which the golden relation is imposed | Unspecified physical matching input | CKM parameters run above the weak scale. The standalone SM running diagnostic is not a threshold-matched evolution of the messenger construction. |
| Anti-linear involution on the chosen elementary fields | Exactly computed with a representation-content restriction | `3.A6` has no class-inverting automorphism valid for arbitrary irreducible content. All added fields and contractions need compatible CP action. |
| Nonzero J and commutator invariant in the quark example | Correct conditional demonstration of weak CP violation | The group element was selected for large absolute J, not by a scalar vacuum; it gives unrealistic mixing and no prediction of the physical phase. Strong CP is unaddressed. |
| Modified 44,352-mode operator with three zero modes | Correct conditional mass-squared spectrum | Component choice, connection flattening and rank-three penalty are engineered breaking inputs. A chiral mass operator and the complex local model are not unified. |
| Observable polynomial relations | Exact consequences of the nominated CKM chart with branch conditions | Elimination creates a test of the hypothesis; it does not supply an independently justified interaction. |
| Reproducible artifacts and passing tests | Evidence of implementation consistency | Neither byte reproduction nor test count establishes experimental truth, radiative protection or novelty. |

## The rational-coupling qualification

Set `x=2*cos(theta)`. The minimal polynomial of `2*cos(66 degrees)` has degree eight. A rational derivative vanishing at that root must be divisible by this polynomial, so it also vanishes at all its conjugates. The independent Chebyshev calculation reproduces rank eight for the constant plus twelve harmonics, and rank four on harmonics 2, 3, 5, 8, 9 and 12.

For unrestricted real coefficients, stationarity at one fixed interior angle is one nonzero linear equation. For example, `cos(2 theta)+b*cos(3 theta)` is stationary at 66 degrees when `b=-2*sin(132 degrees)/(3*sin(198 degrees))`. That example does not claim a minimum or a protecting symmetry. It isolates the coefficient-field assumption. Representation coefficients may be algebraic and independent physical couplings may be real, so the appropriate coefficient field must be derived before promoting the rational rank to a model-building requirement. The exact CP-even deformation remains a valid obstruction in the scalar model where it is allowed.

## The superpotential is not the chosen scalar alignment energy

In global supersymmetry with canonical kinetic terms, the scalar F-term potential is `sum |dW/dLambda_ij|^2`; it is not `-Re W`. The audit reconstructs the fully symmetric sextic tensor from its exact polynomial coefficients. Its norm squared is 16 and its one-index reduced tensor is exactly `(16/3) I`. Hence, for `I6(Lambda)=<T,T composed with Lambda>`,

`I6(I)=16`, `dI6/dLambda_ij at I=32 delta_ij`, and `sum Lambda_ij*dI6/dLambda_ij at I=96`.

With only `W=kappa*I6`, the radial line `Lambda=rI`, for real positive r, has `VF=3072*|kappa|^2*r^10`. A nonzero scaled group matrix is therefore not radially stationary in this isolated model, while the origin has zero energy. Generating the sextic in W does not by itself generate the previously chosen nonzero alignment vacuum.

This is a limitation of the isolated term, not a no-go theorem for the allowed messenger EFT. The independently allowed determinant term can balance the gradient: for `W=a*det(Lambda)+kappa*I6(Lambda)`, a nonzero `rI` is F-flat when `a+32*kappa*r^3=0`. Its group transforms are then F-flat as well. The origin remains F-flat, and the complete allowed terms, kinetic metric, source couplings and soft breaking must determine stability and occupation. This audit does not assert that those nonzero branches solve the CKM problem.

The ordinary down-quark example contains both a link and its Hermitian conjugate in its heavy mass block. That is allowed in the nonsupersymmetric theory. Holomorphy prevents copying both entries unchanged into a renormalizable superpotential with just one chiral link. A separate conjugate chiral link, a modified coupling chain, or a nonholomorphic effective interaction would require new fields or matching and a fresh operator audit. A hybrid construction may be possible; none was supplied by the prior calculations.

## Updated data and the interpretation of the target

The 2026 PDG CKM review retains `|Vus|=.22431 +/-.00085`, and quotes combined `|Vcb|=.0407 +/-.0013`, `|Vub|=.00389 +/-.00016`, and `sin(2 beta)=.710 +/-.011`. Inclusive and exclusive determinations remain distinct, and the review's correlated global fit must not be treated as independent data added to these inputs.

Keeping the golden coefficient and 66-degree phase fixed while substituting only the updated central Vcb gives `|Vub|=.00348716940` and `sin(2 beta)=.690881841`. These remain conditional chart predictions. The rounded combined measurement centers instead give `C_eff=.426088669`. First-order independent-error propagation gives about `.0222480`, putting the golden coefficient approximately 1.98 nominal standard deviations below that central combination. This diagnostic is not a joint likelihood or an exclusion significance. It establishes that the measured inputs do not currently fix the coefficient to the golden value. No new fit or posterior selection was run.

The existing retrospective search already reports that its leading formula has only .1603% posterior probability in the support-three family, its B5/smooth training evidence ratio is about .800, and removing phi barely changes its broad forecast. Those findings must remain inputs to our judgment. The narrow forecast conditional on choosing the golden formula does not include uncertainty over choosing that formula. The 66-degree phase was favored using measured gamma; its appearance in later constructed potentials is not independent evidence for it.

## What the audit changes

The search should retain the recovered exact algebra, genuine triplet invariant tensors, canonical quark matching, explicit CP consistency calculation and the scoped obstructions. It should stop treating the golden target, product symmetry, CP-real source frames, unitary link, and three-mode modified spectrum as deductions from one common starting symmetry. They are different added inputs, and the physical maps between them remain missing.

A defensible next result would specify one field content and one Lagrangian, derive its scalar and kinetic terms, solve its joint source/link vacuum, and extract the two canonically normalized quark eigenframes without inserting the target. Allowed variations then test whether any observable relation is forced. A failed relation would still be an informative result. Recovering more elaborate arithmetic that only re-encodes the nominated angle would not repair the audited gaps.

## Verification and sources

Run `PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/audit_flavor_inputs.py`. The deterministic receipt records the independent rational ranks, exact reduced tensor and sextic gradient, updated central-input calculation, and SHA-256 hashes of eleven audited implementation/input files. The historical training receipt is unchanged. The audit reran 65 flavor unit tests and eight Valentiner invariant/CP/global checks successfully. These checks do not independently reconstruct every archival M22 object or certify a complete UV theory.

Primary references: PDG, *CKM Quark-Mixing Matrix*, revised March 2026, https://pdg.lbl.gov/2026/reviews/rpp2026-rev-ckm-matrix.pdf , equations 12.8, 12.11, 12.12 and 12.20; S. P. Martin, *A Supersymmetry Primer*, https://arxiv.org/abs/hep-ph/9709356 , sections 3.2 and 4.7; M.-C. Chen et al., *CP Violation from Finite Groups*, https://arxiv.org/abs/1402.0507 , especially section 4's restricted-representation qualification. Existing character-table and generator references remain in the M22 and Valentiner chapters. The sextic-gradient and coefficient-field checks are independent calculations in this audit, rather than claims taken from these references.
