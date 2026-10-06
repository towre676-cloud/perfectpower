# Electroweak completion, one-loop strong CP and attainable flavor spectra

## The completed calculations

The canonical Nelson–Barr assignment now has an explicitly minimized joint Higgs/flavor branch, a mass-basis one-loop threshold calculation using all 71 physical neutral real scalars, an exact higher-fermion covariant census through three scalar insertions, and a constructive hierarchy and CKM matching benchmark. The scientific receipt is `receipts/m22_interactions/valentiner_quantum.json`; every field coordinate and real metric coefficient is retained. These are calculations on a specified action, rather than a derivation of its input couplings from observed flavor.

The selected real spurion is epsilon = 10^-5. The joint branch has minimum scalar mass squared 4.67875984 x 10^-14 in the declared flavor units and maximum scaled flavor gradient 5.79 x 10^-9. The neutral-scalar threshold is approximately +1.45 x 10^-14 radians. Its CP partner has the opposite phase within 1.32 x 10^-15 radians. The finite-difference Hessian and double-precision eigenbasis set the numerical accuracy; the separate 60-digit trace check does not turn those input matrices into 60-digit data. We therefore use the conservative numerical statement |delta theta| < 2 x 10^-14 at this benchmark, without assigning significance to its last digits.

## A joint positive electroweak branch

Write the neutral Higgs component as H^0 = v + h/sqrt(2), with canonical real h, and retain the 35 complex flavor fields L,A,B,S of the canonical completion. The Higgs potential is -mu_H^2 H-dagger H + lambda_H (H-dagger H)^2, with lambda_H = 0.13. Add all four renormalizable Higgs norm portals on this field content: (H-dagger H) times Tr(L-dagger L), Tr(A-dagger A), Tr(B-dagger B), and Tr(S-dagger S). Their nonzero coefficients are respectively 10^-4, 2 x 10^-4, 3 x 10^-4 and 4 x 10^-4. The family representations and phase charges forbid further renormalizable Higgs portals with these scalars.

At a nominated v, minimize the full flavor potential including the portals. Fix the permitted Higgs mass parameter by mu_H^2 = 2 lambda_H v^2 + sum(lambda_i N_i). This is ordinary electroweak scale matching: v is an input, not a prediction. In canonical real flavor coordinates sigma, the 71-dimensional Hessian has the flavor block from the full portal-shifted potential, mixed entries sqrt(2) v d(sum lambda_i N_i)/d sigma, and h,h entry 4 lambda_H v^2. Positivity is tested on this full matrix, rather than on a fixed-Higgs flavor block.

The receipt scans epsilon = 1, 0.1, 0.01, 0.001 and 10^-5 with v = 0.03 epsilon. Every scanned branch is stationary to the declared tolerance and has all 71 physical neutral eigenvalues positive. Three gauge Goldstone directions are removed by gauge fixing; they are not additional physical scalar minima. This establishes local stability on the tested branch, not a global vacuum selection theorem.

## A chiral spurion that preserves the mixing frame

An additional approximate Z6 has charges 1 for every heavy left-handed fermion, 0 for every heavy right-handed fermion, 2 for the ordinary left and right quarks, 0 for all flavor scalars and the Higgs, and 1 for epsilon. Thus the heavy mass operator requires epsilon, the heavy-left to bare-right source requires its conjugate, and a Higgs-to-heavy-right operator requires epsilon squared. A bare ordinary Higgs Yukawa remains neutral. Take epsilon real and positive, preserving CP in the coefficient basis.

For the declared benchmark all nine heavy mass/source coefficients per sector are multiplied by epsilon. Then M and C scale together, N = M^-1 C is unchanged, and so is the canonical decoupling Yukawa. If v is also scaled by epsilon at a fixed scalar background, the entire 12-state Dirac matrix scales by epsilon. All left and right singular vectors, the full charged and neutral currents, and their CP quartets are exactly unchanged. The receipt checks this finite-scale identity numerically, including the appropriately rescaled pole metric. Portal-induced background shifts are included separately in the joint branch scan.

Small chiral breaking suppresses radiative communication to the flavor vacuum without suppressing the fixed-background weak phase. The general small-spurion strategy is established Nelson–Barr model-building practice; the present result is its explicit charge realization and full-matrix check on this shared-adjoint action. See Murai and Nakayama, *Revisiting the Minimal Nelson-Barr Model*, arXiv:2407.16202, sections 2–3. No novelty is claimed for the general strategy.

## The one-loop determinant calculation

Let U-dagger D V = diag(m_i), with all 12 Dirac masses positive, and let O diagonalize the canonical 71-scalar Hessian. Each real scalar vertex becomes G_a = U-dagger (sum_b O_ba dD/dsigma_b) V. At zero external momentum the finite chirality-changing mass threshold is

    delta D_ij = -sum_(a,k) G_a,ik m_k G_a,kj B0(0,m_k^2,m_a^2)/(16 pi^2),
    B0(0,x,y) = 1 - [x log(x/mu^2)-y log(y/mu^2)]/(x-y).

Use the continuous equal-mass limit B0 = -log(x/mu^2). The second vertex is G, not G-dagger. This chirality structure permits a CP phase. The finite matching convention follows the zero-momentum limit of the neutral-scalar self-energy in appendix A of arXiv:2407.16202. The receipt uses mu = 1 in the stated flavor units. There is no extra color multiplicity on the open fermion self-energy line.

The leading determinant shift is Im Tr(D^-1 delta D), evaluated in the mass basis as sum_i Im(delta D_ii)/m_i. At epsilon = 10^-5 the up contribution is +2.22849 x 10^-14 and the down contribution -7.81399 x 10^-15 radians. The relative mass-correction norms are below 0.036. The UV phase coefficients are numerically below 3 x 10^-17. An independently accumulated 60-digit trace agrees with the double-precision contraction at the tested absolute tolerance.

All 70 flavor vertices are checked against finite differences of the original full mass matrix. The threshold also passes independent changes of left/right fermion basis and real scalar basis, exact conjugate-CP tests on generic matrices, and integral checks of B0 including extreme mass ratios. The full CP-transformed vacuum and independently evaluated Hessian provide the quoted partner check.

The remaining renormalizable one-loop diagonal phase factors vanish algebraically. Neutral gauge vertices have a Hermitian left current and a diagonal real right current. Charged W vertices give only Hermitian wavefunction terms. A neutral Goldstone vertex is i Z_ij m_j/(sqrt(2) v), so its chirality-flip product is proportional to the real quantity -|Z_ij|^2 m_j^2. Charged Goldstone products similarly reduce to |V_ij|^2 m_j^2/v^2 using the full 12-state charged current. These reality identities are tested before truncating to three light states. Higgs/flavor scalar mixing is already included in the 71-mode computation. Scalar tadpole shifts cannot generate a first-order determinant phase because the tree phase is identically zero throughout the positive heavy branch, not merely at one stationary point.

This closes the leading one-loop mass-phase calculation for the stated canonical-bare fermion action. It does not establish two-loop or all-loop protection, and it does not include higher fermion interactions in the loop vertices. A fully quantum-selected scalar vacuum would additionally require scalar Coleman-Weinberg terms and renormalized scalar inputs.

## Quantified fermionic vacuum feedback

The colored Dirac Coleman-Weinberg term is -3 sum_i m_i^4 [log(m_i^2/mu^2)-3/2]/(16 pi^2). Here the closed loop does carry three colors. Its canonical real-field gradient is -3 sum_i m_i^3 [log(m_i^2/mu^2)-1] Re(G_a,ii)/(4 pi^2). The gradient is verified independently by finite differences.

At a fixed scalar background, scaling D and mu by epsilon scales this potential exactly by epsilon^4. The measured ratio at epsilon = 10^-5 is 9.999999999999927 x 10^-21. Match the single allowed Higgs soft mass to hold v fixed; no flavor tadpoles are subtracted. The resulting linearized flavor-coordinate displacement from the fermion loop is below 5.54 x 10^-18. The Higgs soft-mass matching shift is 9.34 x 10^-14. These numbers quantify the fermionic contribution; they do not assert that scalar-loop feedback has been removed.

## The exact higher-fermion operator census

The group projector is computed over all 1,080 elements of each independent 3.A6 factor, in the exact coefficient field already used by the representation certificates. Its three group averages factor. Symmetric scalar powers use their cycle-index characters, including chi(g^2) and chi(g^3), and phase charges are imposed modulo six. This counts commuting scalar insertions correctly. Sixteen distinct character-power signatures suffice for the exact sums.

The complete Higgs covariant counts by scalar degree 0,1,2,3 are 1,2,9,21; hence 33 independent complex covariants. The complete heavy-mass/source counts are 3,6,29,85; hence 123. These are complex intertwiner dimensions before choosing real CP-fixed coefficients. The anti-linear CP action determines the real coefficient basis; no claim is made that each displayed multidegree is individually CP fixed. The receipt retains each left/right endpoint, scalar multidegree and multiplicity.

One useful finite-group result is multiplicity eight for the H_A to H_B covariants with two S fields and one S-dagger. Ordinary continuous-SU(3) matrix and trace words span only five of those directions. A scan restricted to those words would therefore miss three permitted finite-group channels. The exact census prevents that omission without pretending that arbitrary continuous-SU(3) contractions are a complete 3.A6 basis.

An explicit degree-two heavy chord is L-dagger A between D and H_A; another is B S-dagger. Bare Yukawas admit det(L) times the identity at degree three. Such interactions are retained in the counting and are not forbidden by the new spurion. The spurion suppresses Higgs-to-heavy vertices, but its common heavy mass factor cancels from relative corrections inside the heavy block.

For an explicit coefficient domain, the code gives a uniform determinant-phase certificate for *every* permitted higher Higgs operator of scalar degree one to three and heavy-mass/source operator of scalar degree two and three. Normalize each invariant tensor to Frobenius norm one and bound each coefficient magnitude by one. Cauchy–Schwarz bounds each vacuum contraction by the product of its scalar norms. Sum these bounds with the correct cutoff and spurion powers to bound r = ||D_reduced^-1 Delta D_reduced||. For r < 1, |delta arg det D| <= -12 log(1-r). No cancellation or particular tensor basis is assumed.

At Lambda = 10^12 in the declared flavor units, the combined two-sector bound is 2.936 x 10^-11 radians. This is a sufficient finite-EFT quality condition, deliberately conservative. The large cutoff is a stated condition, not a derived UV scale or a demonstrated phenomenologically viable completion. Operators beyond three scalar insertions and derivative operators are outside this certificate.

## Constructive hierarchical spectrum matching

For a chosen positive left-handed target H and N = M^-1 C, a positive ordinary right-handed metric B satisfying B = y^2 H^-1 - N-dagger N gives YY-dagger = H after exact decoupling matching. Choose y large enough to make B positive. At the retained CP-breaking vacuum the nine real polynomial kinetic covariants span every Hermitian metric, so B has a finite polynomial completion (I+T)^2 + eta I that is positive for every flavor field value. The coefficients are real and therefore CP compatible. This proves attainability, rather than requiring a numerical fit to converge.

The benchmark uses illustrative dimensionless up Yukawas (10^-5,0.003,0.9) and down Yukawas (2 x 10^-5,0.0004,0.02), with bare coefficients 1.2 and 0.57. These hierarchical Yukawas are declared test inputs, not running quark mass measurements. For the CKM target use PDG 2026 equation 12.28 central parameters sin(theta12)=0.22517, sin(theta13)=0.003763, sin(theta23)=0.04189, delta=1.154 radians. The constructed result has J = 3.15937163 x 10^-5 and reproduces all CKM magnitudes within 4.45 x 10^-16. The supplied target matrices are checked at 90 digits; the positive polynomial metric reconstruction errors are below 10^-65.

This fitted kinetic action is distinct from the canonical-bare fermion action used for the loop threshold. Its field-dependent kinetic vertices must be included before any quantum claim is transferred to it. Positive metric determinants preserve the tree strong phase. Neither this inverse construction nor the spurion derives the golden CKM coefficient: the benchmark explicitly exposes the free real inputs used to match the hierarchy and mixing.

## Reproduction and release validation

Run `PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_valentiner_quantum.py`, then `PYTHONPATH=python python python/tests/test_valentiner_quantum.py`. The new suite contains 15 focused checks, supplemented by the 41 canonical, adjoint and kinetic checks. Fresh extraction and byte-identical scientific replay are recorded in `receipts/m22_interactions/valentiner_quantum_validation.json`. The standalone PDF and cumulative monograph contain this full chapter; the release archive contains every tracked source, receipt and document.

References: Murai and Nakayama, arXiv:2407.16202v2, appendix A; PDG, *CKM Quark-Mixing Matrix* (2026), section 12.4. Source URLs are retained in the scientific receipt.
