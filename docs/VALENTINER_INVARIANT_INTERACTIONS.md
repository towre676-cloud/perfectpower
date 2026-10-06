# Valentiner interactions, three light families, and the protection boundary

## Result and scope

The recovered cap geometry has a supported central-cover route to a genuine complex triplet. The triplet's first new symmetric invariant is a unique sextic, derived here directly from its exact generators. A minimal vectorlike mediator model has exactly three light modes per charge sector before electroweak breaking, and its canonical matching transmits the flavon frame. Its complete scalar operator space nevertheless contains independent cross-sector quartics. A target-free numerical local-vacuum experiment shows one such operator changing the observable CKM coefficient. Neither the golden coefficient nor the 66-degree physical phase is derived.

These results replace an unspecified symmetry search with a concrete representation, a fixed invariant tensor, specified field content and a counterterm audit. The sextic itself is the classical Valentiner/Wiman invariant, not a newly discovered polynomial. Publication novelty of the combined construction and obstruction requires comparison with the existing invariant-theory and flavor literature.

## The central-cover connection

The earlier cap computation established a component stabilizer A7 and a six-cap block stabilizer A6 of index seven in that A7. Both A7 conjugacy classes in M22 lift to 3.A7 in 3.M22. The GAP Character Table Library lists the index-seven maximal subgroup of 3.A7 as 3.A6, of order 1080. Thus the full preimage of the cap-block A6 is the nonsplit Valentiner cover, rather than the split product C3 x A6. This establishes the abstract central-cover chain 3.A6 < 3.A7 < 3.M22 for the recovered stabilizer geometry.

This conclusion uses the independently computed ordinary stabilizers together with published subgroup classifications. We have not constructed an explicit matrix representation of 3.M22 or lifted every recovered permutation generator. The local triplet does not extend to a three-dimensional representation of the whole cover by this argument. A global bundle, a global mass operator on 7392 caps, and decoupling of its other modes remain separate obligations.

Primary sources: https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/3.M22.html ; https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/3.A7.html ; https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/3.A6.html . The exact local SU(3) generators are those of Hagedorn, Meroni and Vitale, https://arxiv.org/abs/1307.5308 , equations (7,33).

## An exact tensor boundary

Let R be the faithful complex triplet and G=3.A6. We closed its four generators exactly in Q(sqrt(5),omega), with omega squared plus omega plus one equal to zero, obtaining all 1080 elements. For every pair p,q with total degree at most eight, we evaluated the character average dim Inv(R tensor p times Rbar tensor q) = sum_g tr(R(g))^p conjugate(tr(R(g)))^q / 1080. We independently computed the corresponding SU(3) tensor multiplicities from partitions and hook lengths.

Theorem. At total degree at most five the G-invariant tensor space equals the SU(3)-invariant tensor space, for arbitrarily labeled triplet fields. At degree six, the (3,3) space still has dimension six for both groups. The (6,0) space has dimension six for G and five for SU(3), leaving exactly one new tensor. The conjugate statement holds for (0,6); the other degree-six bidegrees add none.

Proof. SU(3) invariants form a subspace of G invariants. The exact character averages and independent hook-length counts coincide in the stated bidegrees. Equality of dimensions therefore proves equality of spaces. In degree six, the symmetric-power average gives dim Inv(Sym6 R)=1. Its tensor cannot be an SU(3) symmetric invariant, because there is no positive-degree SU(3)-invariant polynomial on one fundamental triplet. It exhausts the one-dimensional quotient. All character coefficients cancel exactly in the four-dimensional number field. The full counts are in receipts/m22_interactions/valentiner_invariants.json.

For one commuting triplet, through degree six the only nonconstant invariant bidegrees are (1,1), (2,2), (3,3), (6,0) and (0,6), each with dimension one. The first three are powers of the norm. Consequently every renormalizable single-triplet potential has an accidental continuous SU(3) orientation symmetry. A sextic is the first possible finite-group anisotropy. This is an effective interaction in four spacetime dimensions, requiring a suppression scale or a specified mediator completion.

## The unique sextic in the recovered basis

Writing the triplet as (x,y,z), normalize the sextic by its x6 coefficient. It is F6 = x6+y6+z6 + A(x4 y2+y4 z2+z4 x2) + B(x2 y4+y2 z4+z2 x4) + D x2 y2 z2, with A = [15-9 sqrt(5)+i(15 sqrt(3)+3 sqrt(15))]/8, B = [15+9 sqrt(5)+i(-15 sqrt(3)+3 sqrt(15))]/8 and D = 15-3i sqrt(15).

The coefficients arise from solving invariant linear equations, without a selected angle or golden CKM coefficient. Sparse monomial generators first reduce the degree-six space; the remaining generator leaves a single invariant. Each of the four polynomial identities F6(g phi)=F6(phi) is then checked exactly in the number field. The receipt records every monomial coefficient.

A potential contains a free complex overall coefficient multiplying F6 plus its conjugate. Uniqueness fixes internal component ratios; it does not fix the coefficient relative to other invariants. Its complex coefficients also do not establish physical CP violation. A consistent generalized CP action on all fields and its allowed couplings must still be constructed. Ordinary componentwise conjugation is not assumed to be a symmetry in this basis.

## Specified quarks, flavons and mediator interactions

Take Q_L in R, the Higgs in the trivial family representation, three right-handed up quarks and three right-handed down quarks in family singlets, and one vectorlike quark triplet F_u and one F_d in R. These vectorlike fields are Standard Model weak singlets with the respective up or down electric charge. Introduce six Standard Model singlet flavons phi_fi in R. This is a local four-dimensional effective model after selecting the cap stabilizer; it is not a derived global cap spectrum.

Add a specified shaping group C6 to the sixth power. Each right-handed singlet f_Ri has charge +1 under its own factor, its flavon has charge -1, and all other listed fields are neutral under that factor. The family and shaping symmetries permit, per sector, M_f Fbar_fL F_fR, h_f Qbar_L H_f F_fR, and sum_i lambda_fi Fbar_fL phi_fi f_Ri, plus Hermitian conjugates. Here H_u is the conjugate Higgs doublet and H_d the ordinary one. Each family contraction is unique, by dim Hom_G(R,R)=1. The mediator mass is therefore flavor-universal. Cross-column flavon couplings are forbidden by the specified shaping charges. A bare Qbar_L H_f f_Ri coupling has no family singlet. A mediator-triplet bilinear with one triplet flavon is forbidden by the nontrivial central charge. These exhaust renormalizable mass and Yukawa structures for this listed field content.

The symmetry allows separate M_f, h_f and three lambda_fi in each sector. It does not correlate the up and down parameters. The shaping group is an explicit model assumption, not something derived from M22. Its gauging, anomalies, a scalar messenger completion and quantum thresholds are not claimed.

## Three light modes and canonical projectors

At H=0 define C_f with columns lambda_fi times the flavon expectation values. The heavy row block is [C_f, M_f I], with three left-handed rows and six right-handed columns. For nonzero M_f it has rank exactly three, regardless of C_f. Its right kernel therefore has dimension three; the three Q_L components are the corresponding left chiral light modes. The three heavy singular values are sqrt(|M_f| squared plus s_i(C_f) squared). There are exactly three light families per charge sector in this specified local model, without interpreting a rank-three fiber as a global family count.

Set A_f=C_f/M_f, K_f=I+A_f dagger A_f. The normalized light right frame is [I; -A_f] K_f to the power -1/2, and the matched Yukawa matrix is Y_f=-h_f A_f K_f to the power -1/2. These are exact tree identities at H=0, with no small-flavon expansion. They imply H_f=Y_f Y_f dagger = |h_f| squared S_f (|M_f| squared I+S_f) inverse, where S_f=C_f C_f dagger.

The positive spectral function is strictly increasing. Thus the left spectral projectors of H_f and S_f agree, including the mass ordering for a nondegenerate spectrum. Quark mixing is computed as |V_ij| squared = Tr(P_i^u P_j^d), and J = Im Tr(P_1^u P_1^d P_2^u P_2^d). Arbitrary flavon frames remain arbitrary physical quark frames; canonical normalization neither creates nor protects the golden relation. At finite Higgs expectation value, heavy-light mixing supplies higher-dimensional EFT corrections and potential charged-current nonunitarity. Those corrections are not included in this matching statement.

## The complete scalar space through degree six

For the six specified flavons and C6 shaping factors, a degree smaller than six has equal numbers of each flavon and its conjugate. Consequently the scalar operators coincide with balanced Gram contractions: six quadratic norms; 36 quartics consisting of 21 norm products and 15 absolute overlap squares. With one Higgs, add its quadratic norm, its quartic norm and six Higgs-norm/flavon-norm products, for 50 real renormalizable scalar couplings in total.

At degree six the general Hermitian flavon space has 198 real parameters: 56 cubic norm products, 90 norm-times-overlap squares, the real and imaginary parts of 20 Gram triangles, and the real and imaginary parts of six individual F6(phi_fi). Balanced epsilon contractions are Gram determinants and add no independent operators. Gram rank relations first occur at degree eight. The shaping charges forbid mixed polarizations of the new sextic at degree six: an unbalanced field must occur six times by itself. Under a specified CP action the count can decrease, but no CP classification has been assumed here. Every absolute overlap square remains CP-even under a common unitary anti-linear CP action on the triplets.

In particular, epsilon |phi_u1 dagger phi_d1| squared is an independent allowed quartic. Neither the group nor the shaping charges constrain its coefficient to the chosen sextic coefficient. This is a concrete obstruction to claiming protected alignment merely from uniqueness of F6. It is the interaction-level counterpart of the earlier allowed linear angular deformation, although no equality between those two coordinate descriptions is assumed.

## A target-free local-vacuum deformation experiment

We minimized the phase of each sextic analytically, fixed each flavon norm to one, and considered the reduced potential sum_i -|F6(phi_i)| + epsilon |phi_u1 dagger phi_d1| squared. This is the fixed-norm reduction of polynomial sextic terms plus their conjugates, with independent phases minimized. Radial stability requires separate radial terms; no global minimum or cosmological vacuum selection is certified.

Six independently generated sextic stationary directions were selected from the numerical group orbit, and their column strengths set to 0.07, 0.31 and 0.9 in each sector. None is a measured CKM anchor or the golden target. Analytic gradients are checked against independent central finite differences, and each numerical branch must have gradient norm below 1e-7. The complete matrices, CP invariant and effective golden coefficient are recorded in receipts/m22_interactions/valentiner_alignment_response.json. For epsilon=0, C_eff is 0.4830422217 and J is 0.01663167860. At epsilon=0.01 they become 0.4831824152 and 0.01663578380. The intermediate positive and negative 0.001 cases also give distinct values. The epsilon=0 and epsilon=0.01 branches have different C_eff; this change survives the exact canonical mediator matching theorem. The mixing is not phenomenologically realistic, which is appropriate for an allowed-deformation counterexample rather than a fitted proposal.

The found single-flavon extrema form a numerical 60-line orbit, and sixteen independent searches reach modulus approximately 1.0886621079. These are numerical observations, not an exact orbit classification or a proof of the global modulus bound. Optimizer success flags and final gradients are retained, including precision-loss flags when a sufficiently small verified gradient remains.

## What the next derivation must add

The sextic supplies a real representation-derived coefficient pattern, and the mediator calculation supplies a concrete light-family and normalization result. Their combination does not protect the observable golden relation. The next justified search must introduce interactions that correlate the sectors while controlling all 15 independent quartic overlaps, permit useful mixed sextic contractions without opening arbitrary singlet-copy matrices, and define a consistent generalized CP action. A proposed mechanism must then demonstrate its chosen spectrum and vacuum, test all remaining free parameters, and match the observable projectors. No choice of the desired CKM angle enters the invariant derivation above.

## Reproduction

Run python python/develop_valentiner_invariants.py, then python python/develop_valentiner_alignment.py from the repository. The first command produces an exact invariant receipt and 24 canonical-matching scenarios. The second produces a numerical local-branch receipt with an independent gradient check. The exact group code and dependencies are shared with python/develop_valentiner_frames.py and python/m22_frame_requirements.txt. The monograph renderer includes this complete chapter. No new Lean theorem or experimental measurement is asserted.
